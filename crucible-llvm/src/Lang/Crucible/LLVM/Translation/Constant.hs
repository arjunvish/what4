-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Constant
-- Description      : LLVM constant expression evaluation and GEPs
-- Copyright        : (c) Galois, Inc 2014-2015
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module provides translation-time evaluation of constant
-- expressions.  It also provides an intermediate representation
-- for GEP (getelementpointer) instructions that makes more explicit
-- the places where vectorization may occur, as well as resolving type
-- sizes and field offsets.
-----------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Translation.Constant
  ( -- * Representation of LLVM constant values
    LLVMConst(..)
  , boolConst
  , intConst

    -- * Translations from LLVM syntax to constant values
  , transConstant
  , transConstant'
  , transConstantExpr

    -- * Intermediate representation for GEP
  , GEP(..)
  , GEPResult(..)
  , translateGEP

    -- * Utility functions
  , showInstr
  ) where

import           Control.Monad
import           Control.Monad.Except
import           Data.Bits
import           Data.Traversable
import           Data.Fixed (mod')
import qualified Data.Vector as V
import           Numeric.Natural
import           GHC.TypeLits

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import           Lang.Crucible.LLVM.Bytes
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Translation.Types

-- | Pretty print an LLVM instruction
showInstr :: L.Instr -> String
showInstr i = show (L.ppLLVM38 (L.ppInstr i))

-- | Intermediate representation of a GEP.
--   A @GEP n expr@ is a representation of a GEP with
--   @n@ parallel vector lanes with expressions represented
--   by @expr@ values.
data GEP (n :: Nat) (expr :: *) where
  -- | Start a GEP with a single base pointer
  GEP_scalar_base  :: expr -> GEP 1 expr

  -- | Start a GEP with a vector of @n@ base pointers
  GEP_vector_base  :: NatRepr n -> expr -> GEP n expr

  -- | Copy a scalar base vector pointwise into a
  --   vector of length @n@.
  GEP_scatter      :: NatRepr n -> GEP 1 expr -> GEP n expr

  -- | Add the offset corresponding to the given field
  --   pointwise to each pointer
  GEP_field        :: FieldInfo -> GEP n expr -> GEP n expr

  -- | Add an offset corresponding to the given array index
  --   (multiplied by the given type size) pointwise to the pointers
  --   in each lane.
  GEP_index_each   :: MemType -> GEP n expr -> expr -> GEP n expr

  -- | Given a vector of offsets (whose length must match
  --   the number of lanes), multiply each one by the
  --   type size, and add the offsets to the corresponding
  --   pointers.
  GEP_index_vector :: MemType -> GEP n expr -> expr -> GEP n expr

instance Functor (GEP n) where
  fmap = fmapDefault
instance Foldable (GEP n) where
  foldMap = foldMapDefault

instance Traversable (GEP n) where
  traverse f gep = case gep of
    GEP_scalar_base x            -> GEP_scalar_base <$> f x
    GEP_vector_base n x          -> GEP_vector_base n <$> f x
    GEP_scatter n gep'           -> GEP_scatter n <$> traverse f gep'
    GEP_field fi gep'            -> GEP_field fi <$> traverse f gep'
    GEP_index_each mt gep' idx   -> GEP_index_each mt <$> traverse f gep' <*> f idx
    GEP_index_vector mt gep' idx -> GEP_index_vector mt <$> traverse f gep' <*> f idx

-- | The result of a GEP instruction translation.  It records the number
--   of parallel vector lanes in the resulting instruction, the resulting
--   memory type of the instruction, and the sequence of sub-operations
--   required to compute the GEP instruction.
data GEPResult expr where
  GEPResult :: (1 <= n) => NatRepr n -> MemType -> GEP n expr -> GEPResult expr

instance Functor GEPResult where
  fmap = fmapDefault
instance Foldable GEPResult where
  foldMap = foldMapDefault

instance Traversable GEPResult where
  traverse f (GEPResult n mt gep) = GEPResult n mt <$> traverse f gep


-- | Given the data for an LLVM getelementpointer instruction,
--   preprocess the instruction into a @GEPResult@, checking
--   types, computing vectorization lanes, etc.
translateGEP :: forall wptr m.
  (?lc :: TyCtx.LLVMContext, MonadError String m, HasPtrWidth wptr) =>
  Bool              {- ^ inbounds flag -} ->
  L.Typed L.Value   {- ^ base pointer expression -} ->
  [L.Typed L.Value] {- ^ index arguments -} ->
  m (GEPResult (L.Typed L.Value))

translateGEP _ _ [] =
  throwError "getelementpointer must have at least one index"

translateGEP inbounds base elts =
  do mt <- liftMemType (L.typedType base)
     -- Input value to a GEP must have a pointer type (or be a vector of pointer
     -- types), and the pointed-to type must be representable as a memory type.
     -- The resulting memory type drives the interpretation of the GEP arguments.
     case mt of
       -- Vector base case, with as many lanes as there are input pointers
       VecType n (PtrType baseSymType)
         | Just baseMemType <- TyCtx.asMemType baseSymType
         , Just (Some lanes) <- someNat (toInteger n)
         , Just LeqProof <- isPosNat lanes
         ->  let mt' = ArrayType 0 baseMemType in
             go lanes mt' (GEP_vector_base lanes base) elts

       -- Scalar base case with exactly 1 lane
       PtrType baseSymType
         | Just baseMemType <- TyCtx.asMemType baseSymType
         ->  let mt' = ArrayType 0 baseMemType in
             go (knownNat @1) mt' (GEP_scalar_base base) elts

       _ -> badGEP
 where
 badGEP :: m a
 badGEP = throwError $ unlines [ "Invalid GEP", showInstr (L.GEP inbounds base elts) ]

 -- This auxilary function builds up the intermediate GEP mini-instructions that compute
 -- the overall GEP, as well as the resulting memory type of the final pointers and the
 -- number of vector lanes eventually computed by the GEP.
 go ::
   (1 <= lanes) =>
   NatRepr lanes               {- Number of lanes of the GEP so far -} ->
   MemType                     {- Memory type of the incomming pointer(s) -} ->
   GEP lanes (L.Typed L.Value) {- parital GEP computation -} ->
   [L.Typed L.Value]           {- remaining arguments to process -} ->
   m (GEPResult (L.Typed L.Value))

 -- Final step, all arguments are used up, return the GEPResult
 go lanes mt gep [] = return (GEPResult lanes mt gep)

 -- Resolve one offset value and recurse
 go lanes mt gep (off:xs) =
   do offt <- liftMemType (L.typedType off)
      -- The meaning of the offset depends on the static type of the intermediate result
      case mt of
        -- If it is an array type, the offset should be considered an array index, or
        -- vector of array indices.
        ArrayType _ mt' ->
          case offt of
            -- Single array index, apply pointwise to all intermediate pointers
            IntType _
              -> go lanes mt' (GEP_index_each mt' gep off) xs

            -- Vector of indices, matching the current number of lanes, apply
            -- each offset to the corresponding base pointer
            VecType n (IntType _)
              | natValue lanes == toInteger n
              -> go lanes mt' (GEP_index_vector mt' gep off) xs

            -- Vector of indices, with a single incomming base pointer.  Scatter
            -- the base pointer across the correct number of lanes, and then
            -- apply the vector of offsets componentwise.
            VecType n (IntType _)
              | Just (Some n') <- someNat (toInteger n)
              , Just LeqProof <- isPosNat n'
              , Just Refl <- testEquality lanes (knownNat @1)
              -> go n' mt' (GEP_index_vector mt' (GEP_scatter n' gep) off) xs

            -- Otherwise, some sort of mismatch occured.
            _ -> badGEP

        -- If it is a structure type, the index must be a constant value that indicates
        -- which field (counting from 0) is to be indexed.
        StructType si ->
          do off' <- transConstant' offt (L.typedValue off)
             case off' of
               -- Special case for the zero value
               ZeroConst (IntType _) -> goidx 0

               -- Single index; compute the corresponding field.
               IntConst _ idx -> goidx idx

               -- Special case.  A vector of indices is allowed, but it must be of the correct
               -- number of lanes, and each (constant) index must be the same value.
               VectorConst (IntType _) (i@(IntConst _ idx) : is) | all (same i) is -> goidx idx
                 where
                 same :: LLVMConst -> LLVMConst -> Bool
                 same (IntConst wx x) (IntConst wy y)
                   | Just Refl <- testEquality wx wy = x == y
                 same _ _ = False

               -- Otherwise, invalid GEP instruction
               _ -> badGEP

                  -- using the information from the struct type, figure out which
                  -- field is indicated
            where goidx idx | 0 <= idx && idx < toInteger (V.length flds) =
                       go lanes (fiType fi) (GEP_field fi gep) xs
                     where flds = siFields si
                           fi   = flds V.! (fromInteger idx)

                  goidx _ = badGEP

        _ -> badGEP


-- | Translation-time LLVM constant values.
data LLVMConst where
  -- | A constant value consisting of all zero bits.
  ZeroConst     :: !MemType -> LLVMConst
  -- | A constant integer value, with bit-width @w@.  The integer should
  --   be understood as a value modulo @2^w@.
  IntConst      :: (1 <= w) => !(NatRepr w) -> !Integer -> LLVMConst
  -- | A constant floating point value.
  FloatConst    :: !Float -> LLVMConst
  -- | A constant double value.
  DoubleConst   :: !Double -> LLVMConst
  -- | A constant array value.
  ArrayConst    :: !MemType -> [LLVMConst] -> LLVMConst
  -- | A constant vector value.
  VectorConst   :: !MemType -> [LLVMConst] -> LLVMConst
  -- | A constant structure value.
  StructConst   :: !StructInfo -> [LLVMConst] -> LLVMConst
  -- | A pointer value, consisting of a concrete offset from a global symbol.
  SymbolConst   :: !L.Symbol -> !Integer -> LLVMConst
  -- | A special marker for pointer constants that have been cast as an integer type.
  PtrToIntConst :: !LLVMConst -> LLVMConst

-- | Create an LLVM constant value from a boolean.
boolConst :: Bool -> LLVMConst
boolConst False = IntConst (knownNat @1) 0
boolConst True = IntConst (knownNat @1) 1

-- | Create an LLVM constant of a given width.  The resulting integer
--   constant value will be the unsigned integer value @n mod 2^w@.
intConst ::
  MonadError String m =>
  Natural {- ^ width of the integer constant, @w@ -} ->
  Integer {- ^ value of the integer constant, @n@ -} ->
  m LLVMConst
intConst n 0
  = return (ZeroConst (IntType n))
intConst n x
  | Just (Some w) <- someNat (fromIntegral n)
  , Just LeqProof <- isPosNat w
  = return (IntConst w (toUnsigned w x))
intConst n _
  = throwError ("Invalid integer width: " ++ show n)

-- | Compute the constant value of an expression.  Fail if the
--   given value does not represent a constant.
transConstant ::
  (?lc :: TyCtx.LLVMContext, MonadError String m, HasPtrWidth wptr) =>
  L.Typed L.Value ->
  m LLVMConst
transConstant (L.Typed tp v) =
  do mt <- liftMemType tp
     transConstant' mt v

-- | Compute the constant value of an expression.  Fail if the
--   given value does not represent a constant.
transConstant' ::
  (?lc :: TyCtx.LLVMContext, MonadError String m, HasPtrWidth wptr) =>
  MemType ->
  L.Value ->
  m LLVMConst
transConstant' _tp (L.ValUndef) =
  throwError "Undefined constant value"
transConstant' (IntType n) (L.ValInteger x) =
  intConst n x
transConstant' (IntType 1) (L.ValBool b) =
  return . IntConst (knownNat @1) $ if b then 1 else 0
transConstant' FloatType (L.ValFloat f) =
  return (FloatConst f)
transConstant' DoubleType (L.ValDouble d) =
  return (DoubleConst d)
transConstant' (PtrType _) (L.ValSymbol s) =
  return (SymbolConst s 0)
transConstant' tp L.ValZeroInit =
  return (ZeroConst tp)
transConstant' (PtrType stp) L.ValNull =
  return (ZeroConst (PtrType stp))
transConstant' (VecType n tp) (L.ValVector _tp xs)
  | n == length xs
  = VectorConst tp <$> traverse (transConstant' tp) xs
transConstant' (ArrayType n tp) (L.ValArray _tp xs)
  | n == length xs
  = ArrayConst tp <$> traverse (transConstant' tp) xs
transConstant' (StructType si) (L.ValStruct xs)
  | not (siIsPacked si)
  , V.length (siFields si) == length xs
  = StructConst si <$> traverse transConstant xs
transConstant' (StructType si) (L.ValPackedStruct xs)
  | siIsPacked si
  , V.length (siFields si) == length xs
  = StructConst si <$> traverse transConstant xs

transConstant' tp (L.ValConstExpr cexpr) = transConstantExpr tp cexpr

transConstant' tp val =
  throwError $ unlines ["Cannot compute constant value for expression of type: " ++ show tp
                       , show val
                       ]


-- | Evaluate a GEP instruction to a constant value.
evalConstGEP :: forall m wptr.
  (?lc :: TyCtx.LLVMContext, MonadError String m, HasPtrWidth wptr) =>
  GEPResult LLVMConst ->
  m LLVMConst
evalConstGEP (GEPResult lanes finalMemType gep0) =
   do xs <- go gep0
      unless (toInteger (length xs) == natValue lanes)
             (throwError "Unexpected vector length in result of constant GEP")
      case xs of
        [x] -> return x
        _   -> return (VectorConst (PtrType (MemType finalMemType)) xs)

  where
  dl = TyCtx.llvmDataLayout ?lc

  asOffset :: MemType -> LLVMConst -> m Integer
  asOffset _ (ZeroConst (IntType _)) = return 0
  asOffset mt (IntConst _ x) =
    do let x' = x * (bytesToInteger (memTypeSize dl mt))
       unless (x' <= maxUnsigned ?ptrWidth)
              (throwError "Computed offset overflow in constant GEP")
       return x'
  asOffset _ _ = throwError "Expected offset value in constant GEP"

  addOffset :: Integer -> LLVMConst -> m LLVMConst
  addOffset x (SymbolConst sym off) = return (SymbolConst sym (off+x))
  addOffset _ _ = throwError "Expected symbol constant in constant GEP"

  -- Given a processed GEP instruction, compute the sequence of output
  -- pointer values that result from the instruction.  If the GEP is
  -- scalar-valued, then the result will be a list of one element.
  go :: GEP n LLVMConst -> m [LLVMConst]

  -- Scalar base, return a list containing just the base value.
  go (GEP_scalar_base base)
    = return [base]

  -- Vector base, deconstruct the input value and return the
  -- corresponding values.
  go (GEP_vector_base n x)
    = asVectorOf (fromInteger (natValue n)) return x

  -- Scatter a scalar input across n lanes
  go (GEP_scatter n gep)
    = do ps <- go gep
         case ps of
           [p] -> return (replicate (fromInteger (natValue n)) p)
           _   -> throwError "vector length mismatch in GEP scatter"

  -- Add the offset corresponding to the given field across
  -- all the lanes of the GEP
  go (GEP_field fi gep)
    = do ps <- go gep
         let i = bytesToInteger (fiOffset fi)
         traverse (addOffset i) ps

  -- Compute the offset corresponding to the given array index
  -- and add that offest across all the lanes of the GEP
  go (GEP_index_each mt gep x)
    = do ps <- go gep
         i  <- asOffset mt x
         traverse (addOffset i) ps

  -- For each index in the input vector, compute and offset according
  -- to the given memory type and add the corresponding offset across
  -- each lane of the GEP componentwise.
  go (GEP_index_vector mt gep x)
    = do ps <- go gep
         is <- asVectorOf (length ps) (asOffset mt) x
         zipWithM addOffset is ps

-- | Evaluate a floating point comparison.
evalFcmp ::
  RealFloat a =>
  L.FCmpOp ->
  a -> a -> LLVMConst
evalFcmp op x y = boolConst $ case op of
  L.Ffalse -> False
  L.Ftrue  -> True
  L.Foeq   -> ordered && x == y
  L.Fone   -> ordered && x /= y
  L.Fogt   -> ordered && x >  y
  L.Foge   -> ordered && x >= y
  L.Folt   -> ordered && x <  y
  L.Fole   -> ordered && x <= y
  L.Ford   -> ordered
  L.Fueq   -> unordered || x == y
  L.Fune   -> unordered || x /= y
  L.Fugt   -> unordered || x >  y
  L.Fuge   -> unordered || x >= y
  L.Fult   -> unordered || x <  y
  L.Fule   -> unordered || x <= y
  L.Funo   -> unordered
 where
 unordered = isNaN x || isNaN y
 ordered   = not unordered

-- | Evaluate an integer comparison.
evalIcmp ::
  (1 <= w) =>
  L.ICmpOp ->
  NatRepr w ->
  Integer -> Integer -> LLVMConst
evalIcmp op w x y = boolConst $ case op of
  L.Ieq  -> ux == uy
  L.Ine  -> ux /= uy
  L.Iugt -> ux >  uy
  L.Iuge -> ux >= uy
  L.Iult -> ux <  uy
  L.Iule -> ux <= uy
  L.Isgt -> sx >  sy
  L.Isge -> sx >= sy
  L.Islt -> sx <  sy
  L.Isle -> sx <= sy

 where
 ux = toUnsigned w x
 uy = toUnsigned w y
 sx = toSigned w x
 sy = toSigned w y

-- | Evaluate an arithmetic operation.
evalArith ::
  (MonadError String m, HasPtrWidth wptr) =>
  L.ArithOp ->
  MemType ->
  Arith -> Arith -> m LLVMConst
evalArith op (IntType m) (ArithI x) (ArithI y)
  | Just (Some w) <- someNat (toInteger m)
  , Just LeqProof <- isPosNat w
  = evalIarith op w x y
evalArith op FloatType (ArithF x) (ArithF y) = FloatConst <$> evalFarith op x y
evalArith op DoubleType (ArithD x) (ArithD y) = DoubleConst <$> evalFarith op x y
evalArith _ _ _ _ = throwError "arithmetic arugment mistmatch"

-- | Evaluate a floating-point operation.
evalFarith ::
  (RealFrac a, MonadError String m) =>
  L.ArithOp ->
  a -> a -> m a
evalFarith op x y =
  case op of
    L.FAdd -> return (x + y)
    L.FSub -> return (x - y)
    L.FMul -> return (x * y)
    L.FDiv -> return (x / y)
    L.FRem -> return (mod' x y)
    _ -> throwError "Encountered integer arithmetic operation applied to floating point arguments"

-- | Evaluate an integer or pointer arithmetic operation.
evalIarith ::
  (1 <= w, MonadError String m, HasPtrWidth wptr) =>
  L.ArithOp ->
  NatRepr w ->
  ArithInt -> ArithInt -> m LLVMConst
evalIarith op w (ArithInt x) (ArithInt y)
  = IntConst w <$> evalIarith' op w x y
evalIarith op w (ArithPtr sym x) (ArithInt y)
  | Just Refl <- testEquality w ?ptrWidth
  , L.Add _ _ <- op
  = return $ PtrToIntConst $ SymbolConst sym (x+y)
  | otherwise
  = throwError "Illegal operation applied to pointer argument"
evalIarith op w (ArithInt x) (ArithPtr sym y)
  | Just Refl <- testEquality w ?ptrWidth
  , L.Add _ _ <- op
  = return $ PtrToIntConst $ SymbolConst sym (x+y)
  | otherwise
  = throwError "Illegal operation applied to pointer argument"
evalIarith op w (ArithPtr symx x) (ArithPtr symy y)
  | Just Refl <- testEquality w ?ptrWidth
  , symx == symy
  , L.Sub _ _ <- op
  = return $ IntConst ?ptrWidth (toUnsigned ?ptrWidth (x - y))
  | otherwise
  = throwError "Illegal operation applied to pointer argument"

-- | Evaluate an integer (non-pointer) arithmetic operation.
evalIarith' ::
  (1 <= w, MonadError String m) =>
  L.ArithOp ->
  NatRepr w ->
  Integer -> Integer -> m Integer
evalIarith' op w x y = do
  let nuwTest nuw z =
        when (nuw && toUnsigned w z > maxUnsigned w)
             (throwError "Unsigned overflow in constant arithmetic operation")
  let nswTest nsw z =
        when (nsw && (toSigned w z < minSigned w || toSigned w z > maxSigned w))
             (throwError "Signed overflow in constant arithmetic operation")
  case op of
    L.Add nuw nsw ->
      do let z = x + y
         nuwTest nuw z
         nswTest nsw z
         return z

    L.Sub nuw nsw ->
      do let z = x - y
         nuwTest nuw z
         nswTest nsw z
         return z

    L.Mul nuw nsw ->
      do let z = x * y
         nuwTest nuw z
         nswTest nsw z
         return z

    L.UDiv exact ->
      do when (y == 0)
              (throwError "Division by 0 in constant arithmetic operation")
         let (z,r) = x `quotRem` y
         when (exact && r /= 0)
              (throwError "Exact division failed in constant arithmetic operation")
         return z

    L.SDiv exact ->
      do when (y == 0)
              (throwError "Division by 0 in constant arithmetic operation")
         let sx = toSigned w x
         let sy = toSigned w y
         when (sx == minSigned w && sy == -1)
              (throwError "Signed division overflow in constant arithmetic operation")
         let (z,r) = sx `quotRem` sy
         when (exact && r /= 0 )
              (throwError "Exact division failed in constant arithmetic operation")
         return z
    L.URem ->
      do when (y == 0)
              (throwError "Division by 0 in constant arithmetic operation")
         let r = x `rem` y
         return r

    L.SRem ->
      do when (y == 0)
              (throwError "Division by 0 in constant arithmetic operation")
         let sx = toSigned w x
         let sy = toSigned w y
         when (sx == minSigned w && sy == -1)
              (throwError "Signed division overflow in constant arithmetic operation")
         let r = sx `rem` sy
         return r

    _ -> throwError "Floating point operation applied to integer arguments"

-- | Evaluate a bitwise operation on integer values.
evalBitwise ::
  (1 <= w, MonadError String m) =>
  L.BitOp ->
  NatRepr w ->
  Integer -> Integer -> m LLVMConst
evalBitwise op w x y = IntConst w <$>
  do let ux = toUnsigned w x
     let uy = toUnsigned w y
     let sx = toSigned w x
     case op of
       L.And -> return (ux .&. uy)
       L.Or  -> return (ux .|. uy)
       L.Xor -> return (ux `xor` uy)
       L.Shl nuw nsw ->
         do let z = ux `shiftL` fromInteger uy
            when (nuw && toUnsigned w z > maxUnsigned w)
                 (throwError "Unsigned overflow in left shift")
            when (nsw && toSigned w z > maxUnsigned w)
                 (throwError "Signed overflow in left shift")
            return z
       L.Lshr exact ->
         do let z = ux `shiftR` fromInteger uy
            when (exact && ux /= z `shiftL` fromInteger uy)
                 (throwError "Exact left shift failed")
            return z
       L.Ashr exact ->
         do let z = sx `shiftR` fromInteger uy
            when (exact && ux /= z `shiftL` fromInteger uy)
                 (throwError "Exact left shift failed")
            return (toUnsigned w z)

-- | Evaluate a conversion operation on constants.
evalConv ::
  (?lc :: TyCtx.LLVMContext, MonadError String m, HasPtrWidth wptr) =>
  L.ConstExpr ->
  L.ConvOp ->
  MemType ->
  LLVMConst ->
  m LLVMConst
evalConv expr op mt x = case op of
    L.FpToUi
      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , FloatConst f <- x
      -> return $ IntConst w (truncate f)

      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , DoubleConst d <- x
      -> return $ IntConst w (truncate d)

    L.FpToSi
      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , FloatConst f <- x
      -> return $ IntConst w (truncate f)

      | IntType n <- mt
      , Just (Some w) <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w
      , DoubleConst d <- x
      -> return $ IntConst w (truncate d)

    L.UiToFp
      | FloatType <- mt
      , IntConst w i <- x
      -> return $ FloatConst (fromInteger (toUnsigned w i))

      | DoubleType <- mt
      , IntConst w i <- x
      -> return $ DoubleConst (fromInteger (toUnsigned w i))

    L.SiToFp
      | FloatType <- mt
      , IntConst w i <- x
      -> return $ FloatConst (fromInteger (toSigned w i))

      | DoubleType <- mt
      , IntConst w i <- x
      -> return $ DoubleConst (fromInteger (toSigned w i))

    L.Trunc
      | IntType n <- mt
      , IntConst w i <- x
      , Just (Some w') <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w'
      , Just LeqProof <- testLeq w' w
      -> return $ IntConst w' (toUnsigned w' i)

    L.ZExt
      | IntType n <- mt
      , IntConst w i <- x
      , Just (Some w') <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w'
      , Just LeqProof <- testLeq w w'
      -> return $ IntConst w' (toUnsigned w' i)

    L.SExt
      | IntType n <- mt
      , IntConst w i <- x
      , Just (Some w') <- someNat (toInteger n)
      , Just LeqProof <- isPosNat w'
      , Just LeqProof <- testLeq w w'
      -> return $ IntConst w' (toSigned w' i)

    L.FpTrunc
      | DoubleType <- mt
      , DoubleConst d <- x
      -> return $ DoubleConst d

      | FloatType <- mt
      , DoubleConst d <- x
      -> return $ FloatConst (realToFrac d)

      | FloatType <- mt
      , FloatConst f <- x
      -> return $ FloatConst f

    L.FpExt
      | DoubleType <- mt
      , DoubleConst d <- x
      -> return $ DoubleConst d

      | DoubleType <- mt
      , FloatConst f <- x
      -> return $ DoubleConst (realToFrac f)

      | FloatType <- mt
      , FloatConst f <- x
      -> return $ FloatConst f

    L.IntToPtr
      | PtrToIntConst p <- x
      -> return p

      | otherwise
      -> badExp "cannot convert arbitrary constant values to pointers"

    L.PtrToInt
      | SymbolConst _ _  <- x
      -> return $ PtrToIntConst x
      | otherwise
      -> badExp "invalid pointer value"

    _ -> badExp "unexpected conversion operation"

 where badExp msg = throwError $ unlines [msg, show expr]


-- | Evaluate a bitcast
evalBitCast ::
  MonadError String m =>
  L.ConstExpr {- ^ original expression to evaluate -} ->
  MemType     {- ^ input expressio type -} ->
  LLVMConst   {- ^ input expression -} ->
  MemType     {- ^ desired output type -} ->
  m LLVMConst
evalBitCast expr xty x toty =
  case (xty, toty) of
    _ | xty == toty
      -> return x

    (PtrType _, PtrType _)
      -> return x

    (IntType w, VecType n (IntType m))
      | w == (fromIntegral n) * m
      , Just (Some w') <- someNat (toInteger m)
      , Just LeqProof <- isPosNat w'
      -> do xint <- asInt w x
            -- NB little endian assumption!
            let pieces = [ maxUnsigned w' .&. (xint `shiftR` (i * fromIntegral m))
                         | i <- [0 .. n-1]
                         ]
            return $ VectorConst (IntType m) (map (IntConst w') pieces)

    (VecType n (IntType m), IntType w)
      | w == fromIntegral n * m
      , Just (Some w') <- someNat (toInteger w)
      , Just LeqProof <- isPosNat w'
      -> do xs <- asVectorOf n (asInt m) x
            -- NB little endian assumption!
            let pieces = [ v `shiftL` (i * fromIntegral m)
                         | i <- [0 .. n-1]
                         | v <- xs
                         ]
            return $ IntConst w' (foldr (.|.) 0 pieces)

    _ -> badExp "illegal bitcast"

 where badExp msg = throwError $ unlines [msg, show expr]



asVectorOf ::
  MonadError String m =>
  Int ->
  (LLVMConst -> m a) ->
  (LLVMConst -> m [a])
asVectorOf n f (ZeroConst (VecType m mt))
  | n == m
  = do x <- f (ZeroConst mt)
       return (replicate n x)
asVectorOf n f (VectorConst _ xs)
  | n == length xs
  = traverse f xs
asVectorOf n _ _
  = throwError ("Expected vector constant value of length: " ++ show n)

-- | Type representing integer-like things.  These are either actual
--   integer constants, or constant offsets from global symbols.
data ArithInt where
  ArithInt :: Integer -> ArithInt
  ArithPtr :: L.Symbol -> Integer -> ArithInt

-- | A constant value to which arithmetic operation can be applied.
--   These are integers, pointers, floats and doubles.
data Arith where
  ArithI :: ArithInt -> Arith
  ArithF :: Float -> Arith
  ArithD :: Double -> Arith

asArithInt ::
  (MonadError String m, HasPtrWidth wptr) =>
  Natural   {- ^ expected integer width -} ->
  LLVMConst {- ^ constant value -} ->
  m ArithInt
asArithInt n (ZeroConst (IntType m))
  | n == m
  = return (ArithInt 0)
asArithInt n (IntConst w x)
  | toInteger n == natValue w
  = return (ArithInt x)
asArithInt n (PtrToIntConst (SymbolConst sym off))
  | toInteger n == natValue ?ptrWidth
  = return (ArithPtr sym off)
asArithInt _ _
  = throwError "Expected integer value"

asArith ::
  (MonadError String m, HasPtrWidth wptr) =>
  MemType   {- ^ expected type -} ->
  LLVMConst {- ^ constant value -} ->
  m Arith
asArith (IntType n) x = ArithI <$> asArithInt n x
asArith FloatType x   = ArithF <$> asFloat x
asArith DoubleType x  = ArithD <$> asDouble x
asArith _ _ = throwError "Expected arithmetic type"

asInt ::
  MonadError String m =>
  Natural   {- ^ expected integer width -} ->
  LLVMConst {- ^ constant value -} ->
  m Integer
asInt n (ZeroConst (IntType m))
  | n == m
  = return 0
asInt n (IntConst w x)
  | toInteger n == natValue w
  = return x
asInt n _
  = throwError ("Expected integer constant of size " ++ show n)

asFloat ::
  MonadError String m =>
  LLVMConst {- ^ constant value -} ->
  m Float
asFloat (ZeroConst FloatType) = return 0
asFloat (FloatConst x) = return x
asFloat _ = throwError "Expected floating point constant"

asDouble ::
  MonadError String m =>
  LLVMConst {- ^ constant value -} ->
  m Double
asDouble (ZeroConst DoubleType) = return 0
asDouble (DoubleConst x) = return x
asDouble _ = throwError "Expected double constant"


-- | Compute the value of a constant expression.  Fails if
--   the expression does not actually represent a constant value.
transConstantExpr ::
  (?lc :: TyCtx.LLVMContext, MonadError String m, HasPtrWidth wptr) =>
  MemType ->
  L.ConstExpr ->
  m LLVMConst
transConstantExpr _mt expr = case expr of
  L.ConstGEP _ _ _ [] -> badExp "Constant GEP must have at least two arguments"
  L.ConstGEP _ (Just _) _ _ -> badExp "NYI: Constant GEP with `inrange`"
  L.ConstGEP inbounds Nothing _ (base:exps) ->
    do gep <- translateGEP inbounds base exps
       gep' <- traverse transConstant gep
       evalConstGEP gep'

  L.ConstSelect b x y ->
    do b' <- transConstant b
       x' <- transConstant x
       y' <- transConstant y
       case b' of
         IntConst _w v
           | v /= 0    -> return x'
           | otherwise -> return y'
         _ -> badExp "Expected boolean value in constant select"

  L.ConstBlockAddr _ _ ->
    badExp "constant block addresses not supported"

  L.ConstFCmp op a b ->
    do mt <- liftMemType (L.typedType a)
       case mt of
         VecType n FloatType ->
           do a' <- asVectorOf n asFloat =<< transConstant a
              b' <- asVectorOf n asFloat =<< transConstant b
              return $ VectorConst (IntType 1) $ zipWith (evalFcmp op) a' b'
         VecType n DoubleType ->
           do a' <- asVectorOf n asDouble =<< transConstant a
              b' <- asVectorOf n asDouble =<< transConstant b
              return $ VectorConst (IntType 1) $ zipWith (evalFcmp op) a' b'
         FloatType ->
           do a' <- asFloat =<< transConstant a
              b' <- asFloat =<< transConstant b
              return $ evalFcmp op a' b'
         DoubleType ->
           do a' <- asDouble =<< transConstant a
              b' <- asDouble =<< transConstant b
              return $ evalFcmp op a' b'
         _ -> badExp "Expected floating point arguments"

  L.ConstICmp op a b ->
    do mt <- liftMemType (L.typedType a)
       case mt of
         VecType n (IntType m)
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asVectorOf n (asInt m) =<< transConstant a
                 b' <- asVectorOf n (asInt m) =<< transConstant b
                 return $ VectorConst (IntType 1) $ zipWith (evalIcmp op w) a' b'
         IntType m
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asInt m =<< transConstant a
                 b' <- asInt m =<< transConstant b
                 return $ evalIcmp op w a' b'
         _ -> badExp "Expected integer arguments"

  L.ConstArith op (L.Typed tp a) b ->
    do mt <- liftMemType tp
       case mt of
          VecType n tp' ->
            do a' <- asVectorOf n (asArith tp') =<< transConstant' mt a
               b' <- asVectorOf n (asArith tp') =<< transConstant' mt b
               VectorConst tp' <$> zipWithM (evalArith op tp') a' b'
          tp' ->
            do a' <- asArith tp' =<< transConstant' mt a
               b' <- asArith tp' =<< transConstant' mt b
               evalArith op tp' a' b'

  L.ConstBit op (L.Typed tp a) b ->
    do mt <- liftMemType tp
       case mt of
         VecType n (IntType m)
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asVectorOf n (asInt m) =<< transConstant' mt a
                 b' <- asVectorOf n (asInt m) =<< transConstant' mt b
                 VectorConst (IntType m) <$> zipWithM (evalBitwise op w) a' b'
         IntType m
           | Just (Some w) <- someNat (toInteger m)
           , Just LeqProof <- isPosNat w
           -> do a' <- asInt m =<< transConstant' mt a
                 b' <- asInt m =<< transConstant' mt b
                 evalBitwise op w a' b'
         _ -> badExp "Expected integer arguments"

  L.ConstConv L.BitCast (L.Typed tp x) outty ->
   do toty <- liftMemType outty
      xty  <- liftMemType tp
      x' <- transConstant' xty x
      evalBitCast expr xty x' toty

  L.ConstConv op x outty ->
    do mt <- liftMemType outty
       x' <- transConstant x
       case mt of
         VecType n mt' ->
           do xs <- asVectorOf n return x'
              VectorConst mt' <$> traverse (evalConv expr op mt') xs

         _ -> evalConv expr op mt x'

 where badExp msg = throwError $ unlines [msg, show expr]