------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Partial
-- Description      : Operations on partial values in the LLVM memory model
-- Copyright        : (c) Galois, Inc 2015-2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.MemModel.Partial
  ( PartLLVMVal
  , totalLLVMVal
  , bvConcat
  , consArray
  , appendArray
  , mkArray
  , mkStruct
  , bvToDouble
  , bvToFloat
  , bvToX86_FP80
  , selectHighBv
  , selectLowBv
  , arrayElt
  , fieldVal
  , muxLLVMVal
  ) where

import           Prelude hiding (pred)

import           GHC.Generics (Generic)
import           Control.Lens ((^.), view)
import           Control.Monad.IO.Class (liftIO, MonadIO)
import           Control.Monad.State.Strict (State, get, put, runState)
import           Data.List.NonEmpty (NonEmpty((:|)), nonEmpty)
import           Data.Vector (Vector)
import           Data.Text (Text)
import           Data.Word (Word64)
import           Data.Proxy (Proxy(Proxy))
import qualified Data.Vector as V

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some (Some(..))

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.CFG.Extension.Safety hiding (assertSafe)
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import           Lang.Crucible.LLVM.Bytes (Bytes)
import           Lang.Crucible.LLVM.Extension (LLVM)
import qualified Lang.Crucible.LLVM.Bytes as Bytes
import           Lang.Crucible.LLVM.MemModel.Type (StorageType(..), StorageTypeF(..), Field(..))
import qualified Lang.Crucible.LLVM.MemModel.Type as Type
import           Lang.Crucible.LLVM.MemModel.Value (LLVMVal(..))
import qualified Lang.Crucible.LLVM.MemModel.Value as Value
import           Lang.Crucible.LLVM.Extension.Safety
import qualified Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior as UB
import           Lang.Crucible.Panic (panic)

import           What4.Interface (Pred, IsExprBuilder)
import qualified What4.Interface as W4I
import qualified What4.InterpretedFloatingPoint as W4IFP
import           What4.Partial
import           What4.Partial.AssertionTree (AssertionTree(..))
import           What4.Partial.AssertionTree as W4P

------------------------------------------------------------------------
-- ** PartLLVMVal

-- | The kinds of type errors that arise while reading memory/constructing LLVM
-- values
data TypeError sym =
    TypeMismatch StorageType StorageType
  | UnexpectedArgumentType Text [LLVMVal sym]
  | PreviousErrors Text [TypeError sym]
  deriving (Generic)

-- | Either an 'LLVMValue' paired with a tree of predicates explaining
-- just when it is actually valid, or a type mismatch.
type PartLLVMVal arch sym =
  PartialWithErr
    (TypeError sym)
    (LLVMAssertionTree arch (RegValue' sym))
    (LLVMVal sym)

pattern PartLLVMVal :: LLVMAssertionTree arch (RegValue' sym)
                    -> LLVMVal sym
                    -> PartLLVMVal arch sym
pattern PartLLVMVal p v = NoErr (Partial p v)

typeOfBitvector :: W4I.IsExpr (W4I.SymExpr sym)
                => proxy sym -> W4I.SymBV sym w -> StorageType
typeOfBitvector _ =
  Type.bitvectorType . Bytes.toBytes . natValue . W4I.bvWidth

-- | Make an assertion that isn't about undefined behavior
-- llvmAssert :: Text -> Pred sym -> LLVMValAssertion sym
-- llvmAssert = flip LLVMValAssertion Nothing

-- | An 'LLVMVal' which is always valid.
totalLLVMVal :: (IsExprBuilder sym)
             => sym
             -> LLVMVal sym
             -> PartLLVMVal arch sym
totalLLVMVal sym = NoErr . Partial (Leaf (safe sym))

-- | Add a side-condition to a value that might have caused undefined behavior
addUndefinedBehaviorCondition_ :: proxy sym -- ^ Unused, pins down ambiguous type
                               -> UB.UndefinedBehavior (RegValue' sym)
                               -> Pred sym
                               -> LLVMAssertionTree arch (RegValue' sym)
                               -> LLVMAssertionTree arch (RegValue' sym)
addUndefinedBehaviorCondition_ _proxySym ub pred tree =
  W4P.addCondition tree (undefinedBehavior ub (RV pred))

addUndefinedBehaviorCondition :: sym -- ^ Unused, pins down ambiguous type
                              -> UB.UndefinedBehavior (RegValue' sym)
                              -> Pred sym
                              -> LLVMAssertionTree arch (RegValue' sym)
                              -> LLVMAssertionTree arch (RegValue' sym)
addUndefinedBehaviorCondition sym = addUndefinedBehaviorCondition_ (Just sym)

-- | Take a partial value and assert its safety
-- assertSafe :: (IsSymInterface sym)
--            => sym
--            -> PartLLVMVal arch sym
--            -> IO (LLVMVal sym)
-- assertSafe sym (Partial tree a) = do
--   let proxy = Proxy :: Proxy (LLVM arch)
--   pred <- treeToPredicate proxy sym tree
--   liftIO $ assert sym pred $ AssertFailureSimError $
--     show $ explainTree proxy (Just sym) tree
--   pure a

------------------------------------------------------------------------
-- ** PartLLVMVal interface
--

-- | Convert a bitvector to a float, asserting that it is not a pointer
bvToFloat :: forall arch sym.
  IsSymInterface sym =>
  sym ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)

bvToFloat sym (PartLLVMVal p (LLVMValZero (StorageType (Bitvector 4) _))) =
  PartLLVMVal p . LLVMValFloat Value.SingleSize <$>
    (W4IFP.iFloatFromBinary sym W4IFP.SingleFloatRepr =<<
       W4I.bvLit sym (knownNat @32) 0)

bvToFloat sym (PartLLVMVal p (LLVMValInt blk off))
  | Just Refl <- testEquality (W4I.bvWidth off) (knownNat @32) = do
      pz <- W4I.natEq sym blk =<< W4I.natLit sym 0
      let ub = UB.PointerCast (RV blk, RV off) Float
      PartLLVMVal (addUndefinedBehaviorCondition sym ub pz p) .
        LLVMValFloat Value.SingleSize <$>
        W4IFP.iFloatFromBinary sym W4IFP.SingleFloatRepr off

bvToFloat _ typeMismatch = pure typeMismatch


-- | Convert a bitvector to a double, asserting that it is not a pointer
bvToDouble ::
  IsSymInterface sym => sym ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)

bvToDouble sym (PartLLVMVal p (LLVMValZero (StorageType (Bitvector 8) _))) =
  PartLLVMVal p . LLVMValFloat Value.DoubleSize <$>
    (W4IFP.iFloatFromBinary sym W4IFP.DoubleFloatRepr =<<
       W4I.bvLit sym (knownNat @64) 0)

bvToDouble sym (PartLLVMVal p (LLVMValInt blk off))
  | Just Refl <- testEquality (W4I.bvWidth off) (knownNat @64) = do
      pz <- W4I.natEq sym blk =<< W4I.natLit sym 0
      let ub = UB.PointerCast (RV blk, RV off) Float
      PartLLVMVal (addUndefinedBehaviorCondition sym ub pz p) .
        LLVMValFloat Value.DoubleSize <$>
        W4IFP.iFloatFromBinary sym W4IFP.DoubleFloatRepr off


-- | Convert a bitvector to an FP80 float, asserting that it is not a pointer
bvToX86_FP80 ::
  IsSymInterface sym => sym ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)

bvToX86_FP80 sym (PartLLVMVal p (LLVMValZero (StorageType (Bitvector 10) _))) =
  PartLLVMVal p . LLVMValFloat Value.X86_FP80Size <$>
    (W4IFP.iFloatFromBinary sym W4IFP.X86_80FloatRepr =<<
       W4I.bvLit sym (knownNat @80) 0)

bvToX86_FP80 sym (PartLLVMVal p (LLVMValInt blk off))
  | Just Refl <- testEquality (W4I.bvWidth off) (knownNat @80) = do
      pz <- W4I.natEq sym blk =<< W4I.natLit sym 0
      let ub = UB.PointerCast (RV blk, RV off) X86_FP80
      PartLLVMVal (addUndefinedBehaviorCondition sym ub pz p) .
        LLVMValFloat Value.X86_FP80Size <$>
        W4IFP.iFloatFromBinary sym W4IFP.X86_80FloatRepr off

-- | Concatenate partial LLVM bitvector values. The least-significant
-- (low) bytes are given first. The allocation block number of each
-- argument is asserted to equal 0, indicating non-pointers.
bvConcat :: forall arch sym.
  IsSymInterface sym => sym ->
  PartLLVMVal arch sym ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)

bvConcat sym (PartLLVMVal p1 v1) (PartLLVMVal p2 v2) =
    case (v1, v2) of
      (LLVMValInt blk_low low, LLVMValInt blk_high high) ->
        do go blk_low low blk_high high
      (LLVMValInt blk_low low, LLVMValZero t@(StorageType (Bitvector high_bytes) _)) ->
        Value.zeroInt sym high_bytes $ \case
          Nothing -> return $ Err $ TypeMismatch (typeOfBitvector (Just sym) low) t
          Just (blk_high, high) ->
            go blk_low low blk_high high
      (LLVMValZero t@(StorageType (Bitvector low_bytes) _), LLVMValInt blk_high high) ->
         Value.zeroInt sym low_bytes $ \case
           Nothing -> return $ Err $ TypeMismatch (typeOfBitvector (Just sym) high) t
           Just (blk_low, low) ->
             go blk_low low blk_high high
      (LLVMValZero (StorageType (Bitvector low_bytes) _), LLVMValZero (StorageType (Bitvector high_bytes) _)) ->
        pure $ totalLLVMVal sym (LLVMValZero (Type.bitvectorType (low_bytes + high_bytes)))
      (a, b) -> return $ Err $ UnexpectedArgumentType "While concatenating bitvectors" [a, b]

 where
  go :: forall l h. (1 <= l, 1 <= h) =>
    W4I.SymNat sym -> W4I.SymBV sym l -> W4I.SymNat sym -> W4I.SymBV sym h -> IO (PartLLVMVal arch sym)
  go blk_low low blk_high high
    -- NB we check that the things we are concatenating are each an integral number of
    -- bytes.  This prevents us from concatenating together the partial-byte writes that
    -- result from e.g. writing an i1 or an i20 into memory.  This is consistent with LLVM
    -- documentation, which says that non-integral number of bytes loads will only succeed
    -- if the value was written orignally with the same type.
    | natValue low_w' `mod` 8 == 0
    , natValue high_w' `mod` 8 == 0 =
      do blk0   <- W4I.natLit sym 0
         -- TODO: Why won't this pattern match fail?
         Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
         predLow       <- W4I.natEq sym blk_low blk0
         predHigh      <- W4I.natEq sym blk_high blk0
         bv            <- W4I.bvConcat sym high low
         return $ flip PartLLVMVal (LLVMValInt blk0 bv) $
           let ub1 = UB.PointerCast (RV blk_low, RV low)   (Bitvector 0)
               ub2 = UB.PointerCast (RV blk_high, RV high) (Bitvector 0)
           in
             W4P.And (Leaf (undefinedBehavior ub1 (RV predLow)) :|
                        [ Leaf (undefinedBehavior ub2 (RV predHigh))
                        , p1
                        , p2
                        ])
    | otherwise = return $ Err $
        UnexpectedArgumentType "Non-byte-sized bitvectors" [v1, v2]

    where low_w' = W4I.bvWidth low
          high_w' = W4I.bvWidth high

-- | Cons an element onto a partial LLVM array value.
consArray ::
  IsSymInterface sym =>
  PartLLVMVal arch sym ->
  PartLLVMVal arch sym ->
  PartLLVMVal arch sym
consArray (PartLLVMVal p1 (LLVMValZero tp)) (PartLLVMVal p2 (LLVMValZero (StorageType (Array m tp') _)))
  | tp == tp' =
      PartLLVMVal (W4P.binaryAnd p1 p2) $ LLVMValZero (Type.arrayType (m+1) tp')

consArray (PartLLVMVal p1 hd) (PartLLVMVal p2 (LLVMValZero (StorageType (Array m tp) _)))
  | Value.llvmValStorableType hd == tp =
      PartLLVMVal (W4P.binaryAnd p1 p2) $ LLVMValArray tp (V.cons hd (V.replicate (fromIntegral m) (LLVMValZero tp)))

consArray (PartLLVMVal p1 hd) (PartLLVMVal p2 (LLVMValArray tp vec))
  | Value.llvmValStorableType hd == tp =
      PartLLVMVal (W4P.binaryAnd p1 p2) $ LLVMValArray tp (V.cons hd vec)

consArray _ (PartLLVMVal _ v) =
  Err $ UnexpectedArgumentType "Non-array value" [v]

consArray (Err e1) (Err e2) =
  Err $ PreviousErrors "While consing onto an array" [e1, e2]

-- | Append two partial LLVM array values.
appendArray ::
  IsSymInterface sym =>
  PartLLVMVal arch sym ->
  PartLLVMVal arch sym ->
  PartLLVMVal arch sym
appendArray
  (PartLLVMVal p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PartLLVMVal p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 = PartLLVMVal (W4P.binaryAnd p1 p2) $
                   LLVMValZero (Type.arrayType (n1+n2) tp1)

appendArray
  (PartLLVMVal p1 (LLVMValZero (StorageType (Array n1 tp1) _)))
  (PartLLVMVal p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
      let v1 = V.replicate (fromIntegral n1) (LLVMValZero tp1)
      in PartLLVMVal (W4P.binaryAnd p1 p2) $
           LLVMValArray tp1 (v1 V.++ v2)

appendArray
  (PartLLVMVal p1 (LLVMValArray tp1 v1))
  (PartLLVMVal p2 (LLVMValZero (StorageType (Array n2 tp2) _)))
  | tp1 == tp2 =
      let v2 = V.replicate (fromIntegral n2) (LLVMValZero tp1)
      in PartLLVMVal (W4P.binaryAnd p1 p2) $
           LLVMValArray tp1 (v1 V.++ v2)

appendArray
  (PartLLVMVal p1 (LLVMValArray tp1 v1))
  (PartLLVMVal p2 (LLVMValArray tp2 v2))
  | tp1 == tp2 =
      PartLLVMVal (W4P.binaryAnd p1 p2) $
        LLVMValArray tp1 (v1 V.++ v2)

appendArray (PartLLVMVal _ v1) (PartLLVMVal _ v2) =
  Err $ UnexpectedArgumentType "Non-array value" [v1, v2]

appendArray _ (PartLLVMVal _ v2) =
  Err $ UnexpectedArgumentType "Non-array value" [v2]

appendArray (PartLLVMVal _ v1) _ =
  Err $ UnexpectedArgumentType "Non-array value" [v1]

appendArray (Err e1) (Err e2) =
  Err $ PreviousErrors "While consing onto an array" [e1, e2]


-- | Make a partial LLVM array value.
--
-- It returns 'Unassigned' if any of the elements of the vector are
-- 'Unassigned'. Otherwise, the 'AssertionTree' on the returned value
-- is the 'And' of all the assertions on the values.
mkArray :: forall arch sym. (IsExprBuilder sym, IsSymInterface sym) =>
  sym ->
  StorageType ->
  Vector (PartLLVMVal arch sym) ->
  PartLLVMVal arch sym
mkArray sym tp vec =
  let f :: PartLLVMVal arch sym
        -> State [AssertionClassifierTree (LLVM arch) (RegValue' sym)]
                 (LLVMVal sym)
      f (PartLLVMVal p x) = do
        ps_ <- get     -- Current predicates
        put (p:ps_)    -- Append this one
        pure x
      (vec', ps) = flip runState [] $ (traverse f vec)
  in
    case nonEmpty ps of
      Just ps' -> PartLLVMVal (And ps') $ LLVMValArray tp vec'
      Nothing  -> totalLLVMVal sym (LLVMValArray tp vec')


-- | Make a partial LLVM struct value.
--
-- It returns 'Unassigned' if any of the struct fields are 'Unassigned'.
-- Otherwise, the 'AssertionTree' on the returned value is the 'And' of all the
-- assertions on the values.
mkStruct :: forall arch sym. IsExprBuilder sym =>
  sym ->
  Vector (Field StorageType, PartLLVMVal arch sym) ->
  (PartLLVMVal arch sym)
mkStruct sym vec =
  let f :: (Field StorageType, PartLLVMVal arch sym)
        -> State [AssertionClassifierTree (LLVM arch) (RegValue' sym)]
                 (Field StorageType, LLVMVal sym)
      f (fld, PartLLVMVal p x) = do
        ps_ <- get
        put (p:ps_)
        pure (fld, x)
      (vec', ps) = flip runState [] $ (traverse f vec)
  in
    case nonEmpty ps of
      Just ps' -> PartLLVMVal (And ps') $ LLVMValStruct vec'
      Nothing  -> totalLLVMVal sym (LLVMValStruct vec')


-- | Select some of the least significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectLowBv ::
  IsSymInterface sym => sym ->
  Bytes ->
  Bytes ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)

selectLowBv _sym low hi (PartLLVMVal p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PartLLVMVal p $ LLVMValZero (Type.bitvectorType low)

selectLowBv sym low hi (PartLLVMVal p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (Bytes.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (Bytes.bytesToBits hi)
  , Just LeqProof       <- isPosNat low_w
  , Just Refl           <- testEquality (addNat low_w hi_w) w
  , Just LeqProof       <- testLeq low_w w = do
      pz  <- W4I.natEq sym blk =<< W4I.natLit sym 0
      bv' <- W4I.bvSelect sym (knownNat :: NatRepr 0) low_w bv
      let ub = UB.PointerCast (RV blk, RV bv) (Bitvector 0)
      return $ PartLLVMVal (addUndefinedBehaviorCondition sym ub pz p) $ LLVMValInt blk bv'
  where w = W4I.bvWidth bv
selectLowBv _ _ _ (PartLLVMVal _ v) =
  let msg = "While selecting the low bits of a bitvector"
  in return $ Err $ UnexpectedArgumentType msg [v]
selectLowBv _ _ _ (Err e) =
  let msg = "While selecting the low bits of a bitvector"
  in return $ Err $ PreviousErrors msg [e]

-- | Select some of the most significant bytes of a partial LLVM
-- bitvector value. The allocation block number of the argument is
-- asserted to equal 0, indicating a non-pointer.
selectHighBv ::
  IsSymInterface sym => sym ->
  Bytes ->
  Bytes ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)

selectHighBv _sym low hi (PartLLVMVal p (LLVMValZero (StorageType (Bitvector bytes) _)))
  | low + hi == bytes =
      return $ PartLLVMVal p $ LLVMValZero (Type.bitvectorType hi)

selectHighBv sym low hi (PartLLVMVal p (LLVMValInt blk bv))
  | Just (Some (low_w)) <- someNat (Bytes.bytesToBits low)
  , Just (Some (hi_w))  <- someNat (Bytes.bytesToBits hi)
  , Just LeqProof <- isPosNat hi_w
  , Just Refl <- testEquality (addNat low_w hi_w) w =
    do pz <-  W4I.natEq sym blk =<< W4I.natLit sym 0
       bv' <- W4I.bvSelect sym low_w hi_w bv
       let ub = UB.PointerCast (RV blk, RV bv) (Bitvector 0)
       return $ PartLLVMVal (addUndefinedBehaviorCondition sym ub pz p) $ LLVMValInt blk bv'
  where w = W4I.bvWidth bv
selectHighBv _ _ _ (PartLLVMVal _ v) =
  let msg = "While selecting the high bits of a bitvector"
  in return $ Err $ UnexpectedArgumentType msg [v]
selectHighBv _ _ _ (Err e) =
  let msg = "While selecting the high bits of a bitvector"
  in return $ Err $ PreviousErrors msg [e]


-- | Look up an element in a partial LLVM array value.
arrayElt ::
  Word64 ->
  StorageType ->
  Word64 ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)
arrayElt sz tp idx (PartLLVMVal p (LLVMValZero _)) -- TODO(langston) typecheck
  | 0 <= idx
  , idx < sz =
    return $ PartLLVMVal p (LLVMValZero tp)

arrayElt sz tp idx (PartLLVMVal p (LLVMValArray tp' vec))
  | sz == fromIntegral (V.length vec)
  , 0 <= idx
  , idx < sz
  , tp == tp' =
    return $ PartLLVMVal p (vec V.! fromIntegral idx)

arrayElt _ _ _ (PartLLVMVal _ v) =
  let msg = "While selecting the high bits of a bitvector"
  in return $ Err $ UnexpectedArgumentType msg [v]

arrayElt _ _ _ (Err e) =
  let msg = "While selecting the high bits of a bitvector"
  in return $ Err $ PreviousErrors msg [e]

-- | Look up a field in a partial LLVM struct value.
fieldVal ::
  (Vector (Field StorageType)) ->
  Int ->
  PartLLVMVal arch sym ->
  IO (PartLLVMVal arch sym)
fieldVal flds idx (PartLLVMVal p (LLVMValZero _)) -- TODO(langston) typecheck
  | 0 <= idx
  , idx < V.length flds =
      return $ PartLLVMVal p $ LLVMValZero $ view Type.fieldVal $ flds V.! idx

fieldVal flds idx (PartLLVMVal p (LLVMValStruct vec))
  | flds == fmap fst vec
  , 0 <= idx
  , idx < V.length vec =
    return $ PartLLVMVal p $ snd $ (vec V.! idx)

fieldVal _ _ (PartLLVMVal _ v) =
  let msg = "While getting a struct field"
  in return $ Err $ UnexpectedArgumentType msg [v]

fieldVal _ _ (Err e) =
  let msg = "While getting a struct field"
  in return $ Err $ PreviousErrors msg [e]

------------------------------------------------------------------------
-- ** Merging and muxing
--

-- | If-then-else on partial expressions.
merge :: forall arch sym m. (IsExprBuilder sym, MonadIO m) =>
  sym ->
  (Pred sym -> LLVMVal sym -> LLVMVal sym -> m (PartLLVMVal arch sym))
    {- ^ Operation to combine inner values. The 'Pred' parameter is the
         if/then/else condition -} ->
  Pred sym {- ^ condition to merge on -} ->
  PartLLVMVal arch sym {- ^ 'then' value -}  ->
  PartLLVMVal arch sym {- ^ 'else' value -} ->
  m (PartLLVMVal arch sym)
merge _ f cond (PartLLVMVal px x) (PartLLVMVal py y) = do
  PartLLVMVal pz z <- f cond x y
  pure $ PartLLVMVal (W4P.binaryAnd (Ite (RV cond) px py) pz) z

-- | Mux partial LLVM values.
muxLLVMVal :: forall arch sym
    . IsSymInterface sym
   => sym
   -> Pred sym
   -> PartLLVMVal arch sym
   -> PartLLVMVal arch sym
   -> IO (PartLLVMVal arch sym)
muxLLVMVal sym = merge sym muxval
  where

    muxzero :: Pred sym -> StorageType -> LLVMVal sym -> IO (LLVMVal sym)
    muxzero cond tpz val = case val of
      LLVMValZero tp -> return $ LLVMValZero tp
      LLVMValUndef tpu ->
        -- TODO: Is this the right behavior?
        panic "Cannot mux zero and undef" [ "Zero type: " ++ show tpz
                                          , "Undef type: " ++ show tpu
                                          ]
      LLVMValInt base off ->
        do zbase <- W4I.natLit sym 0
           zoff  <- W4I.bvLit sym (W4I.bvWidth off) 0
           base' <- W4I.natIte sym cond zbase base
           off'  <- W4I.bvIte sym cond zoff off
           return $ LLVMValInt base' off'
      LLVMValFloat Value.SingleSize x ->
        do zerof <- (W4IFP.iFloatLit sym W4IFP.SingleFloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.SingleFloat sym cond zerof x)
           return $ LLVMValFloat Value.SingleSize x'
      LLVMValFloat Value.DoubleSize x ->
        do zerof <- (W4IFP.iFloatLit sym W4IFP.DoubleFloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.DoubleFloat sym cond zerof x)
           return $ LLVMValFloat Value.DoubleSize x'
      LLVMValFloat Value.X86_FP80Size x ->
        do zerof <- (W4IFP.iFloatLit sym W4IFP.X86_80FloatRepr 0)
           x'    <- (W4IFP.iFloatIte @_ @W4IFP.X86_80Float sym cond zerof x)
           return $ LLVMValFloat Value.X86_FP80Size x'

      LLVMValArray tp vec -> LLVMValArray tp <$>
        traverse (muxzero cond tp) vec

      LLVMValStruct flds -> LLVMValStruct <$>
        traverse (\(fld, v) -> (fld,) <$>
                     muxzero cond (fld^.Type.fieldVal) v) flds


    muxval :: Pred sym -> LLVMVal sym -> LLVMVal sym -> IO (PartLLVMVal arch sym)
    muxval cond (LLVMValZero tp) v = totalLLVMVal sym <$> muxzero cond tp v
    muxval cond v (LLVMValZero tp) = do cond' <- W4I.notPred sym cond
                                        totalLLVMVal sym <$> muxzero cond' tp v

    muxval cond (LLVMValInt base1 off1) (LLVMValInt base2 off2)
      | Just Refl <- testEquality (W4I.bvWidth off1) (W4I.bvWidth off2)
      = do base <- liftIO $ W4I.natIte sym cond base1 base2
           off  <- liftIO $ W4I.bvIte sym cond off1 off2
           pure $ totalLLVMVal sym $ LLVMValInt base off

    muxval cond (LLVMValFloat (xsz :: Value.FloatSize fi) x) (LLVMValFloat ysz y)
      | Just Refl <- testEquality xsz ysz
      = totalLLVMVal sym .  LLVMValFloat xsz <$>
          (liftIO $ W4IFP.iFloatIte @_ @fi sym cond x y)

    muxval cond (LLVMValStruct fls1) (LLVMValStruct fls2)
      | fmap fst fls1 == fmap fst fls2 =
          mkStruct sym <$>
            V.zipWithM (\(f, x) (_, y) -> (f,) <$> muxval cond x y) fls1 fls2

    muxval cond (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
      | tp1 == tp2 && V.length v1 == V.length v2 = do
          mkArray sym tp1 <$> V.zipWithM (muxval cond) v1 v2

    muxval _ v1@(LLVMValUndef tp1) (LLVMValUndef tp2)
      | tp1 == tp2 = pure (totalLLVMVal sym v1)

    muxval _ v1 v2 =
      let msg = "While mixing LLVM values"
      in return $ Err $ UnexpectedArgumentType msg [v1, v2]
