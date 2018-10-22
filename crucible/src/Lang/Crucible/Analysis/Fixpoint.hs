{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Analysis.Fixpoint (
  -- * Entry point
  forwardFixpoint,
  forwardFixpoint',
  ScopedReg(..),
  Ignore(..),
  -- * Abstract Domains
  Domain(..),
  IterationStrategy(..),
  Interpretation(..),
  PointAbstraction(..),
  lookupAbstractRegValue,
  modifyAbstractRegValue,
  -- * Pointed domains
  -- $pointed
  Pointed(..),
  pointed
  ) where

import           Control.Applicative
import           Control.Lens.Operators ( (^.), (%=), (.~), (&), (%~) )
import qualified Control.Monad.State.Strict as St
import qualified Data.Functor.Identity as I
import qualified Data.Set as S
import           Text.Printf

import           Prelude

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as PU
import qualified Data.Parameterized.Map as PM
import qualified Data.Parameterized.TraversableFC as PU

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Analysis.Fixpoint.Components

-- | A wrapper around widening strategies
data WideningStrategy = WideningStrategy (Int -> Bool)

-- | A wrapper around widening operators.  This is mostly here to
-- avoid requiring impredicative types later.
data WideningOperator dom = WideningOperator (forall tp . dom tp -> dom tp -> dom tp)

-- | The iteration strategies available for computing fixed points.
--
-- Algorithmically, the best strategies seem to be based on Weak
-- Topological Orders (WTOs).  The WTO approach also naturally
-- supports widening (with a specified widening strategy and widening
-- operator).
--
-- A simple worklist approach is also available.
data IterationStrategy (dom :: CrucibleType -> *) where
  WTO :: IterationStrategy dom
  WTOWidening :: (Int -> Bool) -> (forall tp . dom tp -> dom tp -> dom tp) -> IterationStrategy dom
  Worklist :: IterationStrategy dom

-- | A domain of abstract values, parameterized by a term type
data Domain (dom :: CrucibleType -> *) =
  Domain { domTop    :: forall tp . dom tp
         , domBottom :: forall tp . dom tp
         , domJoin   :: forall tp . dom tp -> dom tp -> dom tp
         , domIter   :: IterationStrategy dom
         , domEq     :: forall tp . dom tp -> dom tp -> Bool
         }

-- | Transfer functions for each statement type
data Interpretation ext (dom :: CrucibleType -> *) =
  Interpretation { interpExpr       :: forall ctx tp
                                     . ScopedReg
                                    -> TypeRepr tp
                                    -> Expr ext ctx tp
                                    -> PointAbstraction dom ctx
                                    -> (Maybe (PointAbstraction dom ctx), dom tp)
                 , interpExt        :: forall ctx tp
                                     . StmtExtension ext (Reg ctx) tp
                                    -> PointAbstraction dom ctx
                                    -> (Maybe (PointAbstraction dom ctx), dom tp)
                 , interpCall       :: forall ctx args ret
                                     . CtxRepr args
                                    -> TypeRepr ret
                                    -> Reg ctx (FunctionHandleType args ret)
                                    -> dom (FunctionHandleType args ret)
                                    -> PU.Assignment dom args
                                    -> PointAbstraction dom ctx
                                    -> (Maybe (PointAbstraction dom ctx), dom ret)
                 , interpReadGlobal :: forall ctx tp
                                     . GlobalVar tp
                                    -> PointAbstraction dom ctx
                                    -> (Maybe (PointAbstraction dom ctx), dom tp)
                 , interpWriteGlobal :: forall ctx tp
                                      . GlobalVar tp
                                     -> Reg ctx tp
                                     -> PointAbstraction dom ctx
                                     -> Maybe (PointAbstraction dom ctx)
                 , interpBr         :: forall blocks ctx
                                     . Reg ctx BoolType
                                    -> dom BoolType
                                    -> JumpTarget blocks ctx
                                    -> JumpTarget blocks ctx
                                    -> PointAbstraction dom ctx
                                    -> (Maybe (PointAbstraction dom ctx), Maybe (PointAbstraction dom ctx))
                 , interpMaybe      :: forall ctx tp
                                     . TypeRepr tp
                                    -> Reg ctx (MaybeType tp)
                                    -> dom (MaybeType tp)
                                    -> PointAbstraction dom ctx
                                    -> (Maybe (PointAbstraction dom ctx), dom tp, Maybe (PointAbstraction dom ctx))
                 }

-- | This abstraction contains the abstract values of each register at
-- the program point represented by the abstraction.  It also contains
-- a map of abstractions for all of the global variables currently
-- known.
data PointAbstraction dom ctx =
  PointAbstraction { _paGlobals :: PM.MapF GlobalVar dom
                   , _paRegisters :: PU.Assignment dom ctx
                   }

instance ShowF dom => Show (PointAbstraction dom ctx) where
  show pa = show (_paRegisters pa)

instance ShowF dom => ShowF (PointAbstraction dom)

-- | Look up the abstract value of a register at a program point
lookupAbstractRegValue :: PointAbstraction dom ctx -> Reg ctx tp -> dom tp
lookupAbstractRegValue pa (Reg ix) = (pa ^. paRegisters) PU.! ix

-- | Modify the abstract value of a register at a program point
modifyAbstractRegValue :: PointAbstraction dom ctx
                       -> Reg ctx tp
                       -> (dom tp -> dom tp)
                       -> PointAbstraction dom ctx
modifyAbstractRegValue pa (Reg ix) f = pa & paRegisters . ixF ix %~ f

-- | The `FunctionAbstraction` contains the abstractions for the entry
-- point of each basic block in the function, as well as the final
-- abstract value for the returned register.
data FunctionAbstraction (dom :: CrucibleType -> *) blocks ret =
  FunctionAbstraction { _faEntryRegs :: PU.Assignment (PointAbstraction dom) blocks
                        -- ^ Mapping from blocks to point abstractions
                        -- at entry to blocks.
                      , _faExitRegs :: PU.Assignment (Ignore (Some (PointAbstraction dom))) blocks
                        -- ^ Mapping from blocks to point abstractions
                        -- at exit from blocks. Blocks are indexed by
                        -- their entry context, but not by there exit
                        -- contexts, so we wrap the point abstraction
                        -- in @Ignore . Some@ to hide the context of
                        -- SSA tmps at exit.
                      , _faRet :: dom ret
                        -- ^ Abstract value at return from function.
                      }

data IterationState (dom :: CrucibleType -> *) blocks ret =
  IterationState { _isFuncAbstr :: FunctionAbstraction dom blocks ret
                 , _isRetAbstr  :: dom ret
                 , _processedOnce :: S.Set (Some (BlockID blocks))
                 }

newtype M (dom :: CrucibleType -> *) blocks ret a = M { runM :: St.State (IterationState dom blocks ret) a }
  deriving (St.MonadState (IterationState dom blocks ret), Monad, Applicative, Functor)

extendRegisters :: dom tp -> PointAbstraction dom ctx -> PointAbstraction dom (ctx ::> tp)
extendRegisters domVal pa =
  pa { _paRegisters = PU.extend (_paRegisters pa) domVal }

-- | Join two point abstractions using the join operation of the domain.
--
-- We join registers pointwise.  For globals, we explicitly call join
-- when the global is in both maps.  If a global is only in one map,
-- there is an implicit join with bottom, which always results in the
-- same element.  Since it is a no-op, we just skip it and keep the
-- one present element.
joinPointAbstractions :: forall (dom :: CrucibleType -> *) ctx
                       . Domain dom
                      -> PointAbstraction dom ctx
                      -> PointAbstraction dom ctx
                      -> PointAbstraction dom ctx
joinPointAbstractions dom = zipPAWith (domJoin dom)

zipPAWith :: forall (dom :: CrucibleType -> *) ctx
                       . (forall tp . dom tp -> dom tp -> dom tp)
                      -> PointAbstraction dom ctx
                      -> PointAbstraction dom ctx
                      -> PointAbstraction dom ctx
zipPAWith op pa1 pa2 =
  pa1 { _paRegisters = PU.zipWith op (pa1 ^. paRegisters) (pa2 ^. paRegisters)
      , _paGlobals = I.runIdentity $ do
          PM.mergeWithKeyM (\_ a b -> return (Just (op a b))) return return (pa1 ^. paGlobals) (pa2 ^. paGlobals)
      }

-- | Compare two point abstractions for equality.
--
-- Note that the globals maps are converted to a list and the lists
-- are checked for equality.  This should be safe if order is
-- preserved properly in the list functions...
equalPointAbstractions :: forall (dom :: CrucibleType -> *) ctx
                        . Domain dom
                       -> PointAbstraction dom ctx
                       -> PointAbstraction dom ctx
                       -> Bool
equalPointAbstractions dom pa1 pa2 =
  PU.foldlFC (\a (Ignore b) -> a && b) True pointwiseEqualRegs && equalGlobals
  where
    checkGlobal (PM.Pair gv1 d1) (PM.Pair gv2 d2) =
      case PM.testEquality gv1 gv2 of
        Just Refl -> domEq dom d1 d2
        Nothing -> False
    equalGlobals = and $ zipWith checkGlobal (PM.toList (pa1 ^. paGlobals)) (PM.toList (pa2 ^. paGlobals))
    pointwiseEqualRegs = PU.zipWith (\a b -> Ignore (domEq dom a b)) (pa1 ^. paRegisters) (pa2 ^. paRegisters)

----------------------------------------------------------------

-- | A CFG-scoped SSA temp register.
--
-- We don't care about the type params yet, hence the
-- existential quantification. We may want to look up the instruction
-- corresponding to a 'ScopedReg' after analysis though, and we'll
-- surely want to compare 'ScopedReg's for equality, and use them to
-- look up values in point abstractions after analysis.
data ScopedReg {- :: Ctx (Ctx CrucibleType) -> * -} where
  ScopedReg :: BlockID blocks ctx1 -> Reg ctx2 tp -> ScopedReg
-- The pretty-show library can't parse the derived version, because it
-- doesn't like bare "%" and/or "$" in atoms.
{- deriving instance Show ScopedReg -}
instance Show ScopedReg where
  showsPrec p (ScopedReg b r) =
    showParen (p > 0) $
    showString (printf "ScopedReg \"%s\" \"%s\"" (show b) (show r))
instance Eq ScopedReg where
  sr1 == sr2 =
    scopedRegIndexVals sr1 == scopedRegIndexVals sr2
instance Ord ScopedReg where
  sr1 `compare` sr2 =
    scopedRegIndexVals sr1 `compare` scopedRegIndexVals sr2

scopedRegIndexVals :: ScopedReg -> (Int, Int)
scopedRegIndexVals (ScopedReg b r) = (blockIDIndexVal b, regIndexVal r)

blockIDIndexVal :: BlockID ctx tp -> Int
blockIDIndexVal = PU.indexVal . blockIDIndex

regIndexVal :: Reg ctx tp -> Int
regIndexVal = PU.indexVal . regIndex

----------------------------------------------------------------

-- | Apply the transfer functions from an interpretation to a block,
-- given a starting set of abstract values.
--
-- Return a set of blocks to visit later.
transfer :: forall ext dom blocks ret ctx
          . ShowF dom
         => Domain dom
         -> Interpretation ext dom
         -> TypeRepr ret
         -> Block ext blocks ret ctx
         -> PointAbstraction dom ctx
         -> M dom blocks ret (S.Set (Some (BlockID blocks)))
transfer dom interp retRepr blk = transferSeq blockInputSize (_blockStmts blk)
  where
    blockInputSize :: PU.Size ctx
    blockInputSize = PU.size $ blockInputs blk

    -- We maintain the current 'Size' of the context so that we can
    -- compute the SSA temp register corresponding to the current
    -- statement.
    transferSeq :: forall ctx'
                 . PU.Size ctx'
                -> StmtSeq ext blocks ret ctx'
                -> PointAbstraction dom ctx'
                -> M dom blocks ret (S.Set (Some (BlockID blocks)))
    transferSeq sz (ConsStmt _loc stmt ss) =
      transferSeq (nextStmtHeight sz stmt) ss .
      transferStmt sz stmt
    transferSeq _sz (TermStmt _loc term) = transferTerm term

    transferStmt :: forall ctx1 ctx2
                  . PU.Size ctx1
                 -> Stmt ext ctx1 ctx2
                 -> PointAbstraction dom ctx1
                 -> PointAbstraction dom ctx2
    transferStmt sz s assignment =
      case s of
        SetReg (tp :: TypeRepr tp) ex ->
          let reg :: Reg (ctx1 ::> tp) tp
              reg = Reg (PU.nextIndex sz)
              scopedReg = ScopedReg (blockID blk) reg
              (assignment', absVal) = interpExpr interp scopedReg tp ex assignment
              assignment'' = maybe assignment (joinPointAbstractions dom assignment) assignment'
          in extendRegisters absVal assignment''

        ExtendAssign estmt ->
          let (assignment', absVal) = interpExt interp estmt assignment
              assignment'' = maybe assignment (joinPointAbstractions dom assignment) assignment'
          in extendRegisters absVal assignment''

        -- This statement aids in debugging the representation, but
        -- should not be a meaningful part of any analysis.  For now,
        -- skip it in the interpretation.  We could add a transfer
        -- function for it...
        --
        -- Note that this is not used to represent print statements in
        -- the language being represented.  This is a *crucible* level
        -- print.  This is actually apparent in the type of Print,
        -- which does not modify its context at all.
        Print _reg -> assignment

        CallHandle retTp funcHandle argTps actuals ->
          let actualsAbstractions = PU.zipWith (\_ act -> lookupReg act assignment) argTps actuals
              funcAbstraction = lookupReg funcHandle assignment
              (assignment', absVal) = interpCall interp argTps retTp funcHandle funcAbstraction actualsAbstractions assignment
              assignment'' = maybe assignment (joinPointAbstractions dom assignment) assignment'
          in extendRegisters absVal assignment''

        -- FIXME: This would actually potentially be nice to
        -- capture. We would need to extend the context,
        -- though... maybe with a unit type.
        Assert _ _ -> assignment
        Assume _ _ -> assignment

        ReadGlobal gv ->
          let (assignment', absVal) = interpReadGlobal interp gv assignment
              assignment'' = maybe assignment (joinPointAbstractions dom assignment) assignment'
          in extendRegisters absVal assignment''
        WriteGlobal gv reg ->
          let assignment' = interpWriteGlobal interp gv reg assignment
          in maybe assignment (joinPointAbstractions dom assignment) assignment'

        FreshConstant{} -> error "transferStmt: FreshConstant not supported"
        NewEmptyRefCell{} -> error "transferStmt: NewEmptyRefCell not supported"
        NewRefCell {} -> error "transferStmt: NewRefCell not supported"
        ReadRefCell {} -> error "transferStmt: ReadRefCell not supported"
        WriteRefCell {} -> error "transferStmt: WriteRefCell not supported"
        DropRefCell {} -> error "transferStmt: DropRefCell not supported"

    -- Transfer a block terminator statement.
    transferTerm :: forall ctx'
                  . TermStmt blocks ret ctx'
                 -> PointAbstraction dom ctx'
                 -> M dom blocks ret (S.Set (Some (BlockID blocks)))
    transferTerm s assignment = do
      -- Save the current point abstraction as the exit point
      -- abstraction since we won't be defining any more SSA tmps in
      -- this block.
      let BlockID srcIdx = blockID blk
      isFuncAbstr %= (faExitRegs . ixF srcIdx .~ Ignore (Some assignment))

      case s of
        ErrorStmt {} -> return S.empty
        Jump target -> transferJump target assignment
        Br condReg target1 target2 -> do
          let condAbst = lookupReg condReg assignment
              (d1, d2) = interpBr interp condReg condAbst target1 target2 assignment
              d1' = maybe assignment (joinPointAbstractions dom assignment) d1
              d2' = maybe assignment (joinPointAbstractions dom assignment) d2
          s1 <- transferJump target1 d1'
          s2 <- transferJump target2 d2'
          return (S.union s1 s2)
        MaybeBranch tp mreg swTarget jmpTarget -> do
          let condAbst = lookupReg mreg assignment
              (d1, mAbstraction, d2) = interpMaybe interp tp mreg condAbst assignment
              d1' = maybe assignment (joinPointAbstractions dom assignment) d1
              d2' = maybe assignment (joinPointAbstractions dom assignment) d2
          s1 <- transferSwitch swTarget mAbstraction d1'
          s2 <- transferJump jmpTarget d2'
          return (S.union s1 s2)
        Return reg -> do
          let absVal = lookupReg reg assignment
          isRetAbstr %= domJoin dom absVal
          return S.empty

        TailCall fn callArgs actuals -> do
          let argAbstractions = PU.zipWith (\_tp act -> lookupReg act assignment) callArgs actuals
              callee = lookupReg fn assignment
              (_assignment', absVal) = interpCall interp callArgs retRepr fn callee argAbstractions assignment
              -- assignment'' = maybe assignment (joinPointAbstractions dom assignment) assignment'

          -- We don't really have a place to put a modified assignment
          -- here, which is interesting.  There is no next block...
          isRetAbstr %= domJoin dom absVal
          return S.empty

        VariantElim {} -> error "transferTerm: VariantElim terminator not supported"


    transferJump :: forall ctx'
                  . JumpTarget blocks ctx'
                 -> PointAbstraction dom ctx'
                 -> M dom blocks ret (S.Set (Some (BlockID blocks)))
    transferJump (JumpTarget target argsTps actuals) assignment = do
      let argRegAbstractions = PU.zipWith (\_tp act -> lookupReg act assignment) argsTps actuals
          blockAbstr0 = assignment { _paRegisters = argRegAbstractions }
      transferTarget target blockAbstr0

    transferSwitch :: forall ctx' tp
                    . SwitchTarget blocks ctx' tp
                   -> dom tp
                   -> PointAbstraction dom ctx'
                   -> M dom blocks ret (S.Set (Some (BlockID blocks)))
    transferSwitch (SwitchTarget target argTps actuals) domVal assignment = do
      let argRegAbstractions = PU.zipWith (\_ act -> lookupReg act assignment) argTps actuals
          blockAbstr0 = assignment { _paRegisters = PU.extend argRegAbstractions domVal }
      transferTarget target blockAbstr0

    -- Return the singleton set containing the target block if we
    -- haven't converged yet on the current block, and otherwise
    -- return an empty set while updating the function abstraction for
    -- the current block.
    transferTarget :: forall ctx'
                    . BlockID blocks ctx'
                   -> PointAbstraction dom ctx'
                   -> M dom blocks ret (S.Set (Some (BlockID blocks)))
    transferTarget target@(BlockID idx) assignment = do
      old <- lookupAssignment idx
      haveVisited <- isVisited target
      let new = joinPointAbstractions dom old assignment
      case haveVisited && equalPointAbstractions dom old new of
        True -> return S.empty
        False -> do
          markVisited target
          isFuncAbstr %= (faEntryRegs . ixF idx .~ new)
          return (S.singleton (Some target))

markVisited :: BlockID blocks ctx -> M dom blocks ret ()
markVisited bid = do
  processedOnce %= S.insert (Some bid)

isVisited :: BlockID blocks ctx -> M dom blocks ret Bool
isVisited bid = do
  s <- St.gets _processedOnce
  return (Some bid `S.member` s)

-- | Compute a fixed point via abstract interpretation over a control
-- flow grap ('CFG') given 1) an interpretation + domain, 2) initial
-- assignments of domain values to global variables, and 3) initial
-- assignments of domain values to function arguments.
--
-- This is an intraprocedural analysis.  To handle function calls, the
-- transfer function for call statements must know how to supply
-- summaries or compute an appropriate conservative approximation.
--
-- There are two results from the fixed point computation:
--
-- 1) For each block in the CFG, the abstraction computed at the *entry* to the block
--
-- 2) The final abstract value for the value returned by the function
forwardFixpoint' :: forall ext dom blocks ret init
                 . ShowF dom
                => Domain dom
                -- ^ The domain of abstract values
                -> Interpretation ext dom
                -- ^ The transfer functions for each statement type
                -> CFG ext blocks init ret
                -- ^ The function to analyze
                -> PM.MapF GlobalVar dom
                -- ^ Assignments of abstract values to global variables at the function start
                -> PU.Assignment dom init
                -- ^ Assignments of abstract values to the function arguments
                -> (PU.Assignment (PointAbstraction dom) blocks, PU.Assignment (Ignore (Some (PointAbstraction dom))) blocks, dom ret)
forwardFixpoint' dom interp cfg globals0 assignment0 =
  let BlockID idx = cfgEntryBlockID cfg
      pa0 = PointAbstraction { _paGlobals = globals0
                             , _paRegisters = assignment0
                             }
      freshAssignment :: PU.Index blocks ctx -> PointAbstraction dom ctx
      freshAssignment i =
        PointAbstraction { _paRegisters = PU.fmapFC (const (domBottom dom)) (blockInputs (getBlock (BlockID i) (cfgBlockMap cfg)))
                         , _paGlobals = PM.empty
                         }
      emptyFreshAssignment :: PU.Index blocks ctx -> Ignore (Some (PointAbstraction dom)) ctx
      emptyFreshAssignment _i =
        Ignore (Some (PointAbstraction { _paRegisters = PU.empty, _paGlobals = PM.empty }))
      s0 = IterationState { _isRetAbstr = domBottom dom
                          , _isFuncAbstr =
                            FunctionAbstraction { _faEntryRegs =
                                                    PU.generate (PU.size (cfgBlockMap cfg)) freshAssignment
                                                      & ixF idx .~ pa0
                                                , _faExitRegs = PU.generate (PU.size (cfgBlockMap cfg)) emptyFreshAssignment
                                                , _faRet = domBottom dom
                                                }
                          , _processedOnce = S.empty
                          }
      iterStrat = iterationStrategy dom
      abstr' = St.execState (runM (iterStrat interp cfg)) s0
  in ( _faEntryRegs (_isFuncAbstr abstr')
     , _faExitRegs (_isFuncAbstr abstr')
     , _isRetAbstr abstr' )

-- Preserve old interface for now; fix tests later if my generalization is the right one.
forwardFixpoint :: forall ext dom blocks ret init
                . ShowF dom
                => Domain dom
                -> Interpretation ext dom
                -> CFG ext blocks init ret
                -> PM.MapF GlobalVar dom
                -> PU.Assignment dom init
                -> (PU.Assignment (PointAbstraction dom) blocks, dom ret)
forwardFixpoint dom interp cfg globals0 assignment0 =
  let (ass, _, ret) = forwardFixpoint' dom interp cfg globals0 assignment0
  in (ass, ret)

-- | Inspect the 'Domain' definition to determine which iteration
-- strategy the caller requested.
iterationStrategy :: ShowF dom => Domain dom -> (Interpretation ext dom -> CFG ext blocks init ret -> M dom blocks ret ())
iterationStrategy dom =
  case domIter dom of
    WTOWidening s op -> wtoIteration (Just (WideningStrategy s, WideningOperator op)) dom
    WTO -> wtoIteration Nothing dom
    Worklist -> worklistIteration dom

-- | Iterate over blocks using a worklist (i.e., after a block is
-- processed and abstract values change, put the block successors on
-- the worklist).
--
-- The worklist is actually processed by taking the lowest-numbered
-- block in a set as the next work item.
worklistIteration :: forall ext dom blocks ret init
                   . ShowF dom
                  => Domain dom
                  -> Interpretation ext dom
                  -> CFG ext blocks init ret
                  -> M dom blocks ret ()
worklistIteration dom interp cfg =
  loop (S.singleton (Some (cfgEntryBlockID cfg)))
  where
    loop worklist =
      case S.minView worklist of
        Nothing -> return ()
        Just (Some target@(BlockID idx), worklist') -> do
          assignment <- lookupAssignment idx
          visit (getBlock target (cfgBlockMap cfg)) assignment worklist'

    visit :: Block ext blocks ret ctx
          -> PointAbstraction dom ctx
          -> S.Set (Some (BlockID blocks))
          -> M dom blocks ret ()
    visit blk startingAssignment worklist' = do
      s <- transfer dom interp (cfgReturnType cfg) blk startingAssignment
      loop (S.union s worklist')

-- | Iterate over the blocks in the control flow graph in weak
-- topological order until a fixed point is reached.
--
-- The weak topological order essentially formalizes the idea of
-- breaking the graph on back edges and putting the result in
-- topological order.  The blocks that serve as loop heads are the
-- heads of their respective strongly connected components.  Those
-- block heads are suitable locations to apply widening operators
-- (which can be provided to this iterator).
wtoIteration :: forall ext dom blocks ret init
              . ShowF dom
             => Maybe (WideningStrategy, WideningOperator dom)
              -- ^ An optional widening operator
             -> Domain dom
             -> Interpretation ext dom
             -> CFG ext blocks init ret
             -> M dom blocks ret ()
wtoIteration mWiden dom interp cfg = loop (computeOrdering cfg)
  where
    loop [] = return ()
    loop (Vertex (Some bid@(BlockID idx)) : rest) = do
      assignment <- lookupAssignment idx
      let blk = getBlock bid (cfgBlockMap cfg)
      _ <- transfer dom interp (cfgReturnType cfg) blk assignment
      loop rest
    loop (SCC { wtoHead = hbid, wtoComps = comps } : rest) = do
      processSCC hbid comps 0
      loop rest

    -- Process a single SCC until the input to the head node of the
    -- SCC stabilizes.  Applies widening if requested.
    processSCC (Some hbid@(BlockID idx)) comps iterNum = do
      headInput0 <- lookupAssignment idx
      -- We process the SCC until the input to the head of the SCC stabilizes
      let headBlock = getBlock hbid (cfgBlockMap cfg)
      _ <- transfer dom interp (cfgReturnType cfg) headBlock headInput0
      loop comps
      headInput1 <- lookupAssignment idx
      case equalPointAbstractions dom headInput0 headInput1 of
        True -> return ()
        False -> do
          case mWiden of
            -- TODO(conathan): figure out if we need to do something
            -- here with 'faExitRegs'?
            Just (WideningStrategy strat, WideningOperator widen)
              | strat iterNum -> do
                  let headInputW = zipPAWith widen headInput0 headInput1
                  isFuncAbstr %= (faEntryRegs . ixF idx .~ headInputW)
            _ -> return ()
          processSCC (Some hbid) comps (iterNum + 1)

-- | Compute a weak topological order for the wto fixpoint iteration
computeOrdering :: CFG ext blocks init ret
                -> [WTOComponent (Some (BlockID blocks))]
computeOrdering cfg = weakTopologicalOrdering successors (Some block0)
  where
    block0 = cfgEntryBlockID cfg
    successors (Some bid) = nextBlocks (getBlock bid (cfgBlockMap cfg))

lookupAssignment :: forall dom blocks ret tp
                  . PU.Index blocks tp
                 -> M dom blocks ret (PointAbstraction dom tp)
lookupAssignment idx = do
  abstr <- St.get
  return ((abstr ^. isFuncAbstr . faEntryRegs) PU.! idx)

lookupReg :: Reg ctx tp -> PointAbstraction dom ctx -> dom tp
lookupReg reg assignment = (assignment ^. paRegisters) PU.! regIndex reg

-- | Turn a non paramaterized type into a parameterized type.
--
-- For when you want to use a @parameterized-utils@ style data
-- structure with a type that doesn't have a parameter.
--
-- The same definition as 'Control.Applicative.Const', but with a
-- different 'Show' instance.
newtype Ignore a (b::k) = Ignore { _ignoreOut :: a }
 deriving (Eq, Ord)

instance Show a => Show (Ignore a tp) where
  show (Ignore x) = show x

instance Show a => ShowF (Ignore a)

-- Lenses

paGlobals :: (Functor f)
          => (PM.MapF GlobalVar dom -> f (PM.MapF GlobalVar dom))
          -> PointAbstraction dom ctx
          -> f (PointAbstraction dom ctx)
paGlobals f pa = (\a -> pa { _paGlobals = a }) <$> f (_paGlobals pa)

paRegisters :: (Functor f)
            => (PU.Assignment dom ctx -> f (PU.Assignment dom ctx))
            -> PointAbstraction dom ctx
            -> f (PointAbstraction dom ctx)
paRegisters f pa = (\a -> pa { _paRegisters = a }) <$> f (_paRegisters pa)

faEntryRegs :: (Functor f)
            => (PU.Assignment (PointAbstraction dom) blocks -> f (PU.Assignment (PointAbstraction dom) blocks))
            -> FunctionAbstraction dom blocks ret
            -> f (FunctionAbstraction dom blocks ret)
faEntryRegs f fa = (\a -> fa { _faEntryRegs = a }) <$> f (_faEntryRegs fa)

faExitRegs :: (Functor f)
           => (PU.Assignment (Ignore (Some (PointAbstraction dom))) blocks -> f (PU.Assignment (Ignore (Some (PointAbstraction dom))) blocks))
           -> FunctionAbstraction dom blocks ret
           -> f (FunctionAbstraction dom blocks ret)
faExitRegs f fa = (\a -> fa { _faExitRegs = a }) <$> f (_faExitRegs fa)

isFuncAbstr :: (Functor f)
            => (FunctionAbstraction dom blocks ret -> f (FunctionAbstraction dom blocks ret))
            -> IterationState dom blocks ret
            -> f (IterationState dom blocks ret)
isFuncAbstr f is = (\a -> is { _isFuncAbstr = a }) <$> f (_isFuncAbstr is)

isRetAbstr :: (Functor f) => (dom ret -> f (dom ret)) -> IterationState dom blocks ret -> f (IterationState dom blocks ret)
isRetAbstr f is = (\a -> is { _isRetAbstr = a }) <$> f (_isRetAbstr is)

processedOnce :: (Functor f)
              => (S.Set (Some (BlockID blocks)) -> f (S.Set (Some (BlockID blocks))))
              -> IterationState dom blocks ret
              -> f (IterationState dom blocks ret)
processedOnce f is = (\a -> is { _processedOnce = a}) <$> f (_processedOnce is)

-- $pointed
--
-- The 'Pointed' type is a wrapper around another 'Domain' that
-- provides distinguished 'Top' and 'Bottom' elements.  Use of this
-- type is never required (domains can always define their own top and
-- bottom), but this1 wrapper can save some boring boilerplate.

-- | The Pointed wrapper that adds Top and Bottom elements
data Pointed dom (tp :: CrucibleType) where
  Top :: Pointed a tp
  Pointed :: dom tp -> Pointed dom tp
  Bottom :: Pointed dom tp

deriving instance (Eq (dom tp)) => Eq (Pointed dom tp)

instance ShowF dom => Show (Pointed dom tp) where
  show Top = "Top"
  show Bottom = "Bottom"
  show (Pointed p) = showF p

instance ShowF dom => ShowF (Pointed dom)

-- | Construct a 'Pointed' 'Domain' from a pointed join function and
-- an equality test.
pointed :: (forall tp . dom tp -> dom tp -> Pointed dom tp)
        -- ^ Join of contained domain elements
        -> (forall tp . dom tp -> dom tp -> Bool)
        -- ^ Equality for domain elements
        -> IterationStrategy (Pointed dom)
        -> Domain (Pointed dom)
pointed j eq iterStrat =
  Domain { domTop = Top
         , domBottom = Bottom
         , domJoin = pointedJoin j
         , domEq = pointedEq eq
           -- TODO(conathan): test faExitRegs computation with WTO
           -- strategy. It was hardcoded to 'WTO' here before conathan
           -- added block-exit point abstractions.
         , domIter = iterStrat
         }

  where
    pointedJoin _ Top _ = Top
    pointedJoin _ _ Top = Top
    pointedJoin _ Bottom a = a
    pointedJoin _ a Bottom = a
    pointedJoin j' (Pointed p1) (Pointed p2) = j' p1 p2

    pointedEq _ Top Top = True
    pointedEq _ Bottom Bottom = True
    pointedEq eq' (Pointed p1) (Pointed p2) = eq' p1 p2
    pointedEq _ _ _ = False
