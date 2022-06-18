{-# LANGUAGE GADTs #-}
module Main where

import Data.Foldable (forM_)
import System.IO (FilePath)

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))

import What4.Config (extendConfig)
import What4.Expr
         ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
         , BoolExpr, GroundValue, groundEval
         , EmptyExprBuilderState(..) )
import What4.Interface
         ( BaseTypeRepr(..), getConfiguration
         , freshConstant, safeSymbol
         , notPred, orPred, andPred )
import What4.Solver
         (defaultLogData, cvc4Options, withCVC4, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat)


cvc4executable :: FilePath
cvc4executable = "cvc4"

main :: IO ()
main = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng

  -- This line is necessary for working with cvc4.
  extendConfig cvc4Options (getConfiguration sym)

  -- Let's determine if the following formula is satisfiable:
  -- f(p, q, r) = (p | !q) & (q | r) & (!p | !r) & (!p | !q | r)

  -- First, declare fresh constants for each of the three variables p, q, r.
  p <- freshConstant sym (safeSymbol "p") BaseBoolRepr
  q <- freshConstant sym (safeSymbol "q") BaseBoolRepr
  r <- freshConstant sym (safeSymbol "r") BaseBoolRepr

  -- Next, create terms for the negation of p, q, and r.
  not_p <- notPred sym p
  not_q <- notPred sym q
  not_r <- notPred sym r

  -- Next, build up each clause of f individually.
  clause1 <- orPred sym p not_q
  clause2 <- orPred sym q r
  clause3 <- orPred sym not_p not_r
  clause4 <- orPred sym not_p =<< orPred sym not_q r

  -- Finally, create f out of the conjunction of all four clauses.
  f <- andPred sym clause1 =<<
       andPred sym clause2 =<<
       andPred sym clause3 clause4

  -- Determine if f is satisfiable, and print the instance if one is found.
  checkModel sym f [ ("p", p)
                   , ("q", q)
                   , ("r", r)
                   ]

  -- Now, let's add one more clause to f.
  clause5 <- orPred sym p =<< orPred sym q not_r
  g <- andPred sym f clause5

  -- Determine if g is satisfiable.
  checkModel sym g [ ("p", p)
                   , ("q", q)
                   , ("r", r)
                   ]

-- | Determine whether a predicate is satisfiable, and print out the values of a
-- set of expressions if a satisfying instance is found.
checkModel ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, BoolExpr t)] ->
  IO ()
checkModel sym f es = do
  -- We will use cvc4 to determine if f is satisfiable.
  withCVC4 sym cvc4executable defaultLogData $ \session -> do
    -- Assume f is true.
    assume (sessionWriter session) f
    runCheckSat session $ \result ->
      case result of
        Sat (ge, _) -> do
          putStrLn "Satisfiable, with model:"
          forM_ es $ \(nm, e) -> do
            v <- groundEval ge e
            putStrLn $ "  " ++ nm ++ " := " ++ show v
        Unsat _ -> putStrLn "Unsatisfiable."
        Unknown -> putStrLn "Solver failed to find a solution."
