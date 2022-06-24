{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Data.Foldable (forM_)
import System.IO (FilePath, IOMode(..), openFile)

import Data.Parameterized.Nonce (newIONonceGenerator)
import Data.Parameterized.Some (Some(..))

import What4.Config (extendConfig)
import What4.Expr
         ( ExprBuilder,  FloatModeRepr(..), newExprBuilder
         , BoolExpr, IntegerExpr, GroundValue, groundEval
         , EmptyExprBuilderState(..) )
import What4.Interface
         ( BaseTypeRepr(..), getConfiguration
         , freshConstant, safeSymbol, notPred
         , impliesPred, intLit, intAdd, intLe )
import What4.Solver
         (LogData(..), defaultLogData, z3Options, withZ3, cvc4Options, withCVC4, SatResult(..))
import What4.Protocol.SMTLib2
         (assume, sessionWriter, runCheckSat, runGetAbduct)
import What4.Protocol.SMTWriter
         (mkSMTTerm)

z3executable :: FilePath
z3executable = "z3"

cvc4executable :: FilePath
cvc4executable = "cvc4"

main :: IO ()
main = do
  Some ng <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr EmptyExprBuilderState ng

  -- The following is satisfiable. Let's get an abduct from the SMT solver,
  -- Some formula that will make it unsatisfiable (its negation provable)
  -- not (y >= 0 => (x + y + z) >= 0)
  -- This query to the SMT solver: (get-abduct A (=> (>= y 0) (>= (+ x y z) 0)))
  
  -- First, declare fresh constants for each of the three variables p, q, r.
  x <- freshConstant sym (safeSymbol "x") BaseIntegerRepr
  y <- freshConstant sym (safeSymbol "y") BaseIntegerRepr
  z <- freshConstant sym (safeSymbol "z") BaseIntegerRepr

  -- Next, build up the clause
  zero <- intLit sym 0                        -- 0
  pxyz <- intAdd sym x =<< intAdd sym y z -- x + y + z
  ygte0 <- intLe sym zero y               -- 0 <= y
  xyzgte0 <- intLe sym zero pxyz          -- 0 <= (x + y + z) 
  f <- impliesPred sym ygte0 xyzgte0      -- (0 <= y) -> (0 <= (x + y + z))

  -- Determine if ~f is satisfiable, and print the instance if one is found.
  {-
  notf <- notPred sym f
  call1 <- checkModel sym notf [ ("x", x)
                               , ("y", y)
                               , ("z", z)
                               ]
  -}

  -- Get me a formula that will allow me to prove f
  testGetAbduct sym f [ ("x", x)
                      , ("y", y)
                      , ("z", z)
                      ]

testGetAbduct :: 
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, IntegerExpr t)] ->
  IO ()
testGetAbduct sym f es = do
  putStrLn "testGetAbduct1:"
  mirroredOutput <- openFile "/tmp/what4abduct.smt2" ReadWriteMode
  let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                         , logVerbosity = 2
                         , logReason = "defaultReason"
                         , logHandle = Just mirroredOutput }
  withCVC4 sym cvc4executable logData $ \session -> do
    putStrLn "testGetAbduct2:"
    f_term <- mkSMTTerm (sessionWriter session) f
    abd <- runGetAbduct session "abd" f_term
    putStrLn "testGetAbduct3:"
    print abd

-- | Determine whether a predicate is satisfiable, and print out the values of a
-- set of expressions if a satisfying instance is found.
{-checkModel ::
  ExprBuilder t st fs ->
  BoolExpr t ->
  [(String, IntegerExpr t)] ->
  IO ()
checkModel sym f es = do
  -- We will use z3 to determine if f is satisfiable.
  mirroredOutput <- openFile "/tmp/quickstart.smt2" ReadWriteMode
  let logData = LogData { logCallbackVerbose = \_ _ -> return ()
                         , logVerbosity = 2
                         , logReason = "defaultReason"
                         , logHandle = Just mirroredOutput }
  withZ3 sym z3executable logData $ \session -> do
    -- Assume f is true.
    assume (sessionWriter session) f
    runCheckSat session $
      \case
        Sat (ge, _) -> do
          putStrLn "Satisfiable, with model:"
          forM_ es $ \(nm, e) -> do
            v <- groundEval ge e
            putStrLn $ "  " ++ nm ++ " := " ++ show v
        Unsat _ -> putStrLn "Unsatisfiable."
        Unknown -> putStrLn "Solver failed to find a solution."
    putStrLn ""-}
