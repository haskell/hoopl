{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module Test (parseTest, evalTest, optTest) where

import Compiler.Hoopl
import Control.Monad.Error

import Ast2ir
import ConstProp
import Eval  (evalProg, ErrorM)
import IR
import Live
import Parse (parseCode)
import Simplify

parse :: String -> String -> ErrorM (M [Proc])
parse file text =
  case parseCode file text of
    Left  err -> throwError $ show err
    Right ps  -> return $ mapM astToIR ps

parseTest :: String -> IO ()
parseTest file =
  do text <- readFile file
     case parse file text of
       Left err -> putStrLn err
       Right p  -> mapM (putStrLn . showProc) (runSimpleUniqueMonad $ runWithFuel 0 p) >> return ()

evalTest' :: String -> String -> ErrorM String
evalTest' file text =
  do procs   <- parse file text
     (_, vs) <- testProg (runSimpleUniqueMonad $ runWithFuel 0 procs)
     return $ "returning: " ++ show vs
  where
    testProg procs@(Proc {name, args} : _) = evalProg procs vsupply name (toV args)
    testProg _ = throwError "No procedures in test program"
    toV args = [I n | (n, _) <- zip [3..] args]
    vsupply = [I x | x <- [5..]]

evalTest :: String -> IO ()
evalTest file =
  do text    <- readFile file
     case evalTest' file text of
       Left err -> putStrLn err
       Right  s -> putStrLn s

optTest' :: String -> String -> ErrorM (M [Proc])
optTest' file text =
  do procs <- parse file text
     return $ procs >>= mapM optProc
  where
    optProc proc@(Proc {entry, body, args}) =
      do { (body',  _, _) <- analyzeAndRewriteFwd fwd (JustC [entry]) body
                             (mapSingleton entry (initFact args))
         ; (body'', _, _) <- analyzeAndRewriteBwd bwd (JustC [entry]) body' mapEmpty
         ; return $ proc { body = body'' } }
    -- With debugging info: 
    -- fwd  = debugFwdJoins trace (const True) $ FwdPass { fp_lattice = constLattice, fp_transfer = varHasLit
    --                                      , fp_rewrite = constProp `thenFwdRw` simplify }
    fwd  = constPropPass
    bwd  = BwdPass { bp_lattice = liveLattice, bp_transfer = liveness
                   , bp_rewrite = deadAsstElim }

constPropPass :: FuelMonad m => FwdPass m Insn ConstFact
-- @ start cprop.tex

----------------------------------------
-- Defining the forward dataflow pass
constPropPass = FwdPass
  { fp_lattice  = constLattice
  , fp_transfer = varHasLit
  , fp_rewrite  = constProp `thenFwdRw` simplify }
-- @ end cprop.tex

optTest :: String -> IO ()
optTest file =
  do text    <- readFile file
     case optTest' file text of
       Left err -> putStrLn err
       Right p  -> mapM_ (putStrLn . showProc) (runSimpleUniqueMonad $ runWithFuel fuel p)
  where
    fuel = 99999



{-- Properties to test:

  1. Is the fixpoint complete (maps all blocks to facts)?
  2. Is the computed fixpoint actually a fixpoint?
  3. Random test generation.

--}
