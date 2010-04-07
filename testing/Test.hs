{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module Test (parseTest, evalTest, optTest) where

import Control.Monad.Error

import ConstProp
import Eval  (evalProg, ErrorM)
import Compiler.Hoopl
import IR
import Live
import Parse (parseCode)
import Simplify

parse :: String -> String -> ErrorM (FuelMonad [Proc])
parse file text =
  case parseCode file text of
    Left  err -> throwError $ show err
    Right p   -> return p

parseTest :: String -> IO ()
parseTest file =
  do text <- readFile file
     case parse file text of
       Left err -> putStrLn err
       Right p  -> mapM (putStrLn . showProc) (runWithFuel 0 p) >> return ()

evalTest' :: String -> String -> ErrorM String
evalTest' file text =
  do procs   <- parse file text
     (_, vs) <- testProg (runWithFuel 0 procs)
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

optTest' :: String -> String -> ErrorM (FuelMonad [Proc])
optTest' file text =
  do procs <- parse file text
     return $ procs >>= mapM optProc
  where
    optProc proc@(Proc {entry, body, args}) =
      do { (body', _)  <- analyzeAndRewriteFwd fwd body  (mkFactBase [(entry, initFact args)])
         ; (body'', _) <- analyzeAndRewriteBwd bwd body' (mkFactBase [])
         ; return $ proc { body = body'' } }
    fwd  = FwdPass { fp_lattice = constLattice, fp_transfer = varHasLit,
                     fp_rewrite = constProp `thenFwdRw` simplify }
    bwd  = BwdPass { bp_lattice = liveLattice, bp_transfer = liveness,
                     bp_rewrite = deadAsstElim }

optTest :: String -> IO ()
optTest file =
  do text    <- readFile file
     case optTest' file text of
       Left err -> putStrLn err
       Right p  -> mapM (putStrLn . showProc) (runWithFuel fuel p) >> return ()
  where
    fuel = 99999



{-- Properties to test:

  1. Is the fixpoint complete (maps all blocks to facts)?
  2. Is the computed fixpoint actually a fixpoint?
  3. Random test generation.

--}
