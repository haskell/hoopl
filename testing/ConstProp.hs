{-# OPTIONS_GHC -Wall -fno-warn-incomplete-patterns #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module ConstProp (ConstFact, constLattice, initFact, varHasLit, constProp) where

import Data.Maybe
import qualified Data.Map as M

import Compiler.Hoopl
import IR
import OptSupport

-- ConstFact:
--   Not present in map => bottom
--   Elt v => variable has value v
--   Top   => variable's value is not constant
type ConstFact = M.Map Var (WithTop Lit)

constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice
  { fact_name   = "Const var value"
  , fact_bot    = M.empty
  , fact_extend = stdMapJoin constFactAdd
  , fact_do_logging = False
  }
  where
    constFactAdd :: (WithTop Lit -> WithTop Lit -> (ChangeFlag, WithTop Lit))
    constFactAdd new old = (ch, joined)
      where joined = if new == old then new else Top
            ch = if joined == old then NoChange else SomeChange

-- Initially, we assume that all variable values are unknown.
initFact :: [Var] -> ConstFact
initFact vars = M.fromList $ [(v, Top) | v <- vars]

-- Only interesting semantic choice: I'm killing the values of the variables
-- at a call site.
-- Note that we don't need a case for x := y, where y holds a constant.
-- We can write the simplest solution and rely on the interleaved optimization.
varHasLit :: FwdTransfer Insn ConstFact
varHasLit (Label l)          f = fromMaybe M.empty $ lookupFact f l
varHasLit (Assign x (Lit l)) f = M.insert x (Elt l) f
varHasLit (Assign x _)       f = M.insert x Top f
varHasLit (Store _ _)        f = f
varHasLit (Branch bid)       f = mkFactBase [(bid, f)]
varHasLit (Cond (Var x) tid fid) f = mkFactBase [(tid, tf), (fid, ff)]
  where tf = M.insert x (bool True)  f
        ff = M.insert x (bool False) f
        bool b = Elt (Bool b)
varHasLit (Cond _ tid fid) f = mkFactBase [(tid, f), (fid, f)]
varHasLit (Call _ _ _ bid) _ = mkFactBase [(bid, fact_bot constLattice)]
varHasLit (Return _)       _ = mkFactBase []

-- Constant propagation: rewriting
constProp :: FwdRewrite Insn ConstFact
constProp = shallowFwdRw cp 
  where
    cp n facts = map_EN (map_EE $ rewriteE (getFwdFact n facts M.empty)) n >>= Just . insnToA
    rewriteE facts (Var v) = case M.lookup v facts of
                               Just (Elt l) -> Just $ Lit l
                               _            -> Nothing
    rewriteE _ _ = Nothing
