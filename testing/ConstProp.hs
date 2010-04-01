{-# OPTIONS_GHC -Wall -fno-warn-incomplete-patterns #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module ConstProp (varHasLit, constProp, ConstFact, constLattice) where

import qualified Data.Map as M

import Hoopl
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

-- Only interesting semantic choice: I'm killing the values of the variables
-- at a call site.
-- Note that we don't need a case for x := y, where y holds a constant.
-- We can write the simplest solution and rely on the interleaved optimization.
varHasLit :: ForwardTransfers Node ConstFact
varHasLit f (Label _)          = f
varHasLit f (Assign x (Lit l)) = M.insert x (Elt l) f
varHasLit f (Assign x _)       = M.insert x Top f
varHasLit f (Store _ _)        = f
varHasLit f (Branch bid)       = [(bid, f)]
varHasLit f (Cond (Var x) tid fid) = [(tid, tf), (fid, ff)]
  where tf = M.insert x (bool True)  f
        ff = M.insert x (bool False) f
        bool b = Elt (Bool b)
varHasLit f (Cond _ tid fid)   = [(tid, f), (fid, f)]
varHasLit _ (Call _ _ _ bid)   = [(bid, fact_bot constLattice)]
varHasLit _ (Return _)         = []

-- Constant propagation: rewriting
constProp :: ForwardRewrites Node ConstFact
constProp facts n = map_EN (map_EE rewriteE) n >>= Just . toAGraph
  where rewriteE (Var v) = case M.lookup v facts of
                             Just (Elt l) -> Just $ Lit l
                             _            -> Nothing
        rewriteE _ = Nothing
