{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module ConstProp (ConstFact, constLattice, initFact, varHasLit, constProp) where

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
    constFactAdd :: JoinFun (WithTop Lit)
    constFactAdd _ (OldFact old) (NewFact new) = (ch, joined)
      where joined = if new == old then new else Top
            ch = if joined == old then NoChange else SomeChange

-- Initially, we assume that all variable values are unknown.
initFact :: [Var] -> ConstFact
initFact vars = M.fromList $ [(v, Top) | v <- vars]

-- Only interesting semantic choice: values of variables are live across
-- a call site.
-- Note that we don't need a case for x := y, where y holds a constant.
-- We can write the simplest solution and rely on the interleaved optimization.
varHasLit :: FwdTransfer Insn ConstFact
varHasLit = mkFTransfer' v
  where
    v :: Insn e x -> ConstFact -> Fact x ConstFact
    v (Label _)              f = f
    v (Assign x (Lit l))     f = M.insert x (PElem l) f
    v (Assign x _)           f = M.insert x Top f
    v (Store _ _)            f = f
    v (Branch bid)           f = mkFactBase [(bid, f)]
    v (Cond (Var x) tid fid) f = mkFactBase [(tid, tf), (fid, ff)]
      where tf = M.insert x (bool True)  f
            ff = M.insert x (bool False) f
            bool b = PElem (Bool b)
    v (Cond _  tid fid)      f = mkFactBase [(tid, f), (fid, f)]
    v (Call vs _ _ bid)      f = mkFactBase [(bid, foldl toTop f vs)]
      where toTop f v = M.insert v Top f
    v (Return _)             _ = mkFactBase []

-- Constant propagation: rewriting
constProp :: forall m . Monad m => FwdRewrite m Insn ConstFact
constProp = shallowFwdRw' cp 
  where
    cp n f = map_EN (map_EE $ rewriteE f) n >>= Just . insnToA
    rewriteE facts (Var v) = case M.lookup v facts of
                               Just (PElem l) -> Just $ Lit l
                               _              -> Nothing
    rewriteE _ _ = Nothing
