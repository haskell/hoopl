{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module ConstProp (ConstFact, constLattice, initFact, varHasLit, constProp) where

import qualified Data.Map as M
import qualified Data.Map as Map

import Compiler.Hoopl
import IR
import OptSupport

-- ConstFact:
--   Not present in map => bottom
--   PElem v => variable has value v
--   Top     => variable's value is not constant
-- @ start cprop.tex
-- Type and definition of the lattice
type ConstFact = Map.Map Var (WithTop Lit)
constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice
  { fact_name   = "Const var value"
  , fact_bot    = Map.empty
  , fact_extend = stdMapJoin (joinWithTop' constFactAdd)
  , fact_do_logging = False
  }
  where
    constFactAdd _ (OldFact old) (NewFact new) 
        = (changeIf (new /= old), joined)
      where joined = if new == old then PElem new else Top

-- @ end cprop.tex
-- Initially, we assume that all variable values are unknown.
initFact :: [Var] -> ConstFact
initFact vars = M.fromList $ [(v, Top) | v <- vars]

-- Only interesting semantic choice: values of variables are live across
-- a call site.
-- Note that we don't need a case for x := y, where y holds a constant.
-- We can write the simplest solution and rely on the interleaved optimization.
-- @ start cprop.tex
----------------------------------------------------------------
-- Analysis: variable equals a literal constant
varHasLit :: FwdTransfer Insn ConstFact
varHasLit = mkFTransfer' v
  where
    v :: Insn e x -> ConstFact -> Fact x ConstFact
    v (Label _)              f = f
    v (Assign x (Lit l))     f = M.insert x (PElem l) f
    v (Assign x _)           f = M.insert x Top f
    v (Store _ _)            f = f
    v (Branch bid)           f = mkFactBase [(bid, f)]
    v (Cond (Var x) tid fid) f 
      = mkFactBase [(tid, Map.insert x (b True)  f),
                    (fid, Map.insert x (b False) f)]
          where b = PElem . Bool
    v (Cond _  tid fid)      f 
      = mkFactBase [(tid, f), (fid, f)]

-- @ end cprop.tex
    v (Call vs _ _ bid)      f = mkFactBase [(bid, foldl toTop f vs)]
      where toTop f v = M.insert v Top f
    v (Return _)             _ = mkFactBase []

-- @ start cprop.tex
----------------------------------------------------------------
-- Rewriting: propagate and fold constants
constProp :: Monad m => FwdRewrite m Insn ConstFact
constProp = shallowFwdRwPoly cp
  where
    cp node facts = return $ fmap insnToG $ (map_EN . map_EE . map_VE) lookup node
      where lookup v = case M.lookup v facts of
                               Just (PElem l) -> Just $ Lit l
                               _              -> Nothing
