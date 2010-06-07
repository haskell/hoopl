{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module ConstProp (ConstFact, constLattice, initFact, varHasLit, constProp) where

import qualified Data.Map as M
import qualified Data.Map as Map

import Compiler.Hoopl
import IR
import OptSupport

type Node = Insn -- for paper

-- ConstFact:
--   Not present in map => bottom
--   PElem v => variable has value v
--   Top     => variable's value is not constant
-- @ start cprop.tex
-- Type and definition of the lattice
type ConstFact = Map.Map Var (WithTop Lit)
constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice
  { fact_name = "Const var value"
  , fact_bot  = Map.empty
  , fact_join = stdMapJoin (joinWithTop' constFactAdd) }
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
--------------------------------------------------
-- Analysis: variable equals a literal constant
varHasLit :: FwdTransfer Node ConstFact
varHasLit = mkFTransfer lt
 where
  lt :: Node e x -> ConstFact -> Fact x ConstFact
  lt (Label _)            f = f
  lt (Assign x (Lit v))   f = M.insert x (PElem v) f
  lt (Assign x _)         f = M.insert x Top f
  lt (Store _ _)          f = f
  lt (Branch l)           f = mkFactBase [(l, f)]
  lt (Cond (Var x) tl fl) f 
      = mkFactBase [(tl, Map.insert x (b True)  f),
                    (fl, Map.insert x (b False) f)]
          where b = PElem . Bool
  lt (Cond _ tl fl) f = mkFactBase [(tl, f), (fl, f)]

-- @ end cprop.tex
  lt (Call vs _ _ bid)      f = mkFactBase [(bid, foldl toTop f vs)]
      where toTop f v = M.insert v Top f
  lt (Return _)             _ = mkFactBase []

-- @ start cprop.tex
--------------------------------------------------
-- Rewriting: propagate and fold constants
constProp :: Monad m => FwdRewrite m Node ConstFact
constProp = shallowFwdRw cp
 where
   cp node f
     = return $ fmap insnToG $ mapVN (lookup f) node
   lookup f x
     = case M.lookup x f of
         Just (PElem v) -> Just $ Lit v
         _              -> Nothing
-- @ end cprop.tex
   mapVN = map_VN