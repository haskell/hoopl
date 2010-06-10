{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module ConstProp (ConstFact, constLattice, initFact, varHasLit, constProp) where

import Control.Monad
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
  , fact_join = stdMapJoin (extendJoinDomain constFactAdd) }
  where
    constFactAdd _ (OldFact old) (NewFact new) 
        = if new == old then (NoChange, PElem new)
          else               (SomeChange, Top)

-- @ end cprop.tex
-- Initially, we assume that all variable values are unknown.
initFact :: [Var] -> ConstFact
initFact vars = Map.fromList $ [(v, Top) | v <- vars]

-- Only interesting semantic choice: values of variables are live across
-- a call site.
-- Note that we don't need a case for x := y, where y holds a constant.
-- We can write the simplest solution and rely on the interleaved optimization.
-- @ start cprop.tex
--------------------------------------------------
-- Analysis: variable equals a literal constant
varHasLit :: FwdTransfer Node ConstFact
varHasLit = mkFTransfer ft
 where
  ft :: Node e x -> ConstFact -> Fact x ConstFact
  ft (Label _)            f = f
  ft (Assign x (Lit v))   f = Map.insert x (PElem v) f
  ft (Assign x _)         f = Map.insert x Top f
  ft (Store _ _)          f = f
  ft (Branch l)           f = mkFactBase [(l, f)]
  ft (Cond (Var x) tl fl) f 
      = mkFactBase [(tl, Map.insert x (b True)  f),
                    (fl, Map.insert x (b False) f)]
          where b = PElem . Bool
  ft (Cond _ tl fl) f = mkFactBase [(tl, f), (fl, f)]

-- @ end cprop.tex
  ft (Call vs _ _ bid)      f = mkFactBase [(bid, foldl toTop f vs)]
      where toTop f v = Map.insert v Top f
  ft (Return _)             _ = mkFactBase []

-- @ start cprop.tex
--------------------------------------------------
-- Rewriting: propagate and fold constants
constProp :: Monad m => FwdRewrite m Node ConstFact
constProp = shallowFwdRw cp
 where
   cp node f
     = return $ liftM nodeToG $ mapVN (lookup f) node
   mapVN      = mapEN . mapEE . mapVE
   lookup f x = case Map.lookup x f of
                  Just (PElem v) -> Just $ Lit v
                  _              -> Nothing
-- @ end cprop.tex
   nodeToG = insnToG
