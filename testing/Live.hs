{-# OPTIONS_GHC -Wall -fno-warn-incomplete-patterns #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module Live (liveLattice, liveness, deadAsstElim) where

import Data.Maybe
import qualified Data.Set as S

import Compiler.Hoopl
import IR
import OptSupport

type Live = S.Set Var
liveLattice :: DataflowLattice Live
liveLattice = DataflowLattice
  { fact_name       = "Live variables"
  , fact_bot        = S.empty
  , fact_extend     = add
  , fact_do_logging = False
  }
    where add (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `S.union` old
              ch = if S.size j > S.size old then SomeChange else NoChange

liveness :: BwdTransfer Insn Live
liveness n outfact = live outfact n
  where
    live :: Fact x Live -> Insn e x -> Fact e Live
    live f (Assign x _)    = addUses (S.delete x f) n
    live f (Label l)       = mkFactBase [(l, f)]
    live f (Store _ _)     = addUses f n
    live f (Branch l)      = addUses (fact f l) n
    live f (Cond _ tl fl)  = addUses (fact f tl `S.union` fact f fl) n
    live f (Call vs _ _ l) = addUses (fact f l `S.difference` S.fromList vs) n
    live _ (Return _)      = addUses (fact_bot liveLattice) n
    fact f l = fromMaybe S.empty $ lookupFact f l
    addUses = fold_EN (fold_EE addVar)
    addVar s (Var v) = S.insert v s
    addVar s _       = s
     
deadAsstElim :: BwdRewrite Insn Live
deadAsstElim = shallowBwdRw d
  where
    d :: SimpleBwdRewrite Insn Live
    d (Assign x _) live = if x `S.member` live then Nothing else Just emptyAGraph
    d _ _ = Nothing
