{-# OPTIONS_GHC -Wall -fno-warn-incomplete-patterns #-}
{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module Live (liveLattice, liveness, deadAsstElim) where

import qualified Data.Set as S

import Hoopl
import IR
import OptSupport

type Live = S.Set Var
liveLattice :: DataflowLattice Live
liveLattice = DataflowLattice
  { fact_name   = "Live variables"
  , fact_bot    = S.empty
  , fact_extend = add
  , fact_do_logging = False
  }
    where add new old = (ch, j)
            where
              j = new `S.union` old
              ch = if S.size j > S.size old then SomeChange else NoChange

liveness :: BackwardTransfers Node Live
liveness outfact n = add_uses (l outfact n) n
  where
    l :: TailFactB x Live -> Node e x -> Live
    l f (Assign x _)      = S.delete x f
    l f (Label _)         = f
    l f (Store _ _)       = f
    l f (Branch bid)      = fact f bid
    l f (Cond _ tid fid)  = fact f tid `S.union` fact f fid
    l f (Call vs _ _ bid) = fact f bid `S.difference` S.fromList vs
    l _ (Return _)        = fact_bot liveLattice
    fact = lookupFact liveLattice
    add_uses = fold_EN (fold_EE add_var)
    add_var s (Var v) = S.insert v s
    add_var s _       = s
     
deadAsstElim :: BackwardRewrites Node Live
deadAsstElim live (Assign x _) =
  if x `S.member` live then Nothing else Just (return GNil)
deadAsstElim _ _ = Nothing
