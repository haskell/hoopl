{-# LANGUAGE RankNTypes #-}

module Compiler.Hoopl.Combinators
  ( SimpleFwdRewrite, noFwdRewrite, thenFwdRw, shallowFwdRw, deepFwdRw, iterFwdRw
  , SimpleBwdRewrite, noBwdRewrite, thenBwdRw, shallowBwdRw, deepBwdRw, iterBwdRw
  )

where

import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.MkGraph

type SimpleFwdRewrite n f 
  = forall e x. n e x -> Fact e f
             -> Maybe (AGraph n e x)

noFwdRewrite :: FwdRewrite n f
noFwdRewrite _ _ = Nothing

shallowFwdRw :: SimpleFwdRewrite n f -> FwdRewrite n f
shallowFwdRw rw n f = case (rw n f) of
                         Nothing -> Nothing
                         Just ag -> Just (FwdRes ag noFwdRewrite)

deepFwdRw :: SimpleFwdRewrite n f -> FwdRewrite n f
deepFwdRw r = iterFwdRw (shallowFwdRw r)

thenFwdRw :: FwdRewrite n f -> FwdRewrite n f -> FwdRewrite n f
thenFwdRw rw1 rw2 n f
  = case rw1 n f of
      Nothing               -> rw2 n f
      Just (FwdRes ag rw1a) -> Just (FwdRes ag (rw1a `thenFwdRw` rw2))

iterFwdRw :: FwdRewrite n f -> FwdRewrite n f
iterFwdRw rw =
  \ n f -> case rw n f of
             Just (FwdRes g rw2) -> Just $ FwdRes g (rw2 `thenFwdRw` iterFwdRw rw)
             Nothing             -> Nothing

----------------------------------------------------------------

type SimpleBwdRewrite n f 
  = forall e x. n e x -> Fact x f
             -> Maybe (AGraph n e x)

noBwdRewrite :: BwdRewrite n f
noBwdRewrite _ _ = Nothing

shallowBwdRw :: SimpleBwdRewrite n f -> BwdRewrite n f
shallowBwdRw rw n f = case (rw n f) of
                         Nothing -> Nothing
                         Just ag -> Just (BwdRes ag noBwdRewrite)

deepBwdRw :: SimpleBwdRewrite n f -> BwdRewrite n f
deepBwdRw r = iterBwdRw (shallowBwdRw r)


thenBwdRw :: BwdRewrite n f -> BwdRewrite n f -> BwdRewrite n f
thenBwdRw rw1 rw2 n f
  = case rw1 n f of
      Nothing               -> rw2 n f
      Just (BwdRes ag rw1a) -> Just (BwdRes ag (rw1a `thenBwdRw` rw2))

iterBwdRw :: BwdRewrite n f -> BwdRewrite n f
iterBwdRw rw =
  \ n f -> case rw n f of
             Just (BwdRes g rw2) -> Just $ BwdRes g (rw2 `thenBwdRw` iterBwdRw rw)
             Nothing             -> Nothing

{-
productFwd :: FwdPass n f -> FwdPass n f' -> FwdPass n (f, f')
productFwd pass pass' = FwdPass lattice transfer rewrite
    where -- can't tell if I have a FactBase of pairs or a pair of facts
          transfer n fb = (fp_transfer pass  $ factBaseMap fst fb,
                           fp_transfer pass' $ factBaseMap snd fb)
          transfer n (f, f') = (fp_transfer pass f, fp_transfer pass' f')
             ...              

-}
