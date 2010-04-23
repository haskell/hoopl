{-# LANGUAGE RankNTypes #-}

module Compiler.Hoopl.Combinators
  ( SimpleFwdRewrite, noFwdRewrite, thenFwdRw
  , shallowFwdRw, shallowFwdRw', deepFwdRw, deepFwdRw', iterFwdRw
  , SimpleBwdRewrite, noBwdRewrite, thenBwdRw
  , shallowBwdRw, shallowBwdRw', deepBwdRw, deepBwdRw', iterBwdRw
  )

where

import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Graph (C, O)
import Compiler.Hoopl.MkGraph

type SFRW n f e x = n e x -> f -> Maybe (AGraph n e x)
type FRW  n f e x = n e x -> f -> Maybe (FwdRes n f e x)
type SimpleFwdRewrite  n f = ( SFRW n f C O , SFRW n f O O , SFRW n f O C )
type SimpleFwdRewrite' n f = forall e x . SFRW n f e x
type LiftFRW n f e x = SFRW n f e x -> FRW n f e x
type MapFRW  n f e x = FRW  n f e x -> FRW n f e x
type MapFRW2 n f e x = FRW  n f e x -> FRW n f e x -> FRW n f e x

----------------------------------------------------------------

wrapSFRewrites :: (LiftFRW n f C O, LiftFRW n f O O, LiftFRW n f O C) -> SimpleFwdRewrite n f -> FwdRewrite n f
wrapSFRewrites (liftF, liftM, liftL) (rwF, rwM, rwL) =
  mkFRewrite (liftF rwF) (liftM rwM) (liftL rwL)

wrapSFRewrites' :: (forall e x . LiftFRW n f e x) -> SimpleFwdRewrite n f -> FwdRewrite n f
wrapSFRewrites' lift = wrapSFRewrites (lift, lift, lift)

wrapFRewrites :: (MapFRW n f C O, MapFRW n f O O, MapFRW n f O C) -> FwdRewrite n f -> FwdRewrite n f
wrapFRewrites (mapF, mapM, mapL) frw = mkFRewrite (mapF f) (mapM m) (mapL l)
  where (f, m, l) = getFRewrites frw
wrapFRewrites' :: (forall e x . MapFRW n f e x) -> FwdRewrite n f -> FwdRewrite n f
wrapFRewrites' map = wrapFRewrites (map, map, map)

wrapFRewrites2 :: (MapFRW2 n f C O, MapFRW2 n f O O, MapFRW2 n f O C) -> FwdRewrite n f -> FwdRewrite n f -> FwdRewrite n f
wrapFRewrites2 (mapF, mapM, mapL) frw1 frw2 = mkFRewrite (mapF f1 f2) (mapM m1 m2) (mapL l1 l2)
  where (f1, m1, l1) = getFRewrites frw1
        (f2, m2, l2) = getFRewrites frw2
wrapFRewrites2' :: (forall e x . MapFRW2 n f e x) -> FwdRewrite n f -> FwdRewrite n f -> FwdRewrite n f
wrapFRewrites2' map = wrapFRewrites2 (map, map, map)

----------------------------------------------------------------

noFwdRewrite :: FwdRewrite n f
noFwdRewrite = mkFRewrite' $ \ _ _ -> Nothing

shallowFwdRw :: forall n f . SimpleFwdRewrite n f -> FwdRewrite n f
shallowFwdRw rw = wrapSFRewrites' f rw
  where f rw n f = case (rw n f) of
                     Nothing -> Nothing
                     Just ag -> Just (FwdRes ag noFwdRewrite)
shallowFwdRw' :: SimpleFwdRewrite' n f -> FwdRewrite n f
shallowFwdRw' f = shallowFwdRw (f, f, f)

deepFwdRw :: SimpleFwdRewrite n f -> FwdRewrite n f
deepFwdRw r = iterFwdRw (shallowFwdRw r)
deepFwdRw' :: SimpleFwdRewrite' n f -> FwdRewrite n f
deepFwdRw' f = deepFwdRw (f, f, f)

thenFwdRw :: FwdRewrite n f -> FwdRewrite n f -> FwdRewrite n f
thenFwdRw rw1 rw2 = wrapFRewrites2' f rw1 rw2
  where f rw1 rw2' n f =
          case rw1 n f of
            Nothing               -> rw2' n f
            Just (FwdRes ag rw1a) -> Just (FwdRes ag (rw1a `thenFwdRw` rw2))

iterFwdRw :: FwdRewrite n f -> FwdRewrite n f
iterFwdRw rw = wrapFRewrites' f rw
  where f rw' n f =
          case rw' n f of
            Just (FwdRes g rw2) -> Just $ FwdRes g (rw2 `thenFwdRw` iterFwdRw rw)
            Nothing             -> Nothing

----------------------------------------------------------------

type SBRW n f e x = n e x -> Fact x f -> Maybe (AGraph n e x)
type BRW  n f e x = n e x -> Fact x f -> Maybe (BwdRes n f e x)
type SimpleBwdRewrite  n f = ( SBRW n f C O , SBRW n f O O , SBRW n f O C )
type SimpleBwdRewrite' n f = forall e x . SBRW n f e x
type LiftBRW n f e x = SBRW n f e x -> BRW n f e x
type MapBRW  n f e x = BRW  n f e x -> BRW n f e x
type MapBRW2 n f e x = BRW  n f e x -> BRW n f e x -> BRW n f e x

----------------------------------------------------------------

wrapSBRewrites :: (LiftBRW n f C O, LiftBRW n f O O, LiftBRW n f O C) -> SimpleBwdRewrite n f -> BwdRewrite n f
wrapSBRewrites (liftF, liftM, liftL) (rwF, rwM, rwL) =
  mkBRewrite (liftF rwF) (liftM rwM) (liftL rwL)

wrapSBRewrites' :: (forall e x . LiftBRW n f e x) -> SimpleBwdRewrite n f -> BwdRewrite n f
wrapSBRewrites' lift = wrapSBRewrites (lift, lift, lift)

wrapBRewrites :: (MapBRW n f C O, MapBRW n f O O, MapBRW n f O C) -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites (mapF, mapM, mapL) brw = mkBRewrite (mapF f) (mapM m) (mapL l)
  where (f, m, l) = getBRewrites brw
wrapBRewrites' :: (forall e x . MapBRW n f e x) -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites' map = wrapBRewrites (map, map, map)

wrapBRewrites2 :: (MapBRW2 n f C O, MapBRW2 n f O O, MapBRW2 n f O C) -> BwdRewrite n f -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites2 (mapF, mapM, mapL) brw1 brw2 = mkBRewrite (mapF f1 f2) (mapM m1 m2) (mapL l1 l2)
  where (f1, m1, l1) = getBRewrites brw1
        (f2, m2, l2) = getBRewrites brw2
wrapBRewrites2' :: (forall e x . MapBRW2 n f e x) -> BwdRewrite n f -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites2' map = wrapBRewrites2 (map, map, map)

----------------------------------------------------------------

noBwdRewrite :: BwdRewrite n f
noBwdRewrite = mkBRewrite' $ \ _ _ -> Nothing

shallowBwdRw :: SimpleBwdRewrite n f -> BwdRewrite n f
shallowBwdRw rw = wrapSBRewrites' f rw
  where f rw n f = case (rw n f) of
                     Nothing -> Nothing
                     Just ag -> Just (BwdRes ag noBwdRewrite)
shallowBwdRw' :: SimpleBwdRewrite' n f -> BwdRewrite n f
shallowBwdRw' f = shallowBwdRw (f, f, f)

deepBwdRw :: SimpleBwdRewrite n f -> BwdRewrite n f
deepBwdRw r = iterBwdRw (shallowBwdRw r)
deepBwdRw' :: SimpleBwdRewrite' n f -> BwdRewrite n f
deepBwdRw' f = deepBwdRw (f, f, f)


thenBwdRw :: BwdRewrite n f -> BwdRewrite n f -> BwdRewrite n f
thenBwdRw rw1 rw2 = wrapBRewrites2' f rw1 rw2
  where f rw1 rw2' n f =
          case rw1 n f of
            Nothing               -> rw2' n f
            Just (BwdRes ag rw1a) -> Just (BwdRes ag (rw1a `thenBwdRw` rw2))

iterBwdRw :: BwdRewrite n f -> BwdRewrite n f
iterBwdRw rw = wrapBRewrites' f rw
  where f rw' n f =
          case rw' n f of
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
