{-# LANGUAGE RankNTypes, LiberalTypeSynonyms #-}

module Compiler.Hoopl.Combinators
  ( SimpleFwdRewrite, noFwdRewrite, thenFwdRw
  , shallowFwdRw, shallowFwdRw', deepFwdRw, deepFwdRw', iterFwdRw
  , SimpleBwdRewrite, noBwdRewrite, thenBwdRw
  , shallowBwdRw, shallowBwdRw', deepBwdRw, deepBwdRw', iterBwdRw
  )

where

import Data.Function

import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Graph (C, O)
import Compiler.Hoopl.MkGraph

type FR n f = FwdRewrite n f
type BR n f = BwdRewrite n f

type SFRW n f e x = n e x -> f -> Maybe (AGraph n e x)
type FRW  n f e x = n e x -> f -> Maybe (FwdRes n f e x)
type SimpleFwdRewrite  n f = ExTriple (SFRW n f)
type ExTriple a = (a C O, a O O, a O C) -- ^ entry/exit triple
type SimpleFwdRewrite' n f = forall e x . SFRW n f e x
type LiftFRW n f e x = SFRW n f e x -> FRW n f e x
type MapFRW  n f e x = FRW  n f e x -> FRW n f e x
type MapFRW2 n f e x = FRW  n f e x -> FRW n f e x -> FRW n f e x

----------------------------------------------------------------



type Bogus a = (forall e x . a e x) -> ExTriple a


scalar :: forall a . Bogus a
-- scalar :: forall a . (forall e x . a e x) -> ExTriple a
scalar a = (a, a, a)

wrapSFRewrites :: ExTriple (LiftFRW n f) -> SimpleFwdRewrite n f -> FR n f
wrapSFRewrites (liftF, liftM, liftL) (rwF, rwM, rwL) =
  mkFRewrite (liftF rwF) (liftM rwM) (liftL rwL)

wrapSFRewrites' :: (forall e x . LiftFRW n f e x) -> SimpleFwdRewrite n f -> FR n f
wrapSFRewrites' lift = wrapSFRewrites (lift, lift, lift)

wrapFRewrites :: ExTriple (MapFRW n f) -> FR n f -> FR n f
wrapFRewrites (mapF, mapM, mapL) frw = mkFRewrite (mapF f) (mapM m) (mapL l)
  where (f, m, l) = getFRewrites frw
wrapFRewrites' :: (forall e x . MapFRW n f e x) -> FR n f -> FR n f
-- wrapFRewrites' map = wrapFRewrites $ (scalar::Bogus (MapFRW n f)) map --  (map, map, map)
wrapFRewrites' map = wrapFRewrites (map, map, map)

wrapFRewrites2 :: ExTriple (MapFRW2 n f) -> FR n f -> FR n f -> FR n f
wrapFRewrites2 (mapF, mapM, mapL) frw1 frw2 =
  mkFRewrite (mapF f1 f2) (mapM m1 m2) (mapL l1 l2)
    where (f1, m1, l1) = getFRewrites frw1
          (f2, m2, l2) = getFRewrites frw2

wrapSFRewritesalso :: ExTriple (LiftFRW n f) -> SimpleFwdRewrite n f -> FR n f
wrapSFRewritesalso lift rw = uncurry3 mkFRewrite $ apply lift rw

wrapFRewritesalso :: ExTriple (MapFRW n f) -> FR n f -> FR n f
wrapFRewritesalso maps frw = uncurry3 mkFRewrite $ apply maps $ getFRewrites frw

wrapFRewrites2also :: ExTriple (MapFRW2 n f) -> FR n f -> FR n f -> FR n f
wrapFRewrites2also maps frw1 frw2 =
  uncurry3 mkFRewrite $ (applyBinary maps `on` getFRewrites) frw1 frw2

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

applyBinary :: (a -> b -> c, d -> e -> f, g -> h -> i)
            -> (a, d, g) -> (b, e, h) -> (c, f, i)
applyBinary (f1, f2, f3) (x1, x2, x3) (y1, y2, y3) = (f1 x1 y1, f2 x2 y2, f3 x3 y3)

apply :: (a -> b, d -> e, g -> h)
            -> (a, d, g) -> (b, e, h)
apply (f1, f2, f3) (x1, x2, x3) = (f1 x1, f2 x2, f3 x3)


wrapFRewrites2' :: (forall e x . MapFRW2 n f e x) -> FR n f -> FR n f -> FR n f
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

wrapSBRewrites :: ExTriple (LiftBRW n f) -> SimpleBwdRewrite n f -> BwdRewrite n f
wrapSBRewrites (liftF, liftM, liftL) (rwF, rwM, rwL) =
  mkBRewrite (liftF rwF) (liftM rwM) (liftL rwL)

wrapSBRewrites' :: (forall e x . LiftBRW n f e x) -> SimpleBwdRewrite n f -> BR n f
wrapSBRewrites' lift = wrapSBRewrites (lift, lift, lift)

wrapBRewrites :: ExTriple (MapBRW n f) -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites (mapF, mapM, mapL) brw = mkBRewrite (mapF f) (mapM m) (mapL l)
  where (f, m, l) = getBRewrites brw
wrapBRewrites' :: (forall e x . MapBRW n f e x) -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites' map = wrapBRewrites (map, map, map)

wrapBRewrites2 :: ExTriple (MapBRW2 n f) -> BR n f -> BR n f -> BR n f
wrapBRewrites2 (mapF, mapM, mapL) brw1 brw2 = mkBRewrite (mapF f1 f2) (mapM m1 m2) (mapL l1 l2)
  where (f1, m1, l1) = getBRewrites brw1
        (f2, m2, l2) = getBRewrites brw2
wrapBRewrites2' :: (forall e x . MapBRW2 n f e x) -> BR n f -> BR n f -> BR n f
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
