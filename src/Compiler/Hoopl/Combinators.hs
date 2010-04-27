{-# LANGUAGE RankNTypes, LiberalTypeSynonyms #-}

module Compiler.Hoopl.Combinators
  ( SimpleFwdRewrite, noFwdRewrite, thenFwdRw
  , shallowFwdRw, shallowFwdRw', deepFwdRw, deepFwdRw', iterFwdRw
  , SimpleBwdRewrite, noBwdRewrite, thenBwdRw
  , shallowBwdRw, shallowBwdRw', deepBwdRw, deepBwdRw', iterBwdRw
  , noRewritePoly
  )

where

import Data.Function

import Compiler.Hoopl.DataflowNest
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
-- common operations on triples

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

apply :: (a -> b, d -> e, g -> h) -> (a, d, g) -> (b, e, h)
apply (f1, f2, f3) (x1, x2, x3) = (f1 x1, f2 x2, f3 x3)

applyBinary :: (a -> b -> c, d -> e -> f, g -> h -> i)
            -> (a, d, g) -> (b, e, h) -> (c, f, i)
applyBinary (f1, f2, f3) (x1, x2, x3) (y1, y2, y3) = (f1 x1 y1, f2 x2 y2, f3 x3 y3)


----------------------------------------------------------------

wrapSFRewrites :: ExTriple (LiftFRW n f) -> SimpleFwdRewrite n f -> FR n f
wrapSFRewrites lift rw = uncurry3 mkFRewrite $ apply lift rw

wrapFRewrites :: ExTriple (MapFRW n f) -> FR n f -> FR n f
wrapFRewrites map frw = uncurry3 mkFRewrite $ apply map $ getFRewrites frw

wrapFRewrites2 :: ExTriple (MapFRW2 n f) -> FR n f -> FR n f -> FR n f
wrapFRewrites2 map frw1 frw2 =
  uncurry3 mkFRewrite $ (applyBinary map `on` getFRewrites) frw1 frw2


-- Combinators for higher-rank rewriting functions:
wrapSFRewrites' :: (forall e x . LiftFRW n f e x) -> SimpleFwdRewrite n f -> FR n f
wrapSFRewrites' lift = wrapSFRewrites (lift, lift, lift)

wrapFRewrites' :: (forall e x . MapFRW n f e x) -> FR n f -> FR n f
wrapFRewrites' map = wrapFRewrites (map, map, map)

wrapFRewrites2' :: (forall e x . MapFRW2 n f e x) -> FR n f -> FR n f -> FR n f
wrapFRewrites2' map = wrapFRewrites2 (map, map, map)

----------------------------------------------------------------

noFwdRewrite :: FwdRewrite n f
noFwdRewrite = mkFRewrite' noRewritePoly

noRewritePoly :: a -> b -> Maybe c
noRewritePoly _ _ = Nothing

shallowFwdRw :: forall n f . SimpleFwdRewrite n f -> FwdRewrite n f
shallowFwdRw rw = wrapSFRewrites' lift rw
  where lift rw n f = fmap withoutRewrite (rw n f) 
        withoutRewrite ag = FwdRes ag noFwdRewrite

shallowFwdRw' :: SimpleFwdRewrite' n f -> FwdRewrite n f
shallowFwdRw' f = shallowFwdRw (f, f, f)

deepFwdRw  :: SimpleFwdRewrite  n f -> FwdRewrite n f
deepFwdRw' :: SimpleFwdRewrite' n f -> FwdRewrite n f
deepFwdRw  r = iterFwdRw (shallowFwdRw r)
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
type SimpleBwdRewrite  n f = ExTriple ( SBRW n f)
type SimpleBwdRewrite' n f = forall e x . SBRW n f e x
type LiftBRW n f e x = SBRW n f e x -> BRW n f e x
type MapBRW  n f e x = BRW  n f e x -> BRW n f e x
type MapBRW2 n f e x = BRW  n f e x -> BRW n f e x -> BRW n f e x

----------------------------------------------------------------

wrapSBRewrites :: ExTriple (LiftBRW n f) -> SimpleBwdRewrite n f -> BwdRewrite n f
wrapSBRewrites lift rw = uncurry3 mkBRewrite $ apply lift rw

wrapBRewrites :: ExTriple (MapBRW n f) -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites map rw = uncurry3 mkBRewrite $ apply map $ getBRewrites rw

wrapBRewrites2 :: ExTriple (MapBRW2 n f) -> BR n f -> BR n f -> BR n f
wrapBRewrites2 map rw1 rw2 =
  uncurry3 mkBRewrite $ (applyBinary map `on` getBRewrites) rw1 rw2

-- Combinators for higher-rank rewriting functions:
wrapSBRewrites' :: (forall e x . LiftBRW n f e x) -> SimpleBwdRewrite n f -> BR n f
wrapSBRewrites' lift = wrapSBRewrites (lift, lift, lift)

wrapBRewrites' :: (forall e x . MapBRW n f e x) -> BwdRewrite n f -> BwdRewrite n f
wrapBRewrites' map = wrapBRewrites (map, map, map)

wrapBRewrites2' :: (forall e x . MapBRW2 n f e x) -> BR n f -> BR n f -> BR n f
wrapBRewrites2' map = wrapBRewrites2 (map, map, map)

----------------------------------------------------------------

noBwdRewrite :: BwdRewrite n f
noBwdRewrite = mkBRewrite' $ \ _ _ -> Nothing

shallowBwdRw :: SimpleBwdRewrite n f -> BwdRewrite n f
shallowBwdRw rw = wrapSBRewrites' lift rw
  where lift rw n f = fmap withoutRewrite (rw n f)
        withoutRewrite ag = BwdRes ag noBwdRewrite

shallowBwdRw' :: SimpleBwdRewrite' n f -> BwdRewrite n f
shallowBwdRw' f = shallowBwdRw (f, f, f)

deepBwdRw  :: SimpleBwdRewrite  n f -> BwdRewrite n f
deepBwdRw' :: SimpleBwdRewrite' n f -> BwdRewrite n f
deepBwdRw  r = iterBwdRw (shallowBwdRw r)
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

-- Note: The transfer is assymetric if the passes return facts for
-- different sets of successors...
{-
productFwd :: FwdPass n f -> FwdPass n f' -> FwdPass n (f, f')
productFwd pass1 pass2 = FwdPass lattice transfer rewrite
    where -- can't tell if I have a FactBase of pairs or a pair of facts
          lattice  = undefined
          transfer = mkFTransfer (tf tf1 tf2) (tf tm1 tm2) (tfb tl1 tl2)
            where
              tf  t1 t2 n (f1, f2) = (t1 n f1, t2 n f2)
              tfb t1 t2 n (f1, f2) = mapWithLFactBase withfb2 fb1
                where fb1 = t1 n f1
                      fb2 = t2 n f2
                      withfb2 l f = (f, fromMaybe bot2 $ lookupFact fb2 l)
                      bot2 = fact_bot (fp_lattice pass2)
              (tf1, tm1, tl1) = getFTransfers (fp_transfer pass1)
              (tf2, tm2, tl2) = getFTransfers (fp_transfer pass2)
          rewrite = undefined
-}
