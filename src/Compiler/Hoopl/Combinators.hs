{-# LANGUAGE RankNTypes, LiberalTypeSynonyms, ScopedTypeVariables #-}

module Compiler.Hoopl.Combinators
  ( SimpleFwdRewrite, SimpleFwdRewrite', noFwdRewrite, thenFwdRw
  , shallowFwdRw, shallowFwdRw', deepFwdRw, deepFwdRw', iterFwdRw
  , SimpleBwdRewrite, SimpleBwdRewrite', noBwdRewrite, thenBwdRw
  , shallowBwdRw, shallowBwdRw', deepBwdRw, deepBwdRw', iterBwdRw
  , productFwd, productBwd
  )

where

import Control.Monad
import Data.Function
import Data.Maybe

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Graph (Graph, C, O)
import Compiler.Hoopl.Label

type FR m n f = FwdRewrite m n f
type BR m n f = BwdRewrite m n f

type SFRW m n f e x = n e x -> f -> m (Maybe (Graph n e x))
type FRW  m n f e x = n e x -> f -> m (FwdRes m n f e x)
type SimpleFwdRewrite  m n f = ExTriple (SFRW m n f)
type ExTriple a = (a C O, a O O, a O C) -- ^ entry/exit triple
type SimpleFwdRewrite' m n f = forall e x . SFRW m n f e x
type LiftFRW m n f e x = SFRW m n f e x -> FRW m n f e x
type MapFRW  m n f e x = FRW  m n f e x -> FRW m n f e x
type MapFRW2 m n f e x = FRW  m n f e x -> FRW m n f e x -> FRW m n f e x

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

wrapSFRewrites :: ExTriple (LiftFRW m n f) -> SimpleFwdRewrite m n f -> FR m n f
wrapSFRewrites lift rw = uncurry3 mkFRewrite $ apply lift rw

wrapFRewrites :: ExTriple (MapFRW m n f) -> FR m n f -> FR m n f
wrapFRewrites map frw = uncurry3 mkFRewrite $ apply map $ getFRewrites frw

wrapFRewrites2 :: ExTriple (MapFRW2 m n f) -> FR m n f -> FR m n f -> FR m n f
wrapFRewrites2 map frw1 frw2 =
  uncurry3 mkFRewrite $ (applyBinary map `on` getFRewrites) frw1 frw2


-- Combinators for higher-rank rewriting functions:
wrapSFRewrites' :: (forall e x . LiftFRW m n f e x) -> SimpleFwdRewrite m n f -> FR m n f
wrapSFRewrites' lift = wrapSFRewrites (lift, lift, lift)

wrapFRewrites' :: (forall e x . MapFRW m n f e x) -> FR m n f -> FR m n f
wrapFRewrites' map = wrapFRewrites (map, map, map)

wrapFRewrites2' :: (forall e x . MapFRW2 m n f e x) -> FR m n f -> FR m n f -> FR m n f
wrapFRewrites2' map = wrapFRewrites2 (map, map, map)

----------------------------------------------------------------

noFwdRewrite :: Monad m => FwdRewrite m n f
noFwdRewrite = mkFRewrite' $ \ _ _ -> return NoFwdRes

shallowFwdRw :: forall m n f . Monad m => SimpleFwdRewrite m n f -> FwdRewrite m n f
shallowFwdRw rw = wrapSFRewrites' lift rw
  where lift rw n f = liftM withoutRewrite (rw n f) 
        withoutRewrite Nothing = NoFwdRes
        withoutRewrite (Just g) = FwdRes g noFwdRewrite

shallowFwdRw' :: Monad m => SimpleFwdRewrite' m n f -> FwdRewrite m n f
shallowFwdRw' f = shallowFwdRw (f, f, f)

deepFwdRw  :: Monad m => SimpleFwdRewrite  m n f -> FwdRewrite m n f
deepFwdRw' :: Monad m => SimpleFwdRewrite' m n f -> FwdRewrite m n f
deepFwdRw  r = iterFwdRw (shallowFwdRw r)
deepFwdRw' f = deepFwdRw (f, f, f)

thenFwdRw :: Monad m => FwdRewrite m n f -> FwdRewrite m n f -> FwdRewrite m n f
thenFwdRw rw1 rw2 = wrapFRewrites2' f rw1 rw2
  where f rw1 rw2' n f = do
          res1 <- rw1 n f
          case res1 of
            NoFwdRes        -> rw2' n f
            (FwdRes g rw1a) -> return $ FwdRes g (rw1a `thenFwdRw` rw2)

iterFwdRw :: Monad m => FwdRewrite m n f -> FwdRewrite m n f
iterFwdRw rw = wrapFRewrites' f rw
  where f rw' n f = liftM iterRewrite (rw' n f)
        iterRewrite NoFwdRes = NoFwdRes
        iterRewrite (FwdRes g rw2) = FwdRes g (rw2 `thenFwdRw` iterFwdRw rw)

----------------------------------------------------------------

type SBRW m n f e x = n e x -> Fact x f -> m (Maybe (Graph n e x))
type BRW  m n f e x = n e x -> Fact x f -> m (BwdRes m n f e x)
type SimpleBwdRewrite  m n f = ExTriple ( SBRW m n f)
type SimpleBwdRewrite' m n f = forall e x . SBRW m n f e x
type LiftBRW m n f e x = SBRW m n f e x -> BRW m n f e x
type MapBRW  m n f e x = BRW  m n f e x -> BRW m n f e x
type MapBRW2 m n f e x = BRW  m n f e x -> BRW m n f e x -> BRW m n f e x

----------------------------------------------------------------

wrapSBRewrites :: ExTriple (LiftBRW m n f) -> SimpleBwdRewrite m n f -> BwdRewrite m n f
wrapSBRewrites lift rw = uncurry3 mkBRewrite $ apply lift rw

wrapBRewrites :: ExTriple (MapBRW m n f) -> BwdRewrite m n f -> BwdRewrite m n f
wrapBRewrites map rw = uncurry3 mkBRewrite $ apply map $ getBRewrites rw

wrapBRewrites2 :: ExTriple (MapBRW2 m n f) -> BR m n f -> BR m n f -> BR m n f
wrapBRewrites2 map rw1 rw2 =
  uncurry3 mkBRewrite $ (applyBinary map `on` getBRewrites) rw1 rw2

-- Combinators for higher-rank rewriting functions:
wrapSBRewrites' :: (forall e x . LiftBRW m n f e x) -> SimpleBwdRewrite m n f -> BR m n f
wrapSBRewrites' lift = wrapSBRewrites (lift, lift, lift)

wrapBRewrites' :: (forall e x . MapBRW m n f e x) -> BwdRewrite m n f -> BwdRewrite m n f
wrapBRewrites' map = wrapBRewrites (map, map, map)

wrapBRewrites2' :: (forall e x . MapBRW2 m n f e x) -> BR m n f -> BR m n f -> BR m n f
wrapBRewrites2' map = wrapBRewrites2 (map, map, map)

----------------------------------------------------------------

noBwdRewrite :: Monad m => BwdRewrite m n f
noBwdRewrite = mkBRewrite' $ \ _ _ -> return NoBwdRes

shallowBwdRw :: Monad m => SimpleBwdRewrite m n f -> BwdRewrite m n f
shallowBwdRw rw = wrapSBRewrites' lift rw
  where lift rw n f = liftM withoutRewrite (rw n f)
        withoutRewrite Nothing = NoBwdRes
        withoutRewrite (Just g) = BwdRes g noBwdRewrite

shallowBwdRw' :: Monad m => SimpleBwdRewrite' m n f -> BwdRewrite m n f
shallowBwdRw' f = shallowBwdRw (f, f, f)

deepBwdRw  :: Monad m => SimpleBwdRewrite  m n f -> BwdRewrite m n f
deepBwdRw' :: Monad m => SimpleBwdRewrite' m n f -> BwdRewrite m n f
deepBwdRw  r = iterBwdRw (shallowBwdRw r)
deepBwdRw' f = deepBwdRw (f, f, f)


thenBwdRw :: Monad m => BwdRewrite m n f -> BwdRewrite m n f -> BwdRewrite m n f
thenBwdRw rw1 rw2 = wrapBRewrites2' f rw1 rw2
  where f rw1 rw2' n f = do
          res1 <- rw1 n f
          case res1 of
            NoBwdRes        -> rw2' n f
            (BwdRes g rw1a) -> return $ BwdRes g (rw1a `thenBwdRw` rw2)

iterBwdRw :: Monad m => BwdRewrite m n f -> BwdRewrite m n f
iterBwdRw rw = wrapBRewrites' f rw
  where f rw' n f = liftM iterRewrite (rw' n f)
        iterRewrite NoBwdRes = NoBwdRes
        iterRewrite (BwdRes g rw2) = BwdRes g (rw2 `thenBwdRw` iterBwdRw rw)

productFwd :: forall m n f f' . Monad m => FwdPass m n f -> FwdPass m n f' -> FwdPass m n (f, f')
productFwd pass1 pass2 = FwdPass lattice transfer rewrite
  where
    lattice = productLattice (fp_lattice pass1) (fp_lattice pass2)
    transfer = mkFTransfer (tf tf1 tf2) (tf tm1 tm2) (tfb tl1 tl2)
      where
        tf  t1 t2 n (f1, f2) = (t1 n f1, t2 n f2)
        tfb t1 t2 n (f1, f2) = mapMapWithKey withfb2 fb1
          where fb1 = t1 n f1
                fb2 = t2 n f2
                withfb2 l f = (f, fromMaybe bot2 $ lookupFact l fb2)
                bot2 = fact_bot (fp_lattice pass2)
        (tf1, tm1, tl1) = getFTransfers (fp_transfer pass1)
        (tf2, tm2, tl2) = getFTransfers (fp_transfer pass2)
    rewrite = liftRW (fp_rewrite pass1) fst `thenFwdRw` liftRW (fp_rewrite pass2) snd
      where
        liftRW rws proj = mkFRewrite (lift f) (lift m) (lift l)
          where lift rw n f = liftM projRewrite $ rw n (proj f)
                projRewrite NoFwdRes = NoFwdRes
                projRewrite (FwdRes g rws') = FwdRes g $ liftRW rws' proj
                (f, m, l) = getFRewrites rws

productBwd :: forall m n f f' . Monad m => BwdPass m n f -> BwdPass m n f' -> BwdPass m n (f, f')
productBwd pass1 pass2 = BwdPass lattice transfer rewrite
  where
    lattice = productLattice (bp_lattice pass1) (bp_lattice pass2)
    transfer = mkBTransfer (tf tf1 tf2) (tf tm1 tm2) (tfb tl1 tl2)
      where
        tf  t1 t2 n (f1, f2) = (t1 n f1, t2 n f2)
        tfb t1 t2 n fb = (t1 n $ mapMap fst fb, t2 n $ mapMap snd fb)
        (tf1, tm1, tl1) = getBTransfers (bp_transfer pass1)
        (tf2, tm2, tl2) = getBTransfers (bp_transfer pass2)
    rewrite = liftRW (bp_rewrite pass1) fst `thenBwdRw` liftRW (bp_rewrite pass2) snd
      where
        liftRW :: forall f1 . BwdRewrite m n f1 -> ((f, f') -> f1) -> BwdRewrite m n (f, f')
        liftRW rws proj = mkBRewrite (lift proj f) (lift proj m) (lift (mapMap proj) l)
          where lift proj' rw n f = liftM projRewrite $ rw n (proj' f)
                projRewrite NoBwdRes = NoBwdRes
                projRewrite (BwdRes g rws') = BwdRes g $ liftRW rws' proj
                (f, m, l) = getBRewrites rws

productLattice :: forall f f' . DataflowLattice f -> DataflowLattice f' -> DataflowLattice (f, f')
productLattice l1 l2 =
  DataflowLattice
    { fact_name       = fact_name l1 ++ " x " ++ fact_name l2
    , fact_bot        = (fact_bot l1, fact_bot l2)
    , fact_extend     = extend'
    , fact_do_logging = fact_do_logging l1 || fact_do_logging l2
    }
  where
    extend' lbl (OldFact (o1, o2)) (NewFact (n1, n2)) = (c', (f1, f2))
      where (c1, f1) = fact_extend l1 lbl (OldFact o1) (NewFact n1)
            (c2, f2) = fact_extend l2 lbl (OldFact o2) (NewFact n2)
            c' = case (c1, c2) of
                   (NoChange, NoChange) -> NoChange
                   _                    -> SomeChange
