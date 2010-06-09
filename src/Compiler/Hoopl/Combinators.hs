{-# LANGUAGE RankNTypes, LiberalTypeSynonyms, ScopedTypeVariables #-}

module Compiler.Hoopl.Combinators
  ( SimpleFwdRewrite, SimpleFwdRewrite3, noFwdRewrite, thenFwdRw
  , shallowFwdRw3, shallowFwdRw, deepFwdRw3, deepFwdRw, iterFwdRw
  , SimpleBwdRewrite, SimpleBwdRewrite3, noBwdRewrite, thenBwdRw
  , shallowBwdRw3, shallowBwdRw, deepBwdRw3, deepBwdRw, iterBwdRw
  , pairFwd, pairBwd, pairLattice
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

type FwdRes m n f e x = Maybe (FwdRew m n f e x)

type SFRW m n f e x = n e x -> f -> m (Maybe (Graph n e x))
type FRW  m n f e x = n e x -> f -> m (FwdRes m n f e x)
type SimpleFwdRewrite3 m n f = ExTriple (SFRW m n f)
type ExTriple a = (a C O, a O O, a O C) -- ^ entry/exit triple
type SimpleFwdRewrite m n f = forall e x . SFRW m n f e x
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

wrapSFRewrite3 :: ExTriple (LiftFRW m n f) -> SimpleFwdRewrite3 m n f -> FR m n f
wrapSFRewrite3 lift rw = uncurry3 mkFRewrite3 $ apply lift rw

wrapFRewrite3 :: ExTriple (MapFRW m n f) -> FR m n f -> FR m n f
wrapFRewrite3 map frw = uncurry3 mkFRewrite3 $ apply map $ getFRewrite3 frw

wrapFRewrites23 :: ExTriple (MapFRW2 m n f) -> FR m n f -> FR m n f -> FR m n f
wrapFRewrites23 map frw1 frw2 =
  uncurry3 mkFRewrite3 $ (applyBinary map `on` getFRewrite3) frw1 frw2


-- Combinators for higher-rank rewriting functions:
wrapSFRewrites' :: (forall e x . LiftFRW m n f e x) -> SimpleFwdRewrite3 m n f -> FR m n f
wrapSFRewrites' lift = wrapSFRewrite3 (lift, lift, lift)

wrapFRewrites :: (forall e x . MapFRW m n f e x) -> FR m n f -> FR m n f
wrapFRewrites map = wrapFRewrite3 (map, map, map)
-- It's ugly that we can't use
--    wrapFRewrites' = mkFRewrite'
-- Would be nice to refactor here XXX  ---NR


wrapFRewrites2 :: (forall e x . MapFRW2 m n f e x) -> FR m n f -> FR m n f -> FR m n f
wrapFRewrites2 map = wrapFRewrites23 (map, map, map)

----------------------------------------------------------------


shallowFwdRw3 :: forall m n f . Monad m => SimpleFwdRewrite3 m n f -> FwdRewrite m n f
shallowFwdRw3 rw = wrapSFRewrites' lift rw
  where lift rw n f = liftM (fmap (flip FwdRew noFwdRewrite)) (rw n f) 

shallowFwdRw :: Monad m => SimpleFwdRewrite m n f -> FwdRewrite m n f
shallowFwdRw f = shallowFwdRw3 (f, f, f)

deepFwdRw3    :: Monad m => SimpleFwdRewrite3 m n f -> FwdRewrite m n f
deepFwdRw :: Monad m => SimpleFwdRewrite m n f -> FwdRewrite m n f
deepFwdRw3    r = iterFwdRw (shallowFwdRw3 r)
deepFwdRw f = deepFwdRw3 (f, f, f)

-- N.B. rw3, rw3', and rw3a are triples of functions.
-- But rw and rw' are single functions.
-- @ start comb1.tex
thenFwdRw :: Monad m 
          => FwdRewrite m n f 
          -> FwdRewrite m n f 
          -> FwdRewrite m n f
thenFwdRw rw3 rw3' = wrapFRewrites2 thenrw rw3 rw3'
 where
  thenrw rw rw' n f = rw n f >>= fwdRes
     where fwdRes Nothing = rw' n f
           fwdRes (Just (FwdRew g rw3a))
            = return $ Just $ FwdRew g (rw3a `thenFwdRw` rw3')

noFwdRewrite :: Monad m => FwdRewrite m n f
noFwdRewrite = mkFRewrite $ \ _ _ -> return Nothing
-- @ end comb1.tex

-- @ start iterf.tex
iterFwdRw :: Monad m 
          => FwdRewrite m n f 
          -> FwdRewrite m n f
iterFwdRw rw3 = wrapFRewrites iter rw3
 where
    iter rw n f = liftM (liftM fwdRes) (rw n f)
    fwdRes (FwdRew g rw3a) = 
      FwdRew g (rw3a `thenFwdRw` iterFwdRw rw3)
-- @ end iterf.tex

----------------------------------------------------------------
type BwdRes m n f e x = Maybe (BwdRew m n f e x)

type SBRW m n f e x = n e x -> Fact x f -> m (Maybe (Graph n e x))
type BRW  m n f e x = n e x -> Fact x f -> m (BwdRes m n f e x)
type SimpleBwdRewrite3 m n f = ExTriple ( SBRW m n f)
type SimpleBwdRewrite m n f = forall e x . SBRW m n f e x
type LiftBRW m n f e x = SBRW m n f e x -> BRW m n f e x
type MapBRW  m n f e x = BRW  m n f e x -> BRW m n f e x
type MapBRW2 m n f e x = BRW  m n f e x -> BRW m n f e x -> BRW m n f e x

----------------------------------------------------------------

wrapSBRewrite3 :: ExTriple (LiftBRW m n f) -> SimpleBwdRewrite3 m n f -> BwdRewrite m n f
wrapSBRewrite3 lift rw = uncurry3 mkBRewrite3 $ apply lift rw

wrapBRewrite3 :: ExTriple (MapBRW m n f) -> BwdRewrite m n f -> BwdRewrite m n f
wrapBRewrite3 map rw = uncurry3 mkBRewrite3 $ apply map $ getBRewrite3 rw

wrapBRewrites2 :: ExTriple (MapBRW2 m n f) -> BR m n f -> BR m n f -> BR m n f
wrapBRewrites2 map rw1 rw2 =
  uncurry3 mkBRewrite3 $ (applyBinary map `on` getBRewrite3) rw1 rw2

-- Combinators for higher-rank rewriting functions:
wrapSBRewrites' :: (forall e x . LiftBRW m n f e x) -> SimpleBwdRewrite3 m n f -> BR m n f
wrapSBRewrites' lift = wrapSBRewrite3 (lift, lift, lift)

wrapBRewrites' :: (forall e x . MapBRW m n f e x) -> BwdRewrite m n f -> BwdRewrite m n f
wrapBRewrites' map = wrapBRewrite3 (map, map, map)

wrapBRewrites2' :: (forall e x . MapBRW2 m n f e x) -> BR m n f -> BR m n f -> BR m n f
wrapBRewrites2' map = wrapBRewrites2 (map, map, map)

----------------------------------------------------------------

noBwdRewrite :: Monad m => BwdRewrite m n f
noBwdRewrite = mkBRewrite $ \ _ _ -> return Nothing

shallowBwdRw3 :: Monad m => SimpleBwdRewrite3 m n f -> BwdRewrite m n f
shallowBwdRw3 rw = wrapSBRewrites' lift rw
  where lift rw n f = liftM (fmap (flip BwdRew noBwdRewrite)) (rw n f)

shallowBwdRw :: Monad m => SimpleBwdRewrite m n f -> BwdRewrite m n f
shallowBwdRw f = shallowBwdRw3 (f, f, f)

deepBwdRw3 :: Monad m => SimpleBwdRewrite3 m n f -> BwdRewrite m n f
deepBwdRw  :: Monad m => SimpleBwdRewrite  m n f -> BwdRewrite m n f
deepBwdRw3 r = iterBwdRw (shallowBwdRw3 r)
deepBwdRw  f = deepBwdRw3 (f, f, f)


thenBwdRw :: Monad m => BwdRewrite m n f -> BwdRewrite m n f -> BwdRewrite m n f
thenBwdRw rw1 rw2 = wrapBRewrites2' f rw1 rw2
  where f rw1 rw2' n f = do
          res1 <- rw1 n f
          case res1 of
            Nothing              -> rw2' n f
            Just (BwdRew g rw1a) -> return $ Just $ BwdRew g (rw1a `thenBwdRw` rw2)

iterBwdRw :: Monad m => BwdRewrite m n f -> BwdRewrite m n f
iterBwdRw rw = wrapBRewrites' f rw
  where f rw' n f = liftM (fmap iterRewrite) (rw' n f)
        iterRewrite (BwdRew g rw2) = BwdRew g (rw2 `thenBwdRw` iterBwdRw rw)

pairFwd :: forall m n f f' . Monad m => FwdPass m n f -> FwdPass m n f' -> FwdPass m n (f, f')
pairFwd pass1 pass2 = FwdPass lattice transfer rewrite
  where
    lattice = pairLattice (fp_lattice pass1) (fp_lattice pass2)
    transfer = mkFTransfer3 (tf tf1 tf2) (tf tm1 tm2) (tfb tl1 tl2)
      where
        tf  t1 t2 n (f1, f2) = (t1 n f1, t2 n f2)
        tfb t1 t2 n (f1, f2) = mapMapWithKey withfb2 fb1
          where fb1 = t1 n f1
                fb2 = t2 n f2
                withfb2 l f = (f, fromMaybe bot2 $ lookupFact l fb2)
                bot2 = fact_bot (fp_lattice pass2)
        (tf1, tm1, tl1) = getFTransfer3 (fp_transfer pass1)
        (tf2, tm2, tl2) = getFTransfer3 (fp_transfer pass2)
    rewrite = liftRW (fp_rewrite pass1) fst `thenFwdRw` liftRW (fp_rewrite pass2) snd
      where
        liftRW rws proj = mkFRewrite3 (lift f) (lift m) (lift l)
          where lift rw n f = liftM (fmap projRewrite) $ rw n (proj f)
                projRewrite (FwdRew g rws') = FwdRew g $ liftRW rws' proj
                (f, m, l) = getFRewrite3 rws

pairBwd :: forall m n f f' . Monad m => BwdPass m n f -> BwdPass m n f' -> BwdPass m n (f, f')
pairBwd pass1 pass2 = BwdPass lattice transfer rewrite
  where
    lattice = pairLattice (bp_lattice pass1) (bp_lattice pass2)
    transfer = mkBTransfer3 (tf tf1 tf2) (tf tm1 tm2) (tfb tl1 tl2)
      where
        tf  t1 t2 n (f1, f2) = (t1 n f1, t2 n f2)
        tfb t1 t2 n fb = (t1 n $ mapMap fst fb, t2 n $ mapMap snd fb)
        (tf1, tm1, tl1) = getBTransfer3 (bp_transfer pass1)
        (tf2, tm2, tl2) = getBTransfer3 (bp_transfer pass2)
    rewrite = liftRW (bp_rewrite pass1) fst `thenBwdRw` liftRW (bp_rewrite pass2) snd
      where
        liftRW :: forall f1 . BwdRewrite m n f1 -> ((f, f') -> f1) -> BwdRewrite m n (f, f')
        liftRW rws proj = mkBRewrite3 (lift proj f) (lift proj m) (lift (mapMap proj) l)
          where lift proj' rw n f = liftM (fmap projRewrite) $ rw n (proj' f)
                projRewrite (BwdRew g rws') = BwdRew g $ liftRW rws' proj
                (f, m, l) = getBRewrite3 rws

pairLattice :: forall f f' . DataflowLattice f -> DataflowLattice f' -> DataflowLattice (f, f')
pairLattice l1 l2 =
  DataflowLattice
    { fact_name = fact_name l1 ++ " x " ++ fact_name l2
    , fact_bot  = (fact_bot l1, fact_bot l2)
    , fact_join = join
    }
  where
    join lbl (OldFact (o1, o2)) (NewFact (n1, n2)) = (c', (f1, f2))
      where (c1, f1) = fact_join l1 lbl (OldFact o1) (NewFact n1)
            (c2, f2) = fact_join l2 lbl (OldFact o2) (NewFact n2)
            c' = case (c1, c2) of
                   (NoChange, NoChange) -> NoChange
                   _                    -> SomeChange
