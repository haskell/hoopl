{-# LANGUAGE RankNTypes, LiberalTypeSynonyms, ScopedTypeVariables #-}

module Compiler.Hoopl.Combinators
  ( thenFwdRw
  , deepFwdRw3, deepFwdRw, iterFwdRw
  , thenBwdRw
  , deepBwdRw3, deepBwdRw, iterBwdRw
  , pairFwd, pairBwd, pairLattice
  )

where

import Control.Monad
import Data.Function
import Data.Maybe

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Fuel
import Compiler.Hoopl.Graph (Graph, C, O)
import Compiler.Hoopl.Label

type BR m n f = BwdRewrite m n f

type FromFwdRw3 m n f a 
            =  (n C O -> f -> m (Maybe (Graph n C O)))
            -> (n O O -> f -> m (Maybe (Graph n O O)))
            -> (n O C -> f -> m (Maybe (Graph n O C)))
            -> a

----------------------------------------------------------------
-- common operations on triples

apply :: (a -> b, d -> e, g -> h) -> (a, d, g) -> (b, e, h)
apply (f1, f2, f3) (x1, x2, x3) = (f1 x1, f2 x2, f3 x3)

applyBinary :: (a -> b -> c, d -> e -> f, g -> h -> i)
            -> (a, d, g) -> (b, e, h) -> (c, f, i)
applyBinary (f1, f2, f3) (x1, x2, x3) (y1, y2, y3) = (f1 x1 y1, f2 x2 y2, f3 x3 y3)


----------------------------------------------------------------

deepFwdRw3 :: FuelMonad m => FromFwdRw3 m n f (FwdRewrite m n f)
deepFwdRw :: FuelMonad m
          => (forall e x . n e x -> f -> m (Maybe (Graph n e x))) -> FwdRewrite m n f
deepFwdRw3 f m l = iterFwdRw $ mkFRewrite3 f m l
deepFwdRw f = deepFwdRw3 f f f

-- N.B. rw3, rw3', and rw3a are triples of functions.
-- But rw and rw' are single functions.
-- @ start comb1.tex
thenFwdRw :: Monad m 
          => FwdRewrite m n f 
          -> FwdRewrite m n f 
          -> FwdRewrite m n f
-- @ end comb1.tex
thenFwdRw rw3 rw3' =
  FwdRewrite3 $ (applyBinary (thenrw, thenrw, thenrw) `on` getFRewrite3) rw3 rw3'
 where
  thenrw rw rw' n f = rw n f >>= fwdRes
     where fwdRes Nothing = rw' n f
           fwdRes (Just (FwdRew g rw3a))
            = return $ Just $ FwdRew g (rw3a `thenFwdRw` rw3')

-- @ start iterf.tex
iterFwdRw :: Monad m 
          => FwdRewrite m n f 
          -> FwdRewrite m n f
-- @ end iterf.tex
iterFwdRw rw3 = FwdRewrite3 . apply (iter, iter, iter) . getFRewrite3 $ rw3
 where
    iter rw n f = liftM (liftM fwdRes) (rw n f)
    fwdRes (FwdRew g rw3a) = 
      FwdRew g (rw3a `thenFwdRw` iterFwdRw rw3)

----------------------------------------------------------------
type FromBwdRw3 m n f a 
            =  (n C O -> f          -> m (Maybe (Graph n C O)))
            -> (n O O -> f          -> m (Maybe (Graph n O O)))
            -> (n O C -> FactBase f -> m (Maybe (Graph n O C)))
            -> a

type BRW  m n f e x = n e x -> Fact x f -> m (Maybe (BwdRew m n f e x))
type MapBRW2 m n f e x = BRW  m n f e x -> BRW m n f e x -> BRW m n f e x

----------------------------------------------------------------

wrapBRewrites2 :: (forall e x . MapBRW2 m n f e x) -> BR m n f -> BR m n f -> BR m n f
wrapBRewrites2 map = w2 (map, map, map)
  where w2 map rw1 rw2 =
            BwdRewrite3 $ (applyBinary map `on` getBRewrite3) rw1 rw2

----------------------------------------------------------------

deepBwdRw3 :: FuelMonad m => FromBwdRw3 m n f (BwdRewrite m n f)
deepBwdRw  :: FuelMonad m
           => (forall e x . n e x -> Fact x f -> m (Maybe (Graph n e x))) -> BwdRewrite m n f
deepBwdRw3 f m l = iterBwdRw $ mkBRewrite3 f m l
deepBwdRw  f = deepBwdRw3 f f f


thenBwdRw :: Monad m => BwdRewrite m n f -> BwdRewrite m n f -> BwdRewrite m n f
thenBwdRw rw1 rw2 = wrapBRewrites2 f rw1 rw2
  where f rw1 rw2' n f = do
          res1 <- rw1 n f
          case res1 of
            Nothing              -> rw2' n f
            Just (BwdRew g rw1a) -> return $ Just $ BwdRew g (rw1a `thenBwdRw` rw2)

iterBwdRw :: Monad m => BwdRewrite m n f -> BwdRewrite m n f
iterBwdRw rw = BwdRewrite3 . apply (f, f, f) . getBRewrite3 $ rw
  where f rw' n f = liftM (liftM iterRewrite) (rw' n f)
        iterRewrite (BwdRew g rw2) = BwdRew g (rw2 `thenBwdRw` iterBwdRw rw)

-- @ start pairf.tex
pairFwd :: Monad m
        => FwdPass m n f
        -> FwdPass m n f' 
        -> FwdPass m n (f, f')
-- @ end pairf.tex
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
        liftRW rws proj = FwdRewrite3 (lift f, lift m, lift l)
          where lift rw n f = liftM (liftM projRewrite) $ rw n (proj f)
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
        liftRW rws proj = BwdRewrite3 (lift proj f, lift proj m, lift (mapMap proj) l)
          where lift proj' rw n f = liftM (liftM projRewrite) $ rw n (proj' f)
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
