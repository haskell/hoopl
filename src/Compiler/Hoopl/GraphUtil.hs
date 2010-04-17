{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- bug in GHC

-- N.B. addBasicBlocks won't work on OO without a Node (branch/label) constraint

module Compiler.Hoopl.GraphUtil
  ( splice, gSplice, zSplice
  , zCat
  , bodyGraph
  )

where

import Compiler.Hoopl.Graph
import Compiler.Hoopl.Zipper

bodyGraph :: Body n -> Graph n C C
bodyGraph b = GMany NothingO b NothingO

splice :: forall block n e a x .
          (forall e x . block n e O -> block n O x -> block n e x)
       -> (Graph' block n e a -> Graph' block n a x -> Graph' block n e x)
splice bcat = sp
  where sp :: forall e a x .
              Graph' block n e a -> Graph' block n a x -> Graph' block n e x

        sp GNil g2 = g2
        sp g1 GNil = g1

        sp (GUnit b1) (GUnit b2) = GUnit (b1 `bcat` b2)

        sp (GUnit b) (GMany (JustO e) bs x) = GMany (JustO (b `bcat` e)) bs x

        sp (GMany e bs (JustO x)) (GUnit b2) = GMany e bs (JustO (x `bcat` b2))

        sp (GMany e1 bs1 (JustO x1)) (GMany (JustO e2) bs2 x2)
          = GMany e1 (addBlock (x1 `bcat` e2) bs1 `BodyCat` bs2) x2

        sp (GMany e1 bs1 NothingO) (GMany NothingO bs2 x2)
           = GMany e1 (bs1 `BodyCat` bs2) x2


gSplice :: Graph  n e a -> Graph  n a x -> Graph  n e x
zSplice :: ZGraph n e a -> ZGraph n a x -> ZGraph n e x

gSplice = splice BCat
zSplice = splice zCat

zCat :: ZBlock n e O -> ZBlock n O x -> ZBlock n e x
zCat b1@(ZFirst {})     (ZMiddle n)  = ZHead   b1 n
zCat b1@(ZFirst {})  b2@(ZLast{})    = ZClosed b1 b2
zCat b1@(ZFirst {})  b2@(ZTail{})    = ZClosed b1 b2
zCat b1@(ZFirst {})     (ZCat b2 b3) = (b1 `zCat` b2) `zCat` b3
zCat b1@(ZHead {})      (ZCat b2 b3) = (b1 `zCat` b2) `zCat` b3
zCat b1@(ZHead {})      (ZMiddle n)  = ZHead   b1 n
zCat b1@(ZHead {})   b2@(ZLast{})    = ZClosed b1 b2
zCat b1@(ZHead {})   b2@(ZTail{})    = ZClosed b1 b2
zCat    (ZMiddle n)  b2@(ZLast{})    = ZTail    n b2
zCat b1@(ZMiddle {}) b2@(ZCat{})     = ZCat    b1 b2
zCat    (ZMiddle n)  b2@(ZTail{})    = ZTail    n b2
zCat    (ZCat b1 b2) b3@(ZLast{})    = b1 `zCat` (b2 `zCat` b3)
zCat    (ZCat b1 b2) b3@(ZTail{})    = b1 `zCat` (b2 `zCat` b3)
zCat b1@(ZCat {})    b2@(ZCat{})     = ZCat    b1 b2


