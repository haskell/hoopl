{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- bug in GHC

-- N.B. addBasicBlocks won't work on OO without a Node (branch/label) constraint

module Compiler.Hoopl.GraphUtil
  ( gSplice
  , bodyGraph
  )

where

import Compiler.Hoopl.Graph

bodyGraph :: Body n -> Graph n C C
bodyGraph b = GMany NothingO b NothingO


gSplice :: Graph n e a -> Graph n a x -> Graph n e x

gSplice GNil g2 = g2
gSplice g1 GNil = g1

gSplice (GUnit b1) (GUnit b2)             
  = GUnit (b1 `BCat` b2)

gSplice (GUnit b) (GMany (JustO e) bs x) 
  = GMany (JustO (b `BCat` e)) bs x

gSplice (GMany e bs (JustO x)) (GUnit b2) 
  = GMany e bs (JustO (x `BCat` b2))

gSplice (GMany e1 bs1 (JustO x1)) (GMany (JustO e2) bs2 x2)
  = GMany e1 (addBlock (x1 `BCat` e2) bs1 `BodyCat` bs2) x2

gSplice (GMany e1 bs1 NothingO) (GMany NothingO bs2 x2)
   = GMany e1 (bs1 `BodyCat` bs2) x2

