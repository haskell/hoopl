{-# LANGUAGE GADTs #-}

-- N.B. addBasicBlocks won't work on OO without a Node (branch/label) constraint

module Compiler.Hoopl.GraphUtil
  ( gCat, addEntrySeq, addExitSeq -- , addBasicBlocks
  , gCatClosed
  , gCatAny
  , bodyGraph
  )

where

import Compiler.Hoopl.Graph

bodyGraph :: Body n -> Graph n C C
bodyGraph b = GMany NothingO b NothingO


gCatAny        :: Graph n e a -> Graph n a x -> Graph n e x
gCat           :: Graph n e O -> Graph n O x -> Graph n e x
addEntrySeq    :: Graph n O C -> Graph n C x -> Graph n O x
addExitSeq     :: Graph n e C -> Graph n C O -> Graph n e O
--addBasicBlocks :: Graph n e x -> Graph n C C -> Graph n e x
gCatClosed     :: Graph n e C -> Graph n C x -> Graph n e x

gCatAny GNil g2 = g2
gCatAny g1 GNil = g1

gCatAny (GUnit b1) (GUnit b2)             
  = GUnit (b1 `BCat` b2)

gCatAny (GUnit b) (GMany (JustO e) bs x) 
  = GMany (JustO (b `BCat` e)) bs x

gCatAny (GMany e bs (JustO x)) (GUnit b2) 
  = GMany e bs (JustO (x `BCat` b2))

gCatAny (GMany e1 bs1 (JustO x1)) (GMany (JustO e2) bs2 x2)
  = GMany e1 (addBlock (x1 `BCat` e2) bs1 `BodyCat` bs2) x2

gCatAny (GMany e1 bs1 NothingO) (GMany NothingO bs2 x2)
   = GMany e1 (bs1 `BodyCat` bs2) x2

gCat = gCatAny
addEntrySeq = gCatAny
addExitSeq = gCatAny
gCatClosed = gCatAny

{-
addEntrySeq (GMany entry body NothingO) (GMany NothingO body' exit) 
  = GMany entry (body `BodyCat` body') exit
  
addExitSeq  (GMany entry body NothingO) (GMany NothingO body' exit) 
  = GMany entry (body `BodyCat` body') exit
  
--addBasicBlocks GNil g2 = g2


gCatClosed (GMany e1 bs1 NothingO) (GMany NothingO bs2 x2)
   = GMany e1 (bs1 `BodyCat` bs2) x2
-}
