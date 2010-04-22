{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- bug in GHC

-- N.B. addBasicBlocks won't work on OO without a Node (branch/label) constraint

module Compiler.Hoopl.GraphUtil ( splice, gSplice , cat , bodyGraph )

where

import Compiler.Hoopl.Graph

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


gSplice :: Graph n e a -> Graph n a x -> Graph n e x
gSplice = splice cat

cat :: Block n e O -> Block n O x -> Block n e x
cat b1@(First {})     (Middle n)  = Head   b1 n
cat b1@(First {})  b2@(Last{})    = Closed b1 b2
cat b1@(First {})  b2@(Tail{})    = Closed b1 b2
cat b1@(First {})     (Cat b2 b3) = (b1 `cat` b2) `cat` b3
cat b1@(Head {})      (Cat b2 b3) = (b1 `cat` b2) `cat` b3
cat b1@(Head {})      (Middle n)  = Head   b1 n
cat b1@(Head {})   b2@(Last{})    = Closed b1 b2
cat b1@(Head {})   b2@(Tail{})    = Closed b1 b2
cat    (Middle n)  b2@(Last{})    = Tail    n b2
cat b1@(Middle {}) b2@(Cat{})     = Cat    b1 b2
cat    (Middle n)  b2@(Tail{})    = Tail    n b2
cat    (Cat b1 b2) b3@(Last{})    = b1 `cat` (b2 `cat` b3)
cat    (Cat b1 b2) b3@(Tail{})    = b1 `cat` (b2 `cat` b3)
cat b1@(Cat {})    b2@(Cat{})     = Cat    b1 b2


