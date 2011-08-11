{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif

-- N.B. addBasicBlocks won't work on OO without a Node (branch/label) constraint

module Compiler.Hoopl.GraphUtil
  ( splice, gSplice , cat , bodyGraph, bodyUnion
  , frontBiasBlock, backBiasBlock
  )

where

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label

bodyGraph :: Body n -> Graph n C C
bodyGraph b = GMany NothingO b NothingO

splice :: forall block n e a x . NonLocal (block n) =>
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

        sp (GMany e1 bs1 (JustO x1)) (GMany (JustO e2) b2 x2)
          = GMany e1 (b1 `bodyUnion` b2) x2
          where b1 = addBlock (x1 `bcat` e2) bs1

        sp (GMany e1 b1 NothingO) (GMany NothingO b2 x2)
          = GMany e1 (b1 `bodyUnion` b2) x2

        sp _ _ = error "bogus GADT match failure"

bodyUnion :: forall a . LabelMap a -> LabelMap a -> LabelMap a
bodyUnion = mapUnionWithKey nodups
  where nodups l _ _ = error $ "duplicate blocks with label " ++ show l

gSplice :: NonLocal n => Graph n e a -> Graph n a x -> Graph n e x
gSplice = splice cat

cat :: Block n e O -> Block n O x -> Block n e x
cat b1@(BFirst {})     (BMiddle n)  = BHead   b1 n
cat b1@(BFirst {})  b2@(BLast{})    = BClosed b1 b2
cat b1@(BFirst {})  b2@(BTail{})    = BClosed b1 b2
cat b1@(BFirst {})     (BCat b2 b3) = (b1 `cat` b2) `cat` b3
cat b1@(BHead {})      (BCat b2 b3) = (b1 `cat` b2) `cat` b3
cat b1@(BHead {})      (BMiddle n)  = BHead   b1 n
cat b1@(BHead {})   b2@(BLast{})    = BClosed b1 b2
cat b1@(BHead {})   b2@(BTail{})    = BClosed b1 b2
cat b1@(BMiddle {}) b2@(BMiddle{})  = BCat    b1 b2
cat    (BMiddle n)  b2@(BLast{})    = BTail    n b2
cat b1@(BMiddle {}) b2@(BCat{})     = BCat    b1 b2
cat    (BMiddle n)  b2@(BTail{})    = BTail    n b2
cat    (BCat b1 b2) b3@(BLast{})    = b1 `cat` (b2 `cat` b3)
cat    (BCat b1 b2) b3@(BTail{})    = b1 `cat` (b2 `cat` b3)
cat b1@(BCat {})    b2@(BCat{})     = BCat    b1 b2
cat b1@(BCat {})    b2@(BMiddle{})  = BCat    b1 b2


----------------------------------------------------------------

-- | A block is "front biased" if the left child of every
-- concatenation operation is a node, not a general block; a
-- front-biased block is analogous to an ordinary list.  If a block is
-- front-biased, then its nodes can be traversed from front to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be front-biased; a closed/open block is inherently back-biased.

frontBiasBlock :: Block n e x -> Block n e x
frontBiasBlock b@(BFirst  {}) = b
frontBiasBlock b@(BMiddle {}) = b
frontBiasBlock b@(BLast   {}) = b
frontBiasBlock b@(BCat {}) = rotate b
  where -- rotate and append ensure every left child of ZCat is ZMiddle
        -- provided 2nd argument to append already has this property
    rotate :: Block n O O -> Block n O O
    append :: Block n O O -> Block n O O -> Block n O O
    rotate (BCat h t)     = append h (rotate t)
    rotate b@(BMiddle {}) = b
    append b@(BMiddle {}) t = b `BCat` t
    append (BCat b1 b2) b3 = b1 `append` (b2 `append` b3)
frontBiasBlock b@(BHead {})    = b -- back-biased by nature; cannot fix
frontBiasBlock b@(BTail {})    = b -- statically front-biased
frontBiasBlock   (BClosed h t) = shiftRight h t
    where shiftRight :: Block n C O -> Block n O C -> Block n C C
          shiftRight (BHead b1 b2)  b3 = shiftRight b1 (BTail b2 b3)
          shiftRight b1@(BFirst {}) b2 = BClosed b1 b2

-- | A block is "back biased" if the right child of every
-- concatenation operation is a node, not a general block; a
-- back-biased block is analogous to a snoc-list.  If a block is
-- back-biased, then its nodes can be traversed from back to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be back-biased; an open/closed block is inherently front-biased.

backBiasBlock :: Block n e x -> Block n e x
backBiasBlock b@(BFirst  {}) = b
backBiasBlock b@(BMiddle {}) = b
backBiasBlock b@(BLast   {}) = b
backBiasBlock b@(BCat {}) = rotate b
  where -- rotate and append ensure every right child of Cat is Middle
        -- provided 1st argument to append already has this property
    rotate :: Block n O O -> Block n O O
    append :: Block n O O -> Block n O O -> Block n O O
    rotate (BCat h t)     = append (rotate h) t
    rotate b@(BMiddle {}) = b
    append h b@(BMiddle {}) = h `BCat` b
    append b1 (BCat b2 b3) = (b1 `append` b2) `append` b3
backBiasBlock b@(BHead {}) = b -- statically back-biased
backBiasBlock b@(BTail {}) = b -- front-biased by nature; cannot fix
backBiasBlock (BClosed h t) = shiftLeft h t
    where shiftLeft :: Block n C O -> Block n O C -> Block n C C
          shiftLeft b1 (BTail b2 b3) = shiftLeft (BHead b1 b2) b3
          shiftLeft b1 b2@(BLast {}) = BClosed b1 b2
