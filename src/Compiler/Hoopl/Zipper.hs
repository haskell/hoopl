{-# LANGUAGE GADTs #-}

module Compiler.Hoopl.Zipper
  ( ZBlock(..), ZGraph, ZBody
  , frontBiasBlock, backBiasBlock
  )
where

import Compiler.Hoopl.Graph

data ZBlock n e x where
  -- nodes
  ZFirst  :: n C O                 -> ZBlock n C O
  ZMiddle :: n O O                 -> ZBlock n O O
  ZLast   :: n O C                 -> ZBlock n O C

  -- concatenation operations
  ZCat    :: ZBlock n O O -> ZBlock n O O -> ZBlock n O O -- non-list-like
  ZHead   :: ZBlock n C O -> n O O        -> ZBlock n C O
  ZTail   :: n O O        -> ZBlock n O C -> ZBlock n O C  

  ZClosed :: ZBlock n C O -> ZBlock n O C -> ZBlock n C C -- the zipper

type ZGraph = Graph' ZBlock
type ZBody  = Body'  ZBlock

instance Edges n => Edges (ZBlock n) where
  entryLabel (ZFirst n)    = entryLabel n
  entryLabel (ZHead h _)   = entryLabel h
  entryLabel (ZClosed h _) = entryLabel h
  successors (ZLast n)     = successors n
  successors (ZTail _ t)   = successors t
  successors (ZClosed _ t) = successors t


----------------------------------------------------------------

-- | A block is "front biased" if the left child of every
-- concatenation operation is a node, not a general block; a
-- front-biased block is analogous to an ordinary list.  If a block is
-- front-biased, then its nodes can be traversed from front to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be front-biased; a closed/open block is inherently back-biased.

frontBiasBlock :: ZBlock n e x -> ZBlock n e x
frontBiasBlock b@(ZFirst  {}) = b
frontBiasBlock b@(ZMiddle {}) = b
frontBiasBlock b@(ZLast   {}) = b
frontBiasBlock b@(ZCat {}) = rotate b
  where -- rotate and append ensure every left child of ZCat is ZMiddle
        -- provided 2nd argument to append already has this property
    rotate :: ZBlock n O O -> ZBlock n O O
    append :: ZBlock n O O -> ZBlock n O O -> ZBlock n O O
    rotate (ZCat h t)     = append h (rotate t)
    rotate b@(ZMiddle {}) = b
    append b@(ZMiddle {}) t = b `ZCat` t
    append (ZCat b1 b2) b3 = b1 `append` (b2 `append` b3)
frontBiasBlock b@(ZHead {}) = b -- back-biased by nature; cannot fix
frontBiasBlock b@(ZTail {}) = b -- statically front-biased
frontBiasBlock (ZClosed h t) = shiftRight h t
    where shiftRight :: ZBlock n C O -> ZBlock n O C -> ZBlock n C C
          shiftRight (ZHead b1 b2) b3 = shiftRight b1 (ZTail b2 b3)
          shiftRight b1@(ZFirst {}) b2 = ZClosed b1 b2

-- | A block is "back biased" if the right child of every
-- concatenation operation is a node, not a general block; a
-- back-biased block is analogous to a snoc-list.  If a block is
-- back-biased, then its nodes can be traversed from back to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be back-biased; an open/closed block is inherently front-biased.

backBiasBlock :: ZBlock n e x -> ZBlock n e x
backBiasBlock b@(ZFirst  {}) = b
backBiasBlock b@(ZMiddle {}) = b
backBiasBlock b@(ZLast   {}) = b
backBiasBlock b@(ZCat {}) = rotate b
  where -- rotate and append ensure every right child of ZCat is ZMiddle
        -- provided 1st argument to append already has this property
    rotate :: ZBlock n O O -> ZBlock n O O
    append :: ZBlock n O O -> ZBlock n O O -> ZBlock n O O
    rotate (ZCat h t)     = append (rotate h) t
    rotate b@(ZMiddle {}) = b
    append h b@(ZMiddle {}) = h `ZCat` b
    append b1 (ZCat b2 b3) = (b1 `append` b2) `append` b3
backBiasBlock b@(ZHead {}) = b -- statically back-biased
backBiasBlock b@(ZTail {}) = b -- front-biased by nature; cannot fix
backBiasBlock (ZClosed h t) = shiftLeft h t
    where shiftLeft :: ZBlock n C O -> ZBlock n O C -> ZBlock n C C
          shiftLeft b1 (ZTail b2 b3) = shiftLeft (ZHead b1 b2) b3
          shiftLeft b1 b2@(ZLast {}) = ZClosed b1 b2
