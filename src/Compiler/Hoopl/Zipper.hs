{-# LANGUAGE GADTs #-}

module Compiler.Hoopl.Zipper ( frontBiasBlock, backBiasBlock )
where

import Compiler.Hoopl.Graph

----------------------------------------------------------------

-- | A block is "front biased" if the left child of every
-- concatenation operation is a node, not a general block; a
-- front-biased block is analogous to an ordinary list.  If a block is
-- front-biased, then its nodes can be traversed from front to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be front-biased; a closed/open block is inherently back-biased.

frontBiasBlock :: Block n e x -> Block n e x
frontBiasBlock b@(First  {}) = b
frontBiasBlock b@(Middle {}) = b
frontBiasBlock b@(Last   {}) = b
frontBiasBlock b@(Cat {}) = rotate b
  where -- rotate and append ensure every left child of ZCat is ZMiddle
        -- provided 2nd argument to append already has this property
    rotate :: Block n O O -> Block n O O
    append :: Block n O O -> Block n O O -> Block n O O
    rotate (Cat h t)     = append h (rotate t)
    rotate b@(Middle {}) = b
    append b@(Middle {}) t = b `Cat` t
    append (Cat b1 b2) b3 = b1 `append` (b2 `append` b3)
frontBiasBlock b@(Head {})    = b -- back-biased by nature; cannot fix
frontBiasBlock b@(Tail {})    = b -- statically front-biased
frontBiasBlock   (Closed h t) = shiftRight h t
    where shiftRight :: Block n C O -> Block n O C -> Block n C C
          shiftRight (Head b1 b2)  b3 = shiftRight b1 (Tail b2 b3)
          shiftRight b1@(First {}) b2 = Closed b1 b2

-- | A block is "back biased" if the right child of every
-- concatenation operation is a node, not a general block; a
-- back-biased block is analogous to a snoc-list.  If a block is
-- back-biased, then its nodes can be traversed from back to back
-- without general recusion; tail recursion suffices.  Not all shapes
-- can be back-biased; an open/closed block is inherently front-biased.

backBiasBlock :: Block n e x -> Block n e x
backBiasBlock b@(First  {}) = b
backBiasBlock b@(Middle {}) = b
backBiasBlock b@(Last   {}) = b
backBiasBlock b@(Cat {}) = rotate b
  where -- rotate and append ensure every right child of Cat is Middle
        -- provided 1st argument to append already has this property
    rotate :: Block n O O -> Block n O O
    append :: Block n O O -> Block n O O -> Block n O O
    rotate (Cat h t)     = append (rotate h) t
    rotate b@(Middle {}) = b
    append h b@(Middle {}) = h `Cat` b
    append b1 (Cat b2 b3) = (b1 `append` b2) `append` b3
backBiasBlock b@(Head {}) = b -- statically back-biased
backBiasBlock b@(Tail {}) = b -- front-biased by nature; cannot fix
backBiasBlock (Closed h t) = shiftLeft h t
    where shiftLeft :: Block n C O -> Block n O C -> Block n C C
          shiftLeft b1 (Tail b2 b3) = shiftLeft (Head b1 b2) b3
          shiftLeft b1 b2@(Last {}) = Closed b1 b2
