{-# LANGUAGE GADTs #-}

module Compiler.Hoopl.Util
  ( gUnitOO, gUnitOC, gUnitCO, gUnitCC
  , zblockGraph
  )
where

import Compiler.Hoopl.Graph
import Compiler.Hoopl.Zipper

gUnitOO :: block n O O -> Graph' block n O O
gUnitOC :: block n O C -> Graph' block n O C
gUnitCO :: block n C O -> Graph' block n C O
gUnitCC :: block n C C -> Graph' block n C C
gUnitOO b = GUnit b
gUnitOC b = GMany (JustO b) BodyEmpty   NothingO
gUnitCO b = GMany NothingO  BodyEmpty   (JustO b)
gUnitCC b = GMany NothingO  (BodyUnit b) NothingO

zblockGraph :: ZBlock n e x -> ZGraph n e x
zblockGraph b@(ZFirst  {}) = gUnitCO b
zblockGraph b@(ZMiddle {}) = gUnitOO b
zblockGraph b@(ZLast   {}) = gUnitOC b
zblockGraph b@(ZCat {})    = gUnitOO b
zblockGraph b@(ZHead {})   = gUnitCO b
zblockGraph b@(ZTail {})   = gUnitOC b
zblockGraph b@(ZClosed {}) = gUnitCC b

