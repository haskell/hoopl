module Compiler.Hoopl.Util
  ( gUnitOO, gUnitOC, gUnitCO, gUnitCC
  )
where

import Compiler.Hoopl.Graph
gUnitOO :: Block n O O -> Graph n O O
gUnitOC :: Block n O C -> Graph n O C
gUnitCO :: Block n C O -> Graph n C O
gUnitCC :: Block n C C -> Graph n C C
gUnitOO b = GUnit b
gUnitOC b = GMany (JustO b) BodyEmpty   NothingO
gUnitCO b = GMany NothingO  BodyEmpty   (JustO b)
gUnitCC b = GMany NothingO  (BodyUnit b) NothingO
