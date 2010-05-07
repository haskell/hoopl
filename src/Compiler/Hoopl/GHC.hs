{- Exposing some internals to GHC -}
module Compiler.Hoopl.GHC
  ( uniqueToInt
  , uniqueToLbl, lblToUnique
  , getFuel, setFuel
  , Body'(..), Block(..)
  )
where

import Compiler.Hoopl.Fuel
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label
import Compiler.Hoopl.Unique
