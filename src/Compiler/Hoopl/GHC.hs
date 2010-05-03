{- Exposing some internals to GHC -}
module Compiler.Hoopl.GHC
  ( uniqueToInt
  , uniqueToLbl, lblToUnique
  , getFuel, setFuel
  )
where

import Compiler.Hoopl.Label
import Compiler.Hoopl.Unique
import Compiler.Hoopl.Fuel
