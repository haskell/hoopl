{- Exposing some internals to GHC -}
module Compiler.Hoopl.GHC
  ( uniqueToInt
  , uniqueToLbl, lblToUnique
  )
where

import Compiler.Hoopl.Label
import Compiler.Hoopl.Unique
