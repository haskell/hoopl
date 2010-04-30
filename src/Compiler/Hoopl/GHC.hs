{- Exposing some internals to GHC -}
module Compiler.Hoopl.GHC
  ( lblOfUniq, uniqOfLbl
  , intOfUniq
  )
where

import Compiler.Hoopl.Label
import Compiler.Hoopl.Unique
