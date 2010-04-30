module Compiler.Hoopl.Unique
  ( Unique, uniqOfInt, intOfUniq
  , allUniques {- to be used only by the Fuel monad -}
  )

where

import qualified Data.IntMap as M
import qualified Data.IntSet as S

-----------------------------------------------------------------------------
--		Unique
-----------------------------------------------------------------------------

data Unique = Unique {-# UNPACK #-} !Int
  deriving (Eq, Ord)

instance Show Unique where
  show (Unique n) = show n

uniqOfInt :: Int -> Unique
uniqOfInt = Unique

intOfUniq :: Unique -> Int
intOfUniq (Unique key) = key

allUniques :: [Unique]
allUniques = map Unique [1..]
