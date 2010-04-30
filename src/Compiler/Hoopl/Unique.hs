module Compiler.Hoopl.Unique
  ( Unique, intOfUniq, uniqOfInt
  , HooplMonad(..)
  )

where

-----------------------------------------------------------------------------
--		Unique
-----------------------------------------------------------------------------

data Unique = Unique { intOfUniq ::  {-# UNPACK #-} !Int }
  deriving (Eq, Ord)

uniqOfInt :: Int -> Unique
uniqOfInt = Unique

instance Show Unique where
  show (Unique n) = show n

class Monad m => HooplMonad m where
  freshUnique :: m Unique
