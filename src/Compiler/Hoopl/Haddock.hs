{-# LANGUAGE GADTs #-}
module Haddock
where

data Lit a where
  I :: Int  -> Lit Int  -- ^ an integer
  B :: Bool -> Lit Bool -- ^ a Boolean

