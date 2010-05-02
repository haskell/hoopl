{- Baseclasses for Map-like and Set-like collections inspired by containers. -}

{-# LANGUAGE TypeFamilies #-}
module Compiler.Hoopl.Collections ( IsSet(..)
                                  , IsMap(..)
                                  ) where

import Data.List (foldl', foldl1')

class IsSet set where
  type KeySet set

  nullSet :: set -> Bool
  sizeSet :: set -> Int
  memberSet :: KeySet set -> set -> Bool

  emptySet :: set
  singletonSet :: KeySet set -> set
  insertSet :: KeySet set -> set -> set
  deleteSet :: KeySet set -> set -> set

  unionSet :: set -> set -> set
  differenceSet :: set -> set -> set
  intersectionSet :: set -> set -> set
  isSubsetOfSet :: set -> set -> Bool

  foldSet :: (KeySet set -> b -> b) -> b -> set -> b

  elemsSet :: set -> [KeySet set]
  fromListSet :: [KeySet set] -> set

  -- and some derived functions
  insertListSet :: [KeySet set] -> set -> set
  insertListSet keys set = foldl' (flip insertSet) set keys

  deleteListSet :: [KeySet set] -> set -> set
  deleteListSet keys set = foldl' (flip deleteSet) set keys

  unionsSet :: [set] -> set
  unionsSet [] = emptySet
  unionsSet sets = foldl1' unionSet sets


class IsMap map where
  type KeyMap map

  nullMap :: map a -> Bool
  sizeMap :: map a -> Int
  memberMap :: KeyMap map -> map a -> Bool
  lookupMap :: KeyMap map -> map a -> Maybe a
  findWithDefaultMap :: a -> KeyMap map -> map a -> a

  emptyMap :: map a
  singletonMap :: KeyMap map -> a -> map a
  insertMap :: KeyMap map -> a -> map a -> map a
  deleteMap :: KeyMap map -> map a -> map a

  unionMap :: map a -> map a -> map a
  unionWithKeyMap :: (KeyMap map -> a -> a -> a) -> map a -> map a -> map a
  differenceMap :: map a -> map a -> map a
  intersectionMap :: map a -> map a -> map a
  isSubmapOfMap :: Eq a => map a -> map a -> Bool

  mapMap :: (a -> b) -> map a -> map b
  mapWithKeyMap :: (KeyMap map -> a -> b) -> map a -> map b
  foldMap :: (a -> b -> b) -> b -> map a -> b
  foldWithKeyMap :: (KeyMap map -> a -> b -> b) -> b -> map a -> b

  elemsMap :: map a -> [a]
  keysMap :: map a -> [KeyMap map]
  toListMap :: map a -> [(KeyMap map, a)]
  fromListMap :: [(KeyMap map, a)] -> map a

  -- and some derived functions
  insertListMap :: [(KeyMap map, a)] -> map a -> map a
  insertListMap assocs map = foldl' (flip (uncurry insertMap)) map assocs

  deleteListMap :: [KeyMap map] -> map a -> map a
  deleteListMap keys map = foldl' (flip deleteMap) map keys

  unionsMap :: [map a] -> map a
  unionsMap [] = emptyMap
  unionsMap maps = foldl1' unionMap maps
