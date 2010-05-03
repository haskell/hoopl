{-# LANGUAGE TypeFamilies #-}
module Compiler.Hoopl.Label
  ( Label
  , freshLabel
  , LabelSet, LabelMap
  , FactBase, noFacts, mkFactBase, lookupFact

  , uniqueToLbl -- MkGraph and GHC use only
  , lblToUnique -- GHC use only
  )

where

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Unique

-----------------------------------------------------------------------------
--		Label
-----------------------------------------------------------------------------

newtype Label = Label { lblToUnique :: Unique }
  deriving (Eq, Ord)

uniqueToLbl :: Unique -> Label
uniqueToLbl = Label

instance Show Label where
  show (Label n) = "L" ++ show n

freshLabel :: UniqueMonad m => m Label
freshLabel = freshUnique >>= return . uniqueToLbl

-----------------------------------------------------------------------------
-- LabelSet

newtype LabelSet = LS UniqueSet deriving (Eq, Ord, Show)

instance IsSet LabelSet where
  type KeySet LabelSet = Label

  nullSet (LS s) = nullSet s
  sizeSet (LS s) = sizeSet s
  memberSet (Label k) (LS s) = memberSet k s

  emptySet = LS emptySet
  singletonSet (Label k) = LS (singletonSet k)
  insertSet (Label k) (LS s) = LS (insertSet k s)
  deleteSet (Label k) (LS s) = LS (deleteSet k s)

  unionSet (LS x) (LS y) = LS (unionSet x y)
  differenceSet (LS x) (LS y) = LS (differenceSet x y)
  intersectionSet (LS x) (LS y) = LS (intersectionSet x y)
  isSubsetOfSet (LS x) (LS y) = isSubsetOfSet x y

  foldSet k z (LS s) = foldSet (k . uniqueToLbl) z s

  elemsSet (LS s) = map uniqueToLbl (elemsSet s)
  fromListSet ks = LS (fromListSet (map lblToUnique ks))

-----------------------------------------------------------------------------
-- LabelMap

newtype LabelMap v = LM (UniqueMap v) deriving (Eq, Ord, Show)

instance IsMap LabelMap where
  type KeyMap LabelMap = Label

  nullMap (LM m) = nullMap m
  sizeMap (LM m) = sizeMap m
  memberMap (Label k) (LM m) = memberMap k m
  lookupMap (Label k) (LM m) = lookupMap k m
  findWithDefaultMap def (Label k) (LM m) = findWithDefaultMap def k m

  emptyMap = LM emptyMap
  singletonMap (Label k) v = LM (singletonMap k v)
  insertMap (Label k) v (LM m) = LM (insertMap k v m)
  deleteMap (Label k) (LM m) = LM (deleteMap k m)

  unionMap (LM x) (LM y) = LM (unionMap x y)
  unionWithKeyMap f (LM x) (LM y) = LM (unionWithKeyMap (f . uniqueToLbl) x y)
  differenceMap (LM x) (LM y) = LM (differenceMap x y)
  intersectionMap (LM x) (LM y) = LM (intersectionMap x y)
  isSubmapOfMap (LM x) (LM y) = isSubmapOfMap x y

  mapMap f (LM m) = LM (mapMap f m)
  mapWithKeyMap f (LM m) = LM (mapWithKeyMap (f . uniqueToLbl) m)
  foldMap k z (LM m) = foldMap k z m
  foldWithKeyMap k z (LM m) = foldWithKeyMap (k . uniqueToLbl) z m

  elemsMap (LM m) = elemsMap m
  keysMap (LM m) = map uniqueToLbl (keysMap m)
  toListMap (LM m) = [(uniqueToLbl k, v) | (k, v) <- toListMap m]
  fromListMap assocs = LM (fromListMap [(lblToUnique k, v) | (k, v) <- assocs])

-----------------------------------------------------------------------------
-- FactBase

type FactBase f = LabelMap f

noFacts :: FactBase f
noFacts = emptyMap

mkFactBase :: [(Label, f)] -> FactBase f
mkFactBase = fromListMap

lookupFact :: Label -> FactBase f -> Maybe f
lookupFact = lookupMap
