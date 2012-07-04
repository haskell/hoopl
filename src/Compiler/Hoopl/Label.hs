{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif

module Compiler.Hoopl.Label
  ( Label
  , freshLabel
  , LabelSet, LabelMap
  , FactBase, noFacts, lookupFact

  , uniqueToLbl -- MkGraph and GHC use only
  , lblToUnique -- GHC use only
  )

where

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Unique

-----------------------------------------------------------------------------
--		Label
-----------------------------------------------------------------------------

type Label = Unique

lblToUnique :: Label -> Unique
lblToUnique = id

uniqueToLbl :: Unique -> Label
uniqueToLbl = id

--instance Show Label where
--  show (Label n) = "L" ++ show n

freshLabel :: UniqueMonad m => m Label
freshLabel = freshUnique >>= return . uniqueToLbl

type LabelSet = UniqueSet
type LabelMap v = UniqueMap v

-----------------------------------------------------------------------------
-- FactBase

type FactBase f = LabelMap f

noFacts :: FactBase f
noFacts = mapEmpty

lookupFact :: Label -> FactBase f -> Maybe f
lookupFact = mapLookup
