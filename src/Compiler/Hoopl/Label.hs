module Compiler.Hoopl.Label
  ( Label
  , allLabels -- to be used only by the Fuel monad
  , LabelMap
  , FactBase, noFacts, mkFactBase, unitFact, lookupFact, extendFactBase
            , delFromFactBase, unionFactBase
            , elemFactBase, factBaseLabels, factBaseList
  , LabelSet, emptyLabelSet, extendLabelSet, reduceLabelSet
            , mkLabelSet, elemLabelSet, labelSetElems
            , minusLabelSet, unionLabelSet, interLabelSet, sizeLabelSet, 
  )

where

import qualified Data.IntMap as M
import qualified Data.IntSet as S

newtype Label = Label { unLabel :: Int }
  deriving (Eq, Ord)

instance Show Label where
  show (Label n) = "L" ++ show n


allLabels :: [Label]
allLabels = map Label [1..]

type LabelMap a = M.IntMap a



-----------------------------------------------------------------------------
--		Label, FactBase, LabelSet
-----------------------------------------------------------------------------


----------------------
type FactBase a = M.IntMap a

mapFst :: (a->b) -> (a, c) -> (b, c)
mapFst f (a, c) = (f a, c)

noFacts :: FactBase f
noFacts = M.empty

mkFactBase :: [(Label, f)] -> FactBase f
mkFactBase prs = M.fromList $ map (mapFst unLabel) prs

unitFact :: Label -> FactBase f -> FactBase f
-- Restrict a fact base to a single fact
unitFact (Label l) fb = case M.lookup l fb of
                  Just f  -> M.singleton l f
                  Nothing -> M.empty

lookupFact :: FactBase f -> Label -> Maybe f
lookupFact env (Label blk_id) = M.lookup blk_id env

extendFactBase :: FactBase f -> Label -> f -> FactBase f
extendFactBase env (Label blk_id) f = M.insert blk_id f env

unionFactBase :: FactBase f -> FactBase f -> FactBase f
unionFactBase = M.union

elemFactBase :: Label -> FactBase f -> Bool
elemFactBase (Label l) = M.member l

factBaseLabels :: FactBase f -> [Label]
factBaseLabels = map Label . M.keys

factBaseList :: FactBase f -> [(Label, f)]
factBaseList = map (mapFst Label) . M.toList 

delFromFactBase :: FactBase f -> [(Label,a)] -> FactBase f
delFromFactBase fb blks = foldr (M.delete . unLabel . fst) fb blks

----------------------
type LabelSet = S.IntSet -- ought to be a newtype or we expose the rep...

emptyLabelSet :: LabelSet
emptyLabelSet = S.empty

extendLabelSet :: LabelSet -> Label -> LabelSet
extendLabelSet lbls (Label bid) = S.insert bid lbls

reduceLabelSet :: LabelSet -> Label -> LabelSet
reduceLabelSet lbls (Label bid) = S.delete bid lbls

elemLabelSet :: Label -> LabelSet -> Bool
elemLabelSet (Label bid) lbls = S.member bid lbls

labelSetElems :: LabelSet -> [Label]
labelSetElems = map Label . S.toList

minusLabelSet :: LabelSet -> LabelSet -> LabelSet
minusLabelSet = S.difference

unionLabelSet :: LabelSet -> LabelSet -> LabelSet
unionLabelSet = S.union

interLabelSet :: LabelSet -> LabelSet -> LabelSet
interLabelSet = S.intersection

sizeLabelSet :: LabelSet -> Int
sizeLabelSet = S.size

mkLabelSet :: [Label] -> LabelSet
mkLabelSet = S.fromList . map unLabel


