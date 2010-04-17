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
newtype LabelSet = LS { unLS :: S.IntSet }

emptyLabelSet :: LabelSet
emptyLabelSet = LS S.empty

extendLabelSet :: LabelSet -> Label -> LabelSet
extendLabelSet lbls (Label bid) = LS $ S.insert bid $ unLS lbls

reduceLabelSet :: LabelSet -> Label -> LabelSet
reduceLabelSet lbls (Label bid) = LS $ S.delete bid $ unLS lbls

elemLabelSet :: Label -> LabelSet -> Bool
elemLabelSet (Label bid) lbls = S.member bid (unLS lbls)

labelSetElems :: LabelSet -> [Label]
labelSetElems = map Label . S.toList . unLS

set2 :: (S.IntSet -> S.IntSet -> S.IntSet)
     -> (LabelSet -> LabelSet -> LabelSet)
set2 f (LS ls) (LS ls') = LS (f ls ls')

minusLabelSet :: LabelSet -> LabelSet -> LabelSet
minusLabelSet = set2 S.difference

unionLabelSet :: LabelSet -> LabelSet -> LabelSet
unionLabelSet = set2 S.union

interLabelSet :: LabelSet -> LabelSet -> LabelSet
interLabelSet = set2 S.intersection

sizeLabelSet :: LabelSet -> Int
sizeLabelSet = S.size . unLS

mkLabelSet :: [Label] -> LabelSet
mkLabelSet = LS . S.fromList . map unLabel


