{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}

module Compiler.Hoopl.Passes.Dominator
  ( Doms, domLattice, extendDom
  , DominatorNode(..), DominatorTree(..), tree
  , domFirst, domMiddle, domLast
  )
where

import Data.Maybe

import Compiler.Hoopl 

type Doms = [Label] -- might hide this one day
  -- represents part of the domination relation: each label
  -- in a list is dominated by all its successors

extendDom :: Label -> Doms -> Doms
extendDom = (:)

data DominatorNode = Entry | Labelled Label
data DominatorTree = Dominates DominatorNode [DominatorTree]
-- ^ This data structure is a *rose tree* in which each node may have
--  arbitrarily many children.  Each node dominates all its descendants.

{-
Also, here is my mapping from a FactBase for dominator lists into a
dominator tree.  I have *not* tested this code yet, so it may have
bugs.  The key insight is this: to find lists that all have the same
head, convert from a list of lists to a finite map, in 'children'.
Then, to convert from the finite map to list of dominator trees,
use the invariant that each key dominates all the lists of values.
-}

tree :: [(Label, Doms)] -> DominatorTree
tree facts = Dominates Entry $ merge $ map reverse $ map (uncurry (:)) facts
  where merge lists = mapTree $ children $ filter (not . null) lists
        children = foldl addList noFacts
        addList :: FactBase [[Label]] -> [Label] -> FactBase [[Label]]
        addList map (x:xs) = extendFactBase map x (xs:existing)
            where existing = fromMaybe [] $ lookupFact map x
        addList _ [] = error "this can't happen"
        mapTree :: FactBase [[Label]] -> [DominatorTree]
        mapTree map = [Dominates (Labelled x) (merge lists) |
                                                    (x, lists) <- factBaseList map]



domLattice :: DataflowLattice Doms
domLattice = DataflowLattice 
        { fact_name = "dominators"
        , fact_bot  = []
        , fact_extend = extend
        , fact_do_logging = True
        }

extend :: JoinFun Doms
extend (OldFact l) (NewFact l') = (changeIf (length l /= length join), join)
    where join = lcs l l'
          lcs :: Doms -> Doms -> Doms -- longest common suffix
          lcs l l' | length l > length l' = lcs (drop (length l - length l') l) l'
                   | length l < length l' = lcs l' l
                   | otherwise = dropUnlike l l' l
          dropUnlike [] [] maybe_like = maybe_like
          dropUnlike (x:xs) (y:ys) maybe_like =
              dropUnlike xs ys (if x == y then maybe_like else xs)
          dropUnlike _ _ _ = error "this can't happen"


domFirst  :: Edges n => n C O -> FactBase f -> f
domMiddle :: Edges n => n O O -> f -> f
domLast   :: Edges n => n O C -> f -> FactBase f

domFirst n f = fromJust $ lookupFact f (entryLabel n)
domMiddle _ = id
domLast n f = mkFactBase [(l, f) | l <- successors n]

