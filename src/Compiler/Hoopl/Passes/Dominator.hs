{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}

module Compiler.Hoopl.Passes.Dominator
  ( Doms, domPath, domEntry, domLattice, extendDom
  , DominatorNode(..), DominatorTree(..), tree
  , domFirst, domMiddle, domLast
  )
where

import Data.Maybe

import Compiler.Hoopl 

domEntry :: Doms
domEntry = DPath []

data Doms = Unreached
          | DPath [Label] -- might hide this one day
  -- ^ represents part of the domination relation: each label
  -- in a list is dominated by all its successors

instance Show Doms where
  show Unreached = "<unreached node>"
  show (DPath ls) = concat (foldr (\l path -> show l : " -> " : path) ["entry"] ls)

domPath :: Doms -> [Label]
domPath Unreached = [] -- lies
domPath (DPath ls) = ls

extendDom :: Label -> Doms -> Doms
extendDom _ Unreached = error "fault in dominator analysis"
extendDom l (DPath ls) = DPath (l:ls)

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
tree facts = Dominates Entry $ merge $ map reverse $ map mkList facts
  where merge lists = mapTree $ children $ filter (not . null) lists
        children = foldl addList noFacts
        addList :: FactBase [[Label]] -> [Label] -> FactBase [[Label]]
        addList map (x:xs) = extendFactBase map x (xs:existing)
            where existing = fromMaybe [] $ lookupFact map x
        addList _ [] = error "this can't happen"
        mapTree :: FactBase [[Label]] -> [DominatorTree]
        mapTree map = [Dominates (Labelled x) (merge lists) |
                                                    (x, lists) <- factBaseList map]
        mkList (l, doms) = l : domPath doms


domLattice :: DataflowLattice Doms
domLattice = DataflowLattice 
        { fact_name = "dominators"
        , fact_bot  = Unreached
        , fact_extend = extend
        , fact_do_logging = True
        }

extend :: JoinFun Doms
extend _ (OldFact d) (NewFact d') = (changeIf (d `differs` j), j)
    where j = join d d'
          join Unreached d = d
          join d Unreached = d
          join (DPath l) (DPath l') = DPath (lcs l l')
          lcs :: [Label] -> [Label] -> [Label] -- longest common suffix
          lcs l l' | length l > length l' = lcs (drop (length l - length l') l) l'
                   | length l < length l' = lcs l' l
                   | otherwise = dropUnlike l l' l
          dropUnlike [] [] maybe_like = maybe_like
          dropUnlike (x:xs) (y:ys) maybe_like =
              dropUnlike xs ys (if x == y then maybe_like else xs)
          dropUnlike _ _ _ = error "this can't happen"

          differs :: Doms -> Doms -> Bool
          differs Unreached Unreached = False
          differs (DPath l) (DPath l') = lengthDiffers l l'
          differs Unreached (DPath _) = True
          differs (DPath _) Unreached = True

          lengthDiffers [] [] = False
          lengthDiffers (_:xs) (_:ys) = lengthDiffers xs ys
          lengthDiffers [] (_:_) = True
          lengthDiffers (_:_) [] = True



firstXfer :: Edges n => (n C O -> f -> f) -> (n C O -> FactBase f -> f)
firstXfer xfer n fb = xfer n $ fromJust $ lookupFact fb $ entryLabel n

distributeXfer :: Edges n => (n O C -> f -> f) -> (n O C -> f -> FactBase f)
distributeXfer xfer n f = mkFactBase [ (l, xfer n f) | l <- successors n ]


domFirst  :: Edges n => n C O -> FactBase Doms -> Doms
domMiddle :: Edges n => n O O -> f -> f
domLast   :: Edges n => n O C -> f -> FactBase f

domFirst = firstXfer first
  where first _ Unreached  = error "fault in dominator analysis"
        first n (DPath ls) = DPath (entryLabel n : ls)
domMiddle _ = id
domLast n = distributeXfer (const id) n

instance Show DominatorTree where
  show t = "digraph {\n" ++ concat (tree2dot t []) ++ "}\n"

tree2dot :: DominatorTree -> [String] -> [String]
tree2dot (Dominates root trees) = 
               (dotnode root :) . outedges trees . flip (foldl subtree) trees
  where outedges [] = id
        outedges (Dominates n _ : ts) =
            \s -> "  " : show root : " -> " : show n : "\n" : outedges ts s
        dotnode Entry = "  entryNode [shape=plaintext, label=\"entry\"]\n"
        dotnode (Labelled l) = "  " ++ show l ++ "\n"
        subtree = flip tree2dot

instance Show DominatorNode where
  show Entry = "entryNode"
  show (Labelled l) = show l
