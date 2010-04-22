{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}

module Compiler.Hoopl.Passes.Dominator
  ( Doms, domPath, domEntry, domLattice, extendDom
  , DominatorNode(..), DominatorTree(..), tree
  , domFirst, domMiddle, domLast
  )
where

import Data.Maybe

import Compiler.Hoopl hiding (Top, Bot)
import Compiler.Hoopl.Pointed

type Doms = Pointed O C DPath
-- ^ List of labels, extended with a standard bottom element

-- | The fact that goes into the entry of a dominator analysis: the first node
-- is dominated only by the entry point, which is represented by the empty list
-- of labels.
domEntry :: Doms
domEntry = PElem (DPath [])

newtype DPath = DPath [Label]
  -- ^ represents part of the domination relation: each label
  -- in a list is dominated by all its successors.  This is a newtype only so
  -- we can give it a fancy Show instance.

instance Show DPath where
  show (DPath ls) = concat (foldr (\l path -> show l : " -> " : path) ["entry"] ls)

domPath :: Doms -> [Label]
domPath Bot = [] -- lies: an unreachable node appears to be dominated by the entry
domPath (PElem (DPath ls)) = ls

extendDom :: Label -> DPath -> DPath
extendDom l (DPath ls) = DPath (l:ls)

domLattice :: DataflowLattice Doms
domLattice = addPoints "dominators" extend

extend :: JoinFun DPath
extend _ (OldFact (DPath l)) (NewFact (DPath l')) =
                                (changeIf (l `lengthDiffers` j), DPath j)
    where j = lcs l l'
          lcs :: [Label] -> [Label] -> [Label] -- longest common suffix
          lcs l l' | length l > length l' = lcs (drop (length l - length l') l) l'
                   | length l < length l' = lcs l' l
                   | otherwise = dropUnlike l l' l
          dropUnlike [] [] maybe_like = maybe_like
          dropUnlike (x:xs) (y:ys) maybe_like =
              dropUnlike xs ys (if x == y then maybe_like else xs)
          dropUnlike _ _ _ = error "this can't happen"

          lengthDiffers [] [] = False
          lengthDiffers (_:xs) (_:ys) = lengthDiffers xs ys
          lengthDiffers [] (_:_) = True
          lengthDiffers (_:_) [] = True



-- | Dominator functions for first, middle, and last nodes.
domFirst  :: Edges n => n C O -> FactBase Doms -> Doms
domMiddle :: Edges n => n O O -> f -> f
domLast   :: Edges n => n O C -> f -> FactBase f

domFirst = firstXfer first
  where first n = fmap (extendDom $ entryLabel n)
domMiddle _ = id
domLast     = distributeFact


data DominatorNode = Entry | Labelled Label
data DominatorTree = Dominates DominatorNode [DominatorTree]
-- ^ This data structure is a *rose tree* in which each node may have
--  arbitrarily many children.  Each node dominates all its descendants.

-- | Map from a FactBase for dominator lists into a
-- dominator tree.  
tree :: [(Label, Doms)] -> DominatorTree
tree facts = Dominates Entry $ merge $ map reverse $ map mkList facts
   -- This code has been lightly tested.  The key insight is this: to
   -- find lists that all have the same head, convert from a list of
   -- lists to a finite map, in 'children'.  Then, to convert from the
   -- finite map to list of dominator trees, use the invariant that
   -- each key dominates all the lists of values.
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


instance Show DominatorTree where
  show = tree2dot

-- | Given a dominator tree, produce a string representation, in the
-- input language of dot, that will enable dot to produce a
-- visualization of the tree.  For more info about dot see
-- http://www.graphviz.org.

tree2dot :: DominatorTree -> String
tree2dot t = concat $ "digraph {\n" : dot t ["}\n"]
  where
    dot :: DominatorTree -> [String] -> [String]
    dot (Dominates root trees) = 
                   (dotnode root :) . outedges trees . flip (foldl subtree) trees
      where outedges [] = id
            outedges (Dominates n _ : ts) =
                \s -> "  " : show root : " -> " : show n : "\n" : outedges ts s
            dotnode Entry = "  entryNode [shape=plaintext, label=\"entry\"]\n"
            dotnode (Labelled l) = "  " ++ show l ++ "\n"
            subtree = flip dot

instance Show DominatorNode where
  show Entry = "entryNode"
  show (Labelled l) = show l
