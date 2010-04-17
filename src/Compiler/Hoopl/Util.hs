{-# LANGUAGE GADTs, ScopedTypeVariables, FlexibleInstances #-}

module Compiler.Hoopl.Util
  ( gUnitOO, gUnitOC, gUnitCO, gUnitCC
  , zblockGraph
  , postorder_dfs, postorder_dfs_from, postorder_dfs_from_except
  , preorder_dfs, preorder_dfs_from_except
  , labelsDefined, labelsUsed, externalEntryLabels
  , LabelsPtr(..)
  )
where

import Control.Monad

import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label
import Compiler.Hoopl.Zipper

gUnitOO :: block n O O -> Graph' block n O O
gUnitOC :: block n O C -> Graph' block n O C
gUnitCO :: block n C O -> Graph' block n C O
gUnitCC :: block n C C -> Graph' block n C C
gUnitOO b = GUnit b
gUnitOC b = GMany (JustO b) BodyEmpty   NothingO
gUnitCO b = GMany NothingO  BodyEmpty   (JustO b)
gUnitCC b = GMany NothingO  (BodyUnit b) NothingO

zblockGraph :: ZBlock n e x -> ZGraph n e x
zblockGraph b@(ZFirst  {}) = gUnitCO b
zblockGraph b@(ZMiddle {}) = gUnitOO b
zblockGraph b@(ZLast   {}) = gUnitOC b
zblockGraph b@(ZCat {})    = gUnitOO b
zblockGraph b@(ZHead {})   = gUnitCO b
zblockGraph b@(ZTail {})   = gUnitOC b
zblockGraph b@(ZClosed {}) = gUnitCC b


class LabelsPtr l where
  targetLabels :: l -> [Label]

instance Edges n => LabelsPtr (n e C) where
  targetLabels n = successors n

instance LabelsPtr Label where
  targetLabels l = [l]

instance LabelsPtr LabelSet where
  targetLabels = labelSetElems

instance LabelsPtr l => LabelsPtr [l] where
  targetLabels = concatMap targetLabels


-- | Traversal: 'postorder_dfs' returns a list of blocks reachable
-- from the entry of enterable graph. The entry and exit are *not* included.
-- The list has the following property:
--
--	Say a "back reference" exists if one of a block's
--	control-flow successors precedes it in the output list
--
--	Then there are as few back references as possible
--
-- The output is suitable for use in
-- a forward dataflow problem.  For a backward problem, simply reverse
-- the list.  ('postorder_dfs' is sufficiently tricky to implement that
-- one doesn't want to try and maintain both forward and backward
-- versions.)

postorder_dfs :: Edges (block n) => Graph' block n O x -> [block n C C]
preorder_dfs  :: Edges (block n) => Graph' block n O x -> [block n C C]

-- | This is the most important traversal over this data structure.  It drops
-- unreachable code and puts blocks in an order that is good for solving forward
-- dataflow problems quickly.  The reverse order is good for solving backward
-- dataflow problems quickly.  The forward order is also reasonably good for
-- emitting instructions, except that it will not usually exploit Forrest
-- Baskett's trick of eliminating the unconditional branch from a loop.  For
-- that you would need a more serious analysis, probably based on dominators, to
-- identify loop headers.
--
-- The ubiquity of 'postorder_dfs' is one reason for the ubiquity of the 'LGraph'
-- representation, when for most purposes the plain 'Graph' representation is
-- more mathematically elegant (but results in more complicated code).
--
-- Here's an easy way to go wrong!  Consider
-- @
--	A -> [B,C]
--	B -> D
--	C -> D
-- @
-- Then ordinary dfs would give [A,B,D,C] which has a back ref from C to D.
-- Better to get [A,B,C,D]


graphDfs :: (Edges (block n))
         => (LabelMap (block n C C) -> block n O C -> LabelSet -> [block n C C])
         -> (Graph' block n O x -> [block n C C])
graphDfs order (GNil)    = []
graphDfs order (GUnit{}) = []
graphDfs order (GMany (JustO entry) body _) = order blockenv entry emptyLabelSet
  where blockenv = bodyMap body

postorder_dfs = graphDfs postorder_dfs_from_except
preorder_dfs  = graphDfs preorder_dfs_from_except

postorder_dfs_from_except :: forall block e . (Edges block, LabelsPtr e)
                          => LabelMap (block C C) -> e -> LabelSet -> [block C C]
postorder_dfs_from_except blocks b visited =
 vchildren (get_children b) (\acc _visited -> acc) [] visited
 where
   vnode :: block C C -> ([block C C] -> LabelSet -> a) -> [block C C] -> LabelSet -> a
   vnode block cont acc visited =
        if elemLabelSet id visited then
            cont acc visited
        else
            let cont' acc visited = cont (block:acc) visited in
            vchildren (get_children block) cont' acc (extendLabelSet visited id)
      where id = entryLabel block
   vchildren bs cont acc visited = next bs acc visited
      where next children acc visited =
                case children of []     -> cont acc visited
                                 (b:bs) -> vnode b (next bs) acc visited
   get_children block = foldr add_id [] $ targetLabels block
   add_id id rst = case lookupFact blocks id of
                      Just b -> b : rst
                      Nothing -> rst

postorder_dfs_from
    :: (Edges block, LabelsPtr b) => LabelMap (block C C) -> b -> [block C C]
postorder_dfs_from blocks b = postorder_dfs_from_except blocks b emptyLabelSet


----------------------------------------------------------------

data VM a = VM { unVM :: LabelSet -> (a, LabelSet) }
marked :: Label -> VM Bool
mark   :: Label -> VM ()
instance Monad VM where
  return a = VM $ \visited -> (a, visited)
  m >>= k  = VM $ \visited -> let (a, v') = unVM m visited in unVM (k a) v'
marked l = VM $ \v -> (elemLabelSet l v, v)
mark   l = VM $ \v -> ((), extendLabelSet v l)

preorder_dfs_from_except :: forall block e . (Edges block, LabelsPtr e)
                         => LabelMap (block C C) -> e -> LabelSet -> [block C C]
preorder_dfs_from_except blocks b visited =
    (fst $ unVM (children (get_children b)) visited) []
  where children [] = return id
        children (b:bs) = liftM2 (.) (visit b) (children bs)
        visit :: block C C -> VM (HL (block C C))
        visit b = do already <- marked (entryLabel b)
                     if already then return id
                      else do mark (entryLabel b)
                              bs <- children $ get_children b
                              return $ b `cons` bs
        get_children block = foldr add_id [] $ targetLabels block
        add_id id rst = case lookupFact blocks id of
                          Just b -> b : rst
                          Nothing -> rst

type HL a = [a] -> [a] -- Hughes list (constant-time concatenation)
cons :: a -> HL a -> HL a
cons a as tail = a : as tail

----------------------------------------------------------------

labelsDefined :: forall block n e x . Edges (block n) => Graph' block n e x -> LabelSet
labelsDefined GNil      = emptyLabelSet
labelsDefined (GUnit{}) = emptyLabelSet
labelsDefined (GMany _ body x) = foldBodyBlocks addEntry body $ exitLabel x
  where addEntry block labels = extendLabelSet labels (entryLabel block)
        exitLabel :: MaybeO x (block n C O) -> LabelSet
        exitLabel NothingO = emptyLabelSet
        exitLabel (JustO b) = mkLabelSet [entryLabel b]

labelsUsed :: forall block n e x. Edges (block n) => Graph' block n e x -> LabelSet
labelsUsed GNil      = emptyLabelSet
labelsUsed (GUnit{}) = emptyLabelSet
labelsUsed (GMany e body _) = foldBodyBlocks addTargets body $ entryTargets e
  where addTargets block labels = foldl extendLabelSet labels (successors block)
        entryTargets :: MaybeO e (block n O C) -> LabelSet
        entryTargets NothingO = emptyLabelSet
        entryTargets (JustO b) = addTargets b emptyLabelSet

foldBodyBlocks :: (block n C C -> a -> a) -> Body' block n -> a -> a
foldBodyBlocks f BodyEmpty      = id
foldBodyBlocks f (BodyUnit b)   = f b
foldBodyBlocks f (BodyCat b b') = foldBodyBlocks f b . foldBodyBlocks f b'

externalEntryLabels :: Edges (block n) => Body' block n -> LabelSet
externalEntryLabels body = defined `minusLabelSet` used
  where defined = labelsDefined g
        used = labelsUsed g
        g = GMany NothingO body NothingO