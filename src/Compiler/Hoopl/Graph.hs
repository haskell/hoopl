{-# LANGUAGE GADTs, EmptyDataDecls #-}

module Compiler.Hoopl.Graph 
  ( O, C, Block(..), Body(..), Graph(..), MaybeO(..)
  , Edges(entryLabel, successors)
  , addBlock, bodyList
  )
where

import Compiler.Hoopl.Label

-----------------------------------------------------------------------------
--		Graphs
-----------------------------------------------------------------------------

data O
data C

-- Blocks are always non-empty
data Block n e x where
  BUnit :: n e x -> Block n e x
  BCat  :: Block n e O -> Block n O x -> Block n e x

data Body n where
  BodyEmpty :: Body n
  BodyUnit  :: Block n C C -> Body n
  BodyCat   :: Body n -> Body n -> Body n

data Graph n e x where
  GNil  :: Graph n O O
  GUnit :: Block n O O -> Graph n O O
  GMany :: MaybeO e (Block n O C) 
        -> Body n
        -> MaybeO x (Block n C O)
        -> Graph n e x

data MaybeO ex t where
  JustO    :: t -> MaybeO O t
  NothingO ::      MaybeO C t

-------------------------------
class Edges thing where
  entryLabel :: thing C x -> Label
  successors :: thing e C -> [Label]

instance Edges n => Edges (Block n) where
  entryLabel (BUnit n) = entryLabel n
  entryLabel (b `BCat` _) = entryLabel b
  successors (BUnit n)   = successors n
  successors (BCat _ b)  = successors b

------------------------------
addBlock :: Block n C C -> Body n -> Body n
addBlock b body = BodyUnit b `BodyCat` body

bodyList :: Edges n => Body n -> [(Label,Block n C C)]
bodyList body = go body []
  where
    go BodyEmpty       bs = bs
    go (BodyUnit b)    bs = (entryLabel b, b) : bs
    go (BodyCat b1 b2) bs = go b1 (go b2 bs)

