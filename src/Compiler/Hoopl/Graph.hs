{-# LANGUAGE GADTs, EmptyDataDecls #-}

module Compiler.Hoopl.Graph 
  ( O, C, Block(..), Body, Body'(..), bodyMap, Graph, Graph'(..), MaybeO(..)
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

type Body = Body' Block
data Body' block n where
  BodyEmpty :: Body' block n
  BodyUnit  :: block n C C -> Body' block n
  BodyCat   :: Body' block n -> Body' block n -> Body' block n

type Graph = Graph' Block
data Graph' block n e x where
  GNil  :: Graph' block n O O
  GUnit :: block n O O -> Graph' block n O O
  GMany :: MaybeO e (block n O C) 
        -> Body' block n
        -> MaybeO x (block n C O)
        -> Graph' block n e x

data MaybeO ex t where
  JustO    :: t -> MaybeO O t
  NothingO ::      MaybeO C t

instance Functor (MaybeO ex) where
  fmap f NothingO = NothingO
  fmap f (JustO a) = JustO (f a)

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
addBlock :: block n C C -> Body' block n -> Body' block n
addBlock b body = BodyUnit b `BodyCat` body

bodyList :: Edges (block n) => Body' block n -> [(Label,block n C C)]
bodyList body = go body []
  where
    go BodyEmpty       bs = bs
    go (BodyUnit b)    bs = (entryLabel b, b) : bs
    go (BodyCat b1 b2) bs = go b1 (go b2 bs)

bodyMap :: Edges (block n) => Body' block n -> LabelMap (block n C C)
bodyMap = mkFactBase . bodyList

