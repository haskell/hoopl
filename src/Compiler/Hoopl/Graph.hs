{-# LANGUAGE GADTs, EmptyDataDecls, TypeFamilies #-}

module Compiler.Hoopl.Graph 
  ( O, C, Block(..), Body, Body'(..), Graph, Graph'(..)
  , MaybeO(..), MaybeC(..), EitherCO
  , NonLocal(entryLabel, successors)
  , emptyBody, addBlock, bodyList
  )
where

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Label

-----------------------------------------------------------------------------
--		Graphs
-----------------------------------------------------------------------------

-- | Used at the type level to indicate an "open" structure with    
-- a unique, unnamed control-flow edge flowing in or out.         
-- "Fallthrough" and concatenation are permitted at an open point.
data O 
       
       
-- | Used at the type level to indicate a "closed" structure which
-- supports control transfer only through the use of named
-- labels---no "fallthrough" is permitted.  The number of control-flow
-- edges is unconstrained.
data C

-- | A sequence of nodes.  May be any of four shapes (O/O, O/C, C/O, C/C).
-- Open at the entry means single entry, mutatis mutandis for exit.
-- A closed/closed block is a /basic/ block and can't be extended further.
-- Clients should avoid manipulating blocks and should stick to either nodes
-- or graphs.
data Block n e x where
  -- nodes
  BFirst  :: n C O                 -> Block n C O -- x^ block holds a single first node
  BMiddle :: n O O                 -> Block n O O -- x^ block holds a single middle node
  BLast   :: n O C                 -> Block n O C -- x^ block holds a single last node

  -- concatenation operations
  BCat    :: Block n O O -> Block n O O -> Block n O O -- non-list-like
  BHead   :: Block n C O -> n O O       -> Block n C O
  BTail   :: n O O       -> Block n O C -> Block n O C  

  BClosed :: Block n C O -> Block n O C -> Block n C C -- the zipper

-- | A (possibly empty) collection of closed/closed blocks
type Body = Body' Block
newtype Body' block n = Body (LabelMap (block n C C))

-- | A control-flow graph, which may take any of four shapes (O/O, O/C, C/O, C/C).
-- A graph open at the entry has a single, distinguished, anonymous entry point;
-- if a graph is closed at the entry, its entry point(s) are supplied by a context.
type Graph = Graph' Block
data Graph' block n e x where
  GNil  :: Graph' block n O O
  GUnit :: block n O O -> Graph' block n O O
  GMany :: MaybeO e (block n O C) 
        -> Body' block n
        -> MaybeO x (block n C O)
        -> Graph' block n e x

-- | Maybe type indexed by open/closed
data MaybeO ex t where
  JustO    :: t -> MaybeO O t
  NothingO ::      MaybeO C t

-- | Maybe type indexed by closed/open
data MaybeC ex t where
  JustC    :: t -> MaybeC C t
  NothingC ::      MaybeC O t

-- | Either type indexed by closed/open using type families
type family   EitherCO e a b :: *
type instance EitherCO C a b = a
type instance EitherCO O a b = b

instance Functor (MaybeO ex) where
  fmap _ NothingO = NothingO
  fmap f (JustO a) = JustO (f a)

instance Functor (MaybeC ex) where
  fmap _ NothingC = NothingC
  fmap f (JustC a) = JustC (f a)

-------------------------------
-- | Gives access to the anchor points for
-- nonlocal edges as well as the edges themselves
class NonLocal thing where 
  entryLabel :: thing C x -> Label   -- ^ The label of a first node or block
  successors :: thing e C -> [Label] -- ^ Gives control-flow successors

instance NonLocal n => NonLocal (Block n) where
  entryLabel (BFirst n)    = entryLabel n
  entryLabel (BHead h _)   = entryLabel h
  entryLabel (BClosed h _) = entryLabel h
  successors (BLast n)     = successors n
  successors (BTail _ t)   = successors t
  successors (BClosed _ t) = successors t

------------------------------
emptyBody :: Body' block n
emptyBody = Body mapEmpty

addBlock :: NonLocal (block n) => block n C C -> Body' block n -> Body' block n
addBlock b (Body body) = Body $ nodupsInsert (entryLabel b) b body
  where nodupsInsert l b body = if mapMember l body then
                                    error $ "duplicate label " ++ show l ++ " in graph"
                                else
                                    mapInsert l b body

bodyList :: NonLocal (block n) => Body' block n -> [(Label,block n C C)]
bodyList (Body body) = mapToList body
