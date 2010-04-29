{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

-- | Utilities for clients of Hoopl, not used internally.

module Compiler.Hoopl.XUtil
  ( firstXfer, distributeXfer
  , distributeFact, distributeFactBwd
  , successorFacts
  , foldGraphNodes, foldBlockNodesF, foldBlockNodesB
  , analyzeAndRewriteFwdBody
  , analyzeAndRewriteBwdBody
  )
where

import Data.Maybe

import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Fuel
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label
import Compiler.Hoopl.Util


-- | Forward dataflow analysis and rewriting for the special case of a Body.
-- A set of entry points must be supplied; blocks not reachable from
-- the set are thrown away.
analyzeAndRewriteFwdBody
   :: forall n f entries. (Edges n, LabelsPtr entries)
   => FwdPass n f
   -> entries -> Body n -> FactBase f
   -> FuelMonad (Body n, FactBase f)

-- | Backward dataflow analysis and rewriting for the special case of a Body.
-- A set of entry points must be supplied; blocks not reachable from
-- the set are thrown away.
analyzeAndRewriteBwdBody
   :: forall n f entries. (Edges n, LabelsPtr entries)
   => BwdPass n f 
   -> entries -> Body n -> FactBase f 
   -> FuelMonad (Body n, FactBase f)

analyzeAndRewriteFwdBody pass en = mapBodyFacts (analyzeAndRewriteFwd pass (JustC en))
analyzeAndRewriteBwdBody pass en = mapBodyFacts (analyzeAndRewriteBwd pass (JustC en))

mapBodyFacts
    :: (Graph n C C -> Fact C f   -> FuelMonad (Graph n C C, Fact C f, MaybeO C f))
    -> (Body n      -> FactBase f -> FuelMonad (Body n, FactBase f))
-- ^ Internal utility; should not escape
mapBodyFacts anal b f = anal (GMany NothingO b NothingO) f >>= bodyFacts
  where -- the type constraint is needed for the pattern match;
        -- if it were not, we would use do-notation here.
    bodyFacts :: (Graph n C C, Fact C f, MaybeO C f) -> FuelMonad (Body n, Fact C f)
    bodyFacts (GMany NothingO body NothingO, fb, NothingO) = return (body, fb)



-- | A utility function so that a transfer function for a first
-- node can be given just a fact; we handle the lookup.  This
-- function is planned to be made obsolete by changes in the dataflow
-- interface.

firstXfer :: Edges n => (n C O -> f -> f) -> (n C O -> FactBase f -> f)
firstXfer xfer n fb = xfer n $ fromJust $ lookupFact fb $ entryLabel n

-- | This utility function handles a common case in which a transfer function
-- produces a single fact out of a last node, which is then distributed
-- over the outgoing edges.
distributeXfer :: Edges n => (n O C -> f -> f) -> (n O C -> f -> FactBase f)
distributeXfer xfer n f = mkFactBase [ (l, xfer n f) | l <- successors n ]

-- | This utility function handles a common case in which a transfer function
-- for a last node takes the incoming fact unchanged and simply distributes
-- that fact over the outgoing edges.
distributeFact :: Edges n => n O C -> f -> FactBase f
distributeFact n f = mkFactBase [ (l, f) | l <- successors n ]

-- | This utility function handles a common case in which a backward transfer
-- function takes the incoming fact unchanged and tags it with the node's label.
distributeFactBwd :: Edges n => n C O -> f -> FactBase f
distributeFactBwd n f = mkFactBase [ (entryLabel n, f) ]

-- | List of (unlabelled) facts from the successors of a last node
successorFacts :: Edges n => n O C -> FactBase f -> [f]
successorFacts n fb = [ f | id <- successors n, let Just f = lookupFact fb id ]


-- | Fold a function over every node in a block, forward or backward.
-- The fold function must be polymorphic in the shape of the nodes.
foldBlockNodesF :: forall n a .
                   (forall e x . n e x       -> a -> a)
                -> (forall e x . Block n e x -> a -> a)
foldBlockNodesB :: forall n a .
                   (forall e x . n e x       -> a -> a)
                -> (forall e x . Block n e x -> a -> a)
-- | Fold a function over every node in a graph.
-- The fold function must be polymorphic in the shape of the nodes.

foldGraphNodes :: forall n a .
                  (forall e x . n e x       -> a -> a)
                -> (forall e x . Graph n e x -> a -> a)

foldBlockNodes' :: forall n a .
                   ((a -> a) -> (a -> a) -> (a -> a))
                -> (forall e x . n e x       -> a -> a)
                -> (forall e x . Block n e x -> a -> a)
foldBlockNodes' cat f = block
  where block :: forall e x . Block n e x -> a -> a
        block (BFirst  node)    = f node
        block (BMiddle node)    = f node
        block (BLast   node)    = f node
        block (b1 `BCat`    b2) = block b1 `cat` block b2
        block (b1 `BClosed` b2) = block b1 `cat` block b2
        block (b1 `BHead` n)    = block b1 `cat` f n
        block (n `BTail` b2)    = f n `cat` block b2
foldBlockNodesF = foldBlockNodes' (\ f f' -> f' . f)
foldBlockNodesB = foldBlockNodes' (\ f f' -> f  . f')

foldGraphNodes f = graph
    where graph :: forall e x . Graph n e x -> a -> a
          lift  :: forall thing ex . (thing -> a -> a) -> (MaybeO ex thing -> a -> a)

          graph GNil              = id
          graph (GUnit b)         = block b
          graph (GMany e b x)     = lift block e . body b . lift block x
          body (BodyEmpty)        = id
          body (BodyUnit b)       = block b
          body (b1 `BodyCat` b2)  = body b1 . body b2
          lift _ NothingO         = id
          lift f (JustO thing)    = f thing

          block = foldBlockNodesF f

                        
