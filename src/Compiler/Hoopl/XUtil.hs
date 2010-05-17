{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

-- | Utilities for clients of Hoopl, not used internally.

module Compiler.Hoopl.XUtil
  ( firstXfer, distributeXfer
  , distributeFact, distributeFactBwd
  , successorFacts
  , joinFacts
  , joinOutFacts -- deprecated
  , foldGraphNodes, foldBlockNodesF, foldBlockNodesB, foldBlockNodesF3, foldBlockNodesB3
  , blockToNodeList, blockOfNodeList
  , analyzeAndRewriteFwdBody, analyzeAndRewriteBwdBody
  , analyzeAndRewriteFwdOx, analyzeAndRewriteBwdOx
  , noEntries
  , BlockResult(..), lookupBlock
  )
where

import Data.Maybe

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Fuel
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label
import Compiler.Hoopl.Util


-- | Forward dataflow analysis and rewriting for the special case of a Body.
-- A set of entry points must be supplied; blocks not reachable from
-- the set are thrown away.
analyzeAndRewriteFwdBody
   :: forall m n f entries. (FuelMonad m, Edges n, LabelsPtr entries)
   => FwdPass m n f
   -> entries -> Body n -> FactBase f
   -> m (Body n, FactBase f)

-- | Backward dataflow analysis and rewriting for the special case of a Body.
-- A set of entry points must be supplied; blocks not reachable from
-- the set are thrown away.
analyzeAndRewriteBwdBody
   :: forall m n f entries. (FuelMonad m, Edges n, LabelsPtr entries)
   => BwdPass m n f 
   -> entries -> Body n -> FactBase f 
   -> m (Body n, FactBase f)

analyzeAndRewriteFwdBody pass en = mapBodyFacts (analyzeAndRewriteFwd pass (JustC en))
analyzeAndRewriteBwdBody pass en = mapBodyFacts (analyzeAndRewriteBwd pass (JustC en))

mapBodyFacts :: (Monad m)
    => (Graph n C C -> Fact C f   -> m (Graph n C C, Fact C f, MaybeO C f))
    -> (Body n      -> FactBase f -> m (Body n, FactBase f))
-- ^ Internal utility; should not escape
mapBodyFacts anal b f = anal (GMany NothingO b NothingO) f >>= bodyFacts
  where -- the type constraint is needed for the pattern match;
        -- if it were not, we would use do-notation here.
    bodyFacts :: Monad m => (Graph n C C, Fact C f, MaybeO C f) -> m (Body n, Fact C f)
    bodyFacts (GMany NothingO body NothingO, fb, NothingO) = return (body, fb)

{-
  Can't write:

     do (GMany NothingO body NothingO, fb, NothingO) <- anal (....) f
        return (body, fb)

  because we need an explicit type signature in order to do the GADT
  pattern matches on NothingO
-}



-- | Forward dataflow analysis and rewriting for the special case of a 
-- graph open at the entry.  This special case relieves the client
-- from having to specify a type signature for 'NothingO', which beginners
-- might find confusing and experts might find annoying.
analyzeAndRewriteFwdOx
   :: forall m n f x. (FuelMonad m, Edges n)
   => FwdPass m n f -> Graph n O x -> f -> m (Graph n O x, FactBase f, MaybeO x f)

-- | Backward dataflow analysis and rewriting for the special case of a 
-- graph open at the entry.  This special case relieves the client
-- from having to specify a type signature for 'NothingO', which beginners
-- might find confusing and experts might find annoying.
analyzeAndRewriteBwdOx
   :: forall m n f x. (FuelMonad m, Edges n)
   => BwdPass m n f -> Graph n O x -> Fact x f -> m (Graph n O x, FactBase f, f)

-- | A value that can be used for the entry point of a graph open at the entry.
noEntries :: MaybeC O Label
noEntries = NothingC

analyzeAndRewriteFwdOx pass g f  = analyzeAndRewriteFwd pass noEntries g f
analyzeAndRewriteBwdOx pass g fb = analyzeAndRewriteBwd pass noEntries g fb >>= strip
  where strip :: forall m a b c . Monad m => (a, b, MaybeO O c) -> m (a, b, c)
        strip (a, b, JustO c) = return (a, b, c)





-- | A utility function so that a transfer function for a first
-- node can be given just a fact; we handle the lookup.  This
-- function is planned to be made obsolete by changes in the dataflow
-- interface.

firstXfer :: Edges n => (n C O -> f -> f) -> (n C O -> FactBase f -> f)
firstXfer xfer n fb = xfer n $ fromJust $ lookupFact (entryLabel n) fb

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
successorFacts n fb = [ f | id <- successors n, let Just f = lookupFact id fb ]

-- | Join a list of facts.
joinFacts :: DataflowLattice f -> Label -> [f] -> f
joinFacts lat inBlock = foldr extend (fact_bot lat)
  where extend new old = snd $ fact_extend lat inBlock (OldFact old) (NewFact new)

{-# DEPRECATED joinOutFacts
    "should be replaced by 'joinFacts lat l (successorFacts n f)'; as is, it uses the wrong Label" #-}

joinOutFacts :: (Edges node) => DataflowLattice f -> node O C -> FactBase f -> f
joinOutFacts lat n f = foldr extend (fact_bot lat) facts
  where extend (lbl, new) old = snd $ fact_extend lat lbl (OldFact old) (NewFact new)
        facts = [(s, fromJust fact) | s <- successors n, let fact = lookupFact s f, isJust fact]




-- | Fold a function over every node in a block, forward or backward.
-- The fold function must be polymorphic in the shape of the nodes.
foldBlockNodesF3 :: forall n a b c .
                   ( n C O       -> a -> b
                   , n O O       -> b -> b
                   , n O C       -> b -> c)
                 -> (forall e x . Block n e x -> EitherCO e a b -> EitherCO x c b)
foldBlockNodesF  :: forall n a .
                    (forall e x . n e x       -> a -> a)
                 -> (forall e x . Block n e x -> EitherCO e a a -> EitherCO x a a)
foldBlockNodesB3 :: forall n a b c .
                   ( n C O       -> b -> c
                   , n O O       -> b -> b
                   , n O C       -> a -> b)
                 -> (forall e x . Block n e x -> EitherCO x a b -> EitherCO e c b)
foldBlockNodesB  :: forall n a .
                    (forall e x . n e x       -> a -> a)
                 -> (forall e x . Block n e x -> EitherCO x a a -> EitherCO e a a)
-- | Fold a function over every node in a graph.
-- The fold function must be polymorphic in the shape of the nodes.

foldGraphNodes :: forall n a .
                  (forall e x . n e x       -> a -> a)
               -> (forall e x . Graph n e x -> a -> a)


foldBlockNodesF3 (ff, fm, fl) = block
  where block :: forall e x . Block n e x -> EitherCO e a b -> EitherCO x c b
        block (BFirst  node)    = ff node
        block (BMiddle node)    = fm node
        block (BLast   node)    = fl node
        block (b1 `BCat`    b2) = block b1 `cat` block b2
        block (b1 `BClosed` b2) = block b1 `cat` block b2
        block (b1 `BHead` n)    = block b1 `cat` fm n
        block (n `BTail` b2)    = fm n `cat` block b2
        cat f f' = f' . f
foldBlockNodesF f = foldBlockNodesF3 (f, f, f)

foldBlockNodesB3 (ff, fm, fl) = block
  where block :: forall e x . Block n e x -> EitherCO x a b -> EitherCO e c b
        block (BFirst  node)    = ff node
        block (BMiddle node)    = fm node
        block (BLast   node)    = fl node
        block (b1 `BCat`    b2) = block b1 `cat` block b2
        block (b1 `BClosed` b2) = block b1 `cat` block b2
        block (b1 `BHead` n)    = block b1 `cat` fm n
        block (n `BTail` b2)    = fm n `cat` block b2
        cat f f' = f . f'
foldBlockNodesB f = foldBlockNodesB3 (f, f, f)


foldGraphNodes f = graph
    where graph :: forall e x . Graph n e x -> a -> a
          lift  :: forall thing ex . (thing -> a -> a) -> (MaybeO ex thing -> a -> a)

          graph GNil              = id
          graph (GUnit b)         = block b
          graph (GMany e b x)     = lift block e . body b . lift block x
          body :: Body n -> a -> a
          body  (Body bdy)        = \a -> mapFold block a bdy
          lift _ NothingO         = id
          lift f (JustO thing)    = f thing

          block = foldBlockNodesF f

{-# DEPRECATED blockToNodeList, blockOfNodeList 
  "What justifies these functions?  Can they be eliminated?  Replaced with folds?" #-}



-- | Convert a block to a list of nodes. The entry and exit node
-- is or is not present depending on the shape of the block.
blockToNodeList :: Block n e x -> (MaybeC e (n C O), [n O O], MaybeC x (n O C))
blockToNodeList block = case block of
  BFirst n    -> (JustC n, [], NothingC)
  BMiddle n   -> (NothingC, [n], NothingC)
  BLast n     -> (NothingC, [], JustC n)
  BCat {}     -> (NothingC, foldOO block [], NothingC)
  BHead x n   -> case foldCO x [n] of (f, m) -> (f, m, NothingC)
  BTail n x   -> case foldOC x of (m, l) -> (NothingC, n : m, l)
  BClosed x y -> case foldOC y of (m, l) -> case foldCO x m of (f, m') -> (f, m', l)
  where foldCO :: Block n C O -> [n O O] -> (MaybeC C (n C O), [n O O])
        foldCO (BFirst n) m  = (JustC n, m)
        foldCO (BHead x n) m = foldCO x (n : m)

        foldOO :: Block n O O -> [n O O] -> [n O O]
        foldOO (BMiddle n) acc = n : acc
        foldOO (BCat x y) acc  = foldOO x $ foldOO y acc

        foldOC :: Block n O C -> ([n O O], MaybeC C (n O C))
        foldOC (BLast n)   = ([], JustC n)
        foldOC (BTail n x) = case foldOC x of (m, l) -> (n : m, l)

-- | Convert a list of nodes to a block. The entry and exit node
-- must or must not be present depending on the shape of the block.
blockOfNodeList :: (MaybeC e (n C O), [n O O], MaybeC x (n O C)) -> Block n e x
blockOfNodeList (NothingC, [], NothingC) = error "No nodes to created block from in blockOfNodeList"
blockOfNodeList (NothingC, m, NothingC)  = foldr1 BCat (map BMiddle m)
blockOfNodeList (NothingC, m, JustC l)   = foldr BTail (BLast l) m
blockOfNodeList (JustC f, m, NothingC)   = foldl BHead (BFirst f) m
blockOfNodeList (JustC f, m, JustC l)    = BClosed (BFirst f) $ foldr BTail (BLast l) m

data BlockResult n x where
  NoBlock   :: BlockResult n x
  BodyBlock :: Block n C C -> BlockResult n x
  ExitBlock :: Block n C O -> BlockResult n O

lookupBlock :: Edges n => Graph n e x -> Label -> BlockResult n x
lookupBlock (GMany _ _ (JustO exit)) lbl
  | entryLabel exit == lbl = ExitBlock exit
lookupBlock (GMany _ (Body body)  _) lbl =
  case mapLookup lbl body of
    Just b  -> BodyBlock b
    Nothing -> NoBlock
lookupBlock GNil      _ = NoBlock
lookupBlock (GUnit _) _ = NoBlock
