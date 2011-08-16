{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeFamilies  #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Trustworthy #-}
#endif

-- | Utilities for clients of Hoopl, not used internally.

module Compiler.Hoopl.XUtil
  ( firstXfer, distributeXfer
  , distributeFact, distributeFactBwd
  , successorFacts
  , joinFacts
  , joinOutFacts -- deprecated
  , joinMaps
  , foldGraphNodes
  , foldBlockNodesF, foldBlockNodesB, foldBlockNodesF3, foldBlockNodesB3
  , tfFoldBlock
  , ScottBlock(ScottBlock), scottFoldBlock
  , fbnf3
  , blockToNodeList, blockOfNodeList
  , blockToNodeList'   -- alternate version using fold
  , blockToNodeList''  -- alternate version using scottFoldBlock
  , blockToNodeList''' -- alternate version using tfFoldBlock
  , analyzeAndRewriteFwdBody, analyzeAndRewriteBwdBody
  , analyzeAndRewriteFwdOx, analyzeAndRewriteBwdOx
  , noEntries
  , BlockResult(..), lookupBlock
  )
where

import qualified Data.Map as M
import Data.Maybe

import Compiler.Hoopl.Checkpoint
import Compiler.Hoopl.Collections
import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label
import Compiler.Hoopl.Util


-- | Forward dataflow analysis and rewriting for the special case of a Body.
-- A set of entry points must be supplied; blocks not reachable from
-- the set are thrown away.
analyzeAndRewriteFwdBody
   :: forall m n f entries. (CheckpointMonad m, NonLocal n, LabelsPtr entries)
   => FwdPass m n f
   -> entries -> Body n -> FactBase f
   -> m (Body n, FactBase f)

-- | Backward dataflow analysis and rewriting for the special case of a Body.
-- A set of entry points must be supplied; blocks not reachable from
-- the set are thrown away.
analyzeAndRewriteBwdBody
   :: forall m n f entries. (CheckpointMonad m, NonLocal n, LabelsPtr entries)
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
   :: forall m n f x. (CheckpointMonad m, NonLocal n)
   => FwdPass m n f -> Graph n O x -> f -> m (Graph n O x, FactBase f, MaybeO x f)

-- | Backward dataflow analysis and rewriting for the special case of a 
-- graph open at the entry.  This special case relieves the client
-- from having to specify a type signature for 'NothingO', which beginners
-- might find confusing and experts might find annoying.
analyzeAndRewriteBwdOx
   :: forall m n f x. (CheckpointMonad m, NonLocal n)
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

firstXfer :: NonLocal n => (n C O -> f -> f) -> (n C O -> FactBase f -> f)
firstXfer xfer n fb = xfer n $ fromJust $ lookupFact (entryLabel n) fb

-- | This utility function handles a common case in which a transfer function
-- produces a single fact out of a last node, which is then distributed
-- over the outgoing edges.
distributeXfer :: NonLocal n
               => DataflowLattice f -> (n O C -> f -> f) -> (n O C -> f -> FactBase f)
distributeXfer lattice xfer n f =
    mkFactBase lattice [ (l, xfer n f) | l <- successors n ]

-- | This utility function handles a common case in which a transfer function
-- for a last node takes the incoming fact unchanged and simply distributes
-- that fact over the outgoing edges.
distributeFact :: NonLocal n => n O C -> f -> FactBase f
distributeFact n f = mapFromList [ (l, f) | l <- successors n ]
   -- because the same fact goes out on every edge,
   -- there's no need for 'mkFactBase' here.

-- | This utility function handles a common case in which a backward transfer
-- function takes the incoming fact unchanged and tags it with the node's label.
distributeFactBwd :: NonLocal n => n C O -> f -> FactBase f
distributeFactBwd n f = mapSingleton (entryLabel n) f

-- | List of (unlabelled) facts from the successors of a last node
successorFacts :: NonLocal n => n O C -> FactBase f -> [f]
successorFacts n fb = [ f | id <- successors n, let Just f = lookupFact id fb ]

-- | Join a list of facts.
joinFacts :: DataflowLattice f -> Label -> [f] -> f
joinFacts lat inBlock = foldr extend (fact_bot lat)
  where extend new old = snd $ fact_join lat inBlock (OldFact old) (NewFact new)

{-# DEPRECATED joinOutFacts
    "should be replaced by 'joinFacts lat l (successorFacts n f)'; as is, it uses the wrong Label" #-}

joinOutFacts :: (NonLocal node) => DataflowLattice f -> node O C -> FactBase f -> f
joinOutFacts lat n f = foldr join (fact_bot lat) facts
  where join (lbl, new) old = snd $ fact_join lat lbl (OldFact old) (NewFact new)
        facts = [(s, fromJust fact) | s <- successors n, let fact = lookupFact s f, isJust fact]


-- | It's common to represent dataflow facts as a map from variables
-- to some fact about the locations. For these maps, the join
-- operation on the map can be expressed in terms of the join on each
-- element of the codomain:
joinMaps :: Ord k => JoinFun v -> JoinFun (M.Map k v)
joinMaps eltJoin l (OldFact old) (NewFact new) = M.foldrWithKey add (NoChange, old) new
  where 
    add k new_v (ch, joinmap) =
      case M.lookup k joinmap of
        Nothing    -> (SomeChange, M.insert k new_v joinmap)
        Just old_v -> case eltJoin l (OldFact old_v) (NewFact new_v) of
                        (SomeChange, v') -> (SomeChange, M.insert k v' joinmap)
                        (NoChange,   _)  -> (ch, joinmap)



-- | A fold function that relies on the IndexedCO type function.
--   Note that the type parameter e is available to the functions
--   that are applied to the middle and last nodes.
tfFoldBlock :: forall n bc bo c e x .
               ( n C O -> bc
               , n O O -> IndexedCO e bc bo -> IndexedCO e bc bo
               , n O C -> IndexedCO e bc bo -> c)
            -> (Block n e x -> bo -> IndexedCO x c (IndexedCO e bc bo))
tfFoldBlock (f, m, l) bl bo = block bl
  where block :: forall x . Block n e x -> IndexedCO x c (IndexedCO e bc bo)
        block (BFirst  n)       = f n
        block (BMiddle n)       = m n bo
        block (BLast   n)       = l n bo
        block (b1 `BCat`    b2) = oblock b2 $ block b1
        block (b1 `BClosed` b2) = oblock b2 $ block b1
        block (b1 `BHead` n)    = m n $ block b1
        block (n `BTail` b2)    = oblock b2 $ m n bo
        oblock :: forall x . Block n O x -> IndexedCO e bc bo -> IndexedCO x c (IndexedCO e bc bo)
        oblock (BMiddle n)       = m n
        oblock (BLast   n)       = l n
        oblock (b1 `BCat`    b2) = oblock b1 `cat` oblock b2
        oblock (n `BTail` b2)    = m n       `cat` oblock b2
        cat :: forall b c a. (a -> b) -> (b -> c) -> a -> c
        cat f f' = f' . f


type NodeList' e x n = (MaybeC e (n C O), [n O O], MaybeC x (n O C))
blockToNodeList''' ::
  forall n e x. ( IndexedCO e (NodeList' C O n) (NodeList' O O n) ~ NodeList' e O n
                , IndexedCO x (NodeList' e C n) (NodeList' e O n) ~ NodeList' e x n) =>
    Block n e x -> NodeList' e x n
blockToNodeList''' b = (h, reverse ms', t)
  where
    (h, ms', t) = tfFoldBlock (f, m, l) b z
    z :: NodeList' O O n
    z = (NothingC, [], NothingC)
    f :: n C O -> NodeList' C O n
    f n = (JustC n,  [], NothingC)
    m n (h, ms', t) = (h, n : ms', t)
    l n (h, ms', _) = (h, ms', JustC n)


{-
data EitherCO' ex a b where
  LeftCO  :: a -> EitherCO' C a b
  RightCO :: b -> EitherCO' O a b
-}

  -- should be done with a *backward* fold

-- | More general fold

_unused :: Int
_unused = 3
  where _a = foldBlockNodesF3'' (Trips undefined undefined undefined)
        _b = foldBlockNodesF3'

data Trips n a b c = Trips { ff :: forall e . MaybeC e (n C O) -> a -> b
                           , fm :: n O O            -> b -> b
                           , fl :: forall x . MaybeC x (n O C) -> b -> c
                           }

foldBlockNodesF3'' :: forall n a b c .
                      Trips n a b c -> (forall e x . Block n e x -> a -> c)
foldBlockNodesF3'' trips = block
  where block :: Block n e x -> a -> c
        block (b1 `BClosed` b2) = foldCO b1 `cat` foldOC b2
        block (BFirst  node)    = ff trips (JustC node)  `cat` missingLast
        block (b @ BHead {})    = foldCO b `cat` missingLast
        block (BMiddle node)    = missingFirst `cat` fm trips node  `cat` missingLast
        block (b @ BCat {})     = missingFirst `cat` foldOO b `cat` missingLast
        block (BLast   node)    = missingFirst `cat` fl trips (JustC node)
        block (b @ BTail {})    = missingFirst `cat` foldOC b
        missingLast = fl trips NothingC
        missingFirst = ff trips NothingC
        foldCO :: Block n C O -> a -> b
        foldOO :: Block n O O -> b -> b
        foldOC :: Block n O C -> b -> c
        foldCO (BFirst n)   = ff trips (JustC n)
        foldCO (BHead b n)  = foldCO b `cat` fm trips n
        foldOO (BMiddle n)  = fm trips n
        foldOO (BCat b1 b2) = foldOO b1 `cat` foldOO b2
        foldOC (BLast n)    = fl trips (JustC n)
        foldOC (BTail n b)  = fm trips n `cat` foldOC b
        cat :: forall b c a. (a -> b) -> (b -> c) -> a -> c
        f `cat` g = g . f 

data ScottBlock n a = ScottBlock
   { sb_first :: n C O -> a C O
   , sb_mid   :: n O O -> a O O
   , sb_last  :: n O C -> a O C
   , sb_cat   :: forall e x . a e O -> a O x -> a e x
   }

scottFoldBlock :: forall n a e x . ScottBlock n a -> Block n e x -> a e x
scottFoldBlock funs = block
  where block :: forall e x . Block n e x -> a e x
        block (BFirst n)  = sb_first  funs n
        block (BMiddle n) = sb_mid    funs n
        block (BLast   n) = sb_last   funs n
        block (BClosed b1 b2) = block b1 `cat` block b2
        block (BCat    b1 b2) = block b1 `cat` block b2
        block (BHead   b  n)  = block b  `cat` sb_mid funs n
        block (BTail   n  b)  = sb_mid funs n `cat` block b
        cat :: forall e x. a e O -> a O x -> a e x
        cat = sb_cat funs

newtype NodeList n e x
    = NL { unList :: (MaybeC e (n C O), [n O O] -> [n O O], MaybeC x (n O C)) }

fbnf3 :: forall n a b c .
         ( n C O       -> a -> b
         , n O O       -> b -> b
         , n O C       -> b -> c)
      -> (forall e x . Block n e x -> IndexedCO e a b -> IndexedCO x c b)
fbnf3 (ff, fm, fl) block = unFF3 $ scottFoldBlock (ScottBlock f m l cat) block
    where f n = FF3 $ ff n
          m n = FF3 $ fm n
          l n = FF3 $ fl n
          -- XXX Ew.
          cat :: forall t t1 t2 t3 t4 t5 t6 t7 t8 t9 a b c e x.
                 (IndexedCO x c b ~ IndexedCO t9 t7 t6,
                  IndexedCO t8 t5 t6 ~ IndexedCO t4 t2 t1,
                  IndexedCO t3 t t1 ~ IndexedCO e a b) =>
                 FF3 t t1 t2 t3 t4 -> FF3 t5 t6 t7 t8 t9 -> FF3 a b c e x
          FF3 f `cat` FF3 f' = FF3 $ f' . f

newtype FF3 a b c e x = FF3 { unFF3 :: IndexedCO e a b -> IndexedCO x c b }

blockToNodeList'' :: Block n e x -> (MaybeC e (n C O), [n O O], MaybeC x (n O C))
blockToNodeList'' = finish . unList . scottFoldBlock (ScottBlock f m l cat)
    where f n = NL (JustC n, id, NothingC)
          m n = NL (NothingC, (n:), NothingC)
          l n = NL (NothingC, id, JustC n)
          cat :: forall n t1 t3. NodeList n t1 O -> NodeList n O t3 -> NodeList n t1 t3
          NL (e, ms, NothingC) `cat` NL (NothingC, ms', x) = NL (e, ms . ms', x)
          finish :: forall t t1 t2 a. (t, [a] -> t1, t2) -> (t, t1, t2)
          finish (e, ms, x) = (e, ms [], x)



blockToNodeList' :: Block n e x -> (MaybeC e (n C O), [n O O], MaybeC x (n O C))
blockToNodeList' b = unFNL $ foldBlockNodesF3''' ff fm fl b ()
  where ff :: forall n e. MaybeC e (n C O) -> () -> PNL n e
        fm :: forall n e. n O O -> PNL n e -> PNL n e
        fl :: forall n e x. MaybeC x (n O C) -> PNL n e -> FNL n e x
        ff n () = PNL (n, [])
        fm n (PNL (first, mids')) = PNL (first, n : mids')
        fl n (PNL (first, mids')) = FNL (first, reverse mids', n)

   -- newtypes for 'partial node list' and 'final node list'
newtype PNL n e   = PNL (MaybeC e (n C O), [n O O])
newtype FNL n e x = FNL {unFNL :: (MaybeC e (n C O), [n O O], MaybeC x (n O C))}

foldBlockNodesF3''' :: forall n a b c .
                       (forall e   . MaybeC e (n C O) -> a   -> b e)
                    -> (forall e   .           n O O  -> b e -> b e)
                    -> (forall e x . MaybeC x (n O C) -> b e -> c e x)
                    -> (forall e x . Block n e x      -> a   -> c e x)
foldBlockNodesF3''' ff fm fl = block
  where block   :: forall e x . Block n e x -> a   -> c e x
        blockCO ::              Block n C O -> a   -> b C
        blockOO :: forall e .   Block n O O -> b e -> b e
        blockOC :: forall e .   Block n O C -> b e -> c e C
        block (b1 `BClosed` b2) = blockCO b1       `cat` blockOC b2
        block (BFirst  node)    = ff (JustC node)  `cat` fl NothingC
        block (b @ BHead {})    = blockCO b        `cat` fl NothingC
        block (BMiddle node)    = ff NothingC `cat` fm node   `cat` fl NothingC
        block (b @ BCat {})     = ff NothingC `cat` blockOO b `cat` fl NothingC
        block (BLast   node)    = ff NothingC `cat` fl (JustC node)
        block (b @ BTail {})    = ff NothingC `cat` blockOC b
        blockCO (BFirst n)      = ff (JustC n)
        blockCO (BHead b n)     = blockCO b `cat` fm n
        blockOO (BMiddle n)     = fm n
        blockOO (BCat b1 b2)    = blockOO b1 `cat` blockOO b2
        blockOC (BLast n)       = fl (JustC n)
        blockOC (BTail n b)     = fm n `cat` blockOC b
        cat :: forall a b c. (a -> b) -> (b -> c) -> a -> c
        f `cat` g = g . f 


-- | The following function is easy enough to define but maybe not so useful
foldBlockNodesF3' :: forall n a b c .
                   ( n C O -> a -> b
                   , n O O -> b -> b
                   , n O C -> b -> c)
                   -> (a -> b) -- called iff there is no first node
                   -> (b -> c) -- called iff there is no last node
                   -> (forall e x . Block n e x -> a -> c)
foldBlockNodesF3' (ff, fm, fl) missingFirst missingLast = block
  where block   :: forall e x . Block n e x -> a -> c
        blockCO ::              Block n C O -> a -> b
        blockOO ::              Block n O O -> b -> b
        blockOC ::              Block n O C -> b -> c
        block (b1 `BClosed` b2) = blockCO b1 `cat` blockOC b2
        block (BFirst  node)    = ff node  `cat` missingLast
        block (b @ BHead {})    = blockCO b `cat` missingLast
        block (BMiddle node)    = missingFirst `cat` fm node  `cat` missingLast
        block (b @ BCat {})     = missingFirst `cat` blockOO b `cat` missingLast
        block (BLast   node)    = missingFirst `cat` fl node
        block (b @ BTail {})    = missingFirst `cat` blockOC b
        blockCO (BFirst n)   = ff n
        blockCO (BHead b n)  = blockCO b `cat` fm n
        blockOO (BMiddle n)  = fm n
        blockOO (BCat b1 b2) = blockOO b1 `cat` blockOO b2
        blockOC (BLast n)    = fl n
        blockOC (BTail n b)  = fm n `cat` blockOC b
        cat :: forall a b c. (a -> b) -> (b -> c) -> a -> c
        f `cat` g = g . f 

-- | Fold a function over every node in a block, forward or backward.
-- The fold function must be polymorphic in the shape of the nodes.
foldBlockNodesF3 :: forall n a b c .
                   ( n C O       -> a -> b
                   , n O O       -> b -> b
                   , n O C       -> b -> c)
                 -> (forall e x . Block n e x -> IndexedCO e a b -> IndexedCO x c b)
foldBlockNodesF  :: forall n a .
                    (forall e x . n e x       -> a -> a)
                 -> (forall e x . Block n e x -> IndexedCO e a a -> IndexedCO x a a)
foldBlockNodesB3 :: forall n a b c .
                   ( n C O       -> b -> c
                   , n O O       -> b -> b
                   , n O C       -> a -> b)
                 -> (forall e x . Block n e x -> IndexedCO x a b -> IndexedCO e c b)
foldBlockNodesB  :: forall n a .
                    (forall e x . n e x       -> a -> a)
                 -> (forall e x . Block n e x -> IndexedCO x a a -> IndexedCO e a a)
-- | Fold a function over every node in a graph.
-- The fold function must be polymorphic in the shape of the nodes.

foldGraphNodes :: forall n a .
                  (forall e x . n e x       -> a -> a)
               -> (forall e x . Graph n e x -> a -> a)


foldBlockNodesF3 (ff, fm, fl) = block
  where block :: forall e x . Block n e x -> IndexedCO e a b -> IndexedCO x c b
        block (BFirst  node)    = ff node
        block (BMiddle node)    = fm node
        block (BLast   node)    = fl node
        block (b1 `BCat`    b2) = block b1 `cat` block b2
        block (b1 `BClosed` b2) = block b1 `cat` block b2
        block (b1 `BHead` n)    = block b1 `cat` fm n
        block (n `BTail` b2)    = fm n `cat` block b2
        cat :: forall a b c. (a -> b) -> (b -> c) -> a -> c
        cat f f' = f' . f
foldBlockNodesF f = foldBlockNodesF3 (f, f, f)

foldBlockNodesB3 (ff, fm, fl) = block
  where block :: forall e x . Block n e x -> IndexedCO x a b -> IndexedCO e c b
        block (BFirst  node)    = ff node
        block (BMiddle node)    = fm node
        block (BLast   node)    = fl node
        block (b1 `BCat`    b2) = block b1 `cat` block b2
        block (b1 `BClosed` b2) = block b1 `cat` block b2
        block (b1 `BHead` n)    = block b1 `cat` fm n
        block (n `BTail` b2)    = fm n `cat` block b2
        cat :: forall a b c. (b -> c) -> (a -> b) -> a -> c
        cat f f' = f . f'
foldBlockNodesB f = foldBlockNodesB3 (f, f, f)


foldGraphNodes f = graph
    where graph :: forall e x . Graph n e x -> a -> a
          lift  :: forall thing ex . (thing -> a -> a) -> (MaybeO ex thing -> a -> a)

          graph GNil              = id
          graph (GUnit b)         = block b
          graph (GMany e b x)     = lift block e . body b . lift block x
          body :: Body n -> a -> a
          body bdy                = \a -> mapFold block a bdy
          lift _ NothingO         = id
          lift f (JustO thing)    = f thing

          block :: Block n e x -> IndexedCO e a a -> IndexedCO x a a
          block = foldBlockNodesF f

{-# DEPRECATED blockToNodeList, blockOfNodeList 
  "What justifies these functions?  Can they be eliminated?  Replaced with folds?" #-}



-- | Convert a block to a list of nodes. The entry and exit node
-- is or is not present depending on the shape of the block.
--
-- The blockToNodeList function cannot be currently expressed using
-- foldBlockNodesB, because it returns IndexedCO e a b, which means
-- two different types depending on the shape of the block entry.
-- But blockToNodeList returns one of four possible types, depending
-- on the shape of the block entry *and* exit.
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

lookupBlock :: NonLocal n => Graph n e x -> Label -> BlockResult n x
lookupBlock (GMany _ _ (JustO exit)) lbl
  | entryLabel exit == lbl = ExitBlock exit
lookupBlock (GMany _ body _) lbl =
  case mapLookup lbl body of
    Just b  -> BodyBlock b
    Nothing -> NoBlock
lookupBlock GNil      _ = NoBlock
lookupBlock (GUnit _) _ = NoBlock
