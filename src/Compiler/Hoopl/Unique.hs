{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Trustworthy #-}
#endif

module Compiler.Hoopl.Unique
  ( Unique, intToUnique
  , UniqueSet, UniqueMap
  , UniqueMonad(..)
  , SimpleUniqueMonad, runSimpleUniqueMonad
  , UniqueMonadT, runUniqueMonadT

  , uniqueToInt -- exposed through GHC module only!
  )

where

import Compiler.Hoopl.Checkpoint
import Compiler.Hoopl.Collections

import qualified Data.IntMap as M
import qualified Data.IntSet as S

-----------------------------------------------------------------------------
--		Unique
-----------------------------------------------------------------------------

data Unique = Unique { uniqueToInt ::  {-# UNPACK #-} !Int }
  deriving (Eq, Ord)

intToUnique :: Int -> Unique
intToUnique = Unique

instance Show Unique where
  show (Unique n) = show n

-----------------------------------------------------------------------------
-- UniqueSet

newtype UniqueSet = US S.IntSet deriving (Eq, Ord, Show)

instance IsSet UniqueSet where
  type ElemOf UniqueSet = Unique

  setNull (US s) = S.null s
  setSize (US s) = S.size s
  setMember (Unique k) (US s) = S.member k s

  setEmpty = US S.empty
  setSingleton (Unique k) = US (S.singleton k)
  setInsert (Unique k) (US s) = US (S.insert k s)
  setDelete (Unique k) (US s) = US (S.delete k s)

  setUnion (US x) (US y) = US (S.union x y)
  setDifference (US x) (US y) = US (S.difference x y)
  setIntersection (US x) (US y) = US (S.intersection x y)
  setIsSubsetOf (US x) (US y) = S.isSubsetOf x y

  setFold k z (US s) = S.fold (k . intToUnique) z s

  setElems (US s) = map intToUnique (S.elems s)
  setFromList ks = US (S.fromList (map uniqueToInt ks))

-----------------------------------------------------------------------------
-- UniqueMap

newtype UniqueMap v = UM (M.IntMap v) deriving (Eq, Ord, Show)

instance IsMap UniqueMap where
  type KeyOf UniqueMap = Unique

  mapNull (UM m) = M.null m
  mapSize (UM m) = M.size m
  mapMember (Unique k) (UM m) = M.member k m
  mapLookup (Unique k) (UM m) = M.lookup k m
  mapFindWithDefault def (Unique k) (UM m) = M.findWithDefault def k m

  mapEmpty = UM M.empty
  mapSingleton (Unique k) v = UM (M.singleton k v)
  mapInsert (Unique k) v (UM m) = UM (M.insert k v m)
  mapDelete (Unique k) (UM m) = UM (M.delete k m)

  mapUnion (UM x) (UM y) = UM (M.union x y)
  mapUnionWithKey f (UM x) (UM y) = UM (M.unionWithKey (f . intToUnique) x y)
  mapDifference (UM x) (UM y) = UM (M.difference x y)
  mapIntersection (UM x) (UM y) = UM (M.intersection x y)
  mapIsSubmapOf (UM x) (UM y) = M.isSubmapOf x y

  mapMap f (UM m) = UM (M.map f m)
  mapMapWithKey f (UM m) = UM (M.mapWithKey (f . intToUnique) m)
  mapFold k z (UM m) = M.fold k z m
  mapFoldWithKey k z (UM m) = M.foldWithKey (k . intToUnique) z m

  mapElems (UM m) = M.elems m
  mapKeys (UM m) = map intToUnique (M.keys m)
  mapToList (UM m) = [(intToUnique k, v) | (k, v) <- M.toList m]
  mapFromList assocs = UM (M.fromList [(uniqueToInt k, v) | (k, v) <- assocs])

----------------------------------------------------------------
-- Monads

class Monad m => UniqueMonad m where
  freshUnique :: m Unique

newtype SimpleUniqueMonad a = SUM { unSUM :: [Unique] -> (a, [Unique]) }

instance Monad SimpleUniqueMonad where
  return a = SUM $ \us -> (a, us)
  m >>= k  = SUM $ \us -> let (a, us') = unSUM m us in
                              unSUM (k a) us'

instance UniqueMonad SimpleUniqueMonad where
  freshUnique = SUM $ f
    where f (u:us) = (u, us)
          f _ = error "Unique.freshUnique(SimpleUniqueMonad): empty list"

instance CheckpointMonad SimpleUniqueMonad where
  type Checkpoint SimpleUniqueMonad = [Unique]
  checkpoint = SUM $ \us -> (us, us)
  restart us = SUM $ \_  -> ((), us)

runSimpleUniqueMonad :: SimpleUniqueMonad a -> a
runSimpleUniqueMonad m = fst (unSUM m allUniques)

----------------------------------------------------------------

newtype UniqueMonadT m a = UMT { unUMT :: [Unique] -> m (a, [Unique]) }

instance Monad m => Monad (UniqueMonadT m) where
  return a = UMT $ \us -> return (a, us)
  m >>= k  = UMT $ \us -> do { (a, us') <- unUMT m us; unUMT (k a) us' }

instance Monad m => UniqueMonad (UniqueMonadT m) where
  freshUnique = UMT $ f
    where f (u:us) = return (u, us)
          f _ = error "Unique.freshUnique(UniqueMonadT): empty list"

runUniqueMonadT :: Monad m => UniqueMonadT m a -> m a
runUniqueMonadT m = do { (a, _) <- unUMT m allUniques; return a }

allUniques :: [Unique]
allUniques = map Unique [1..]
