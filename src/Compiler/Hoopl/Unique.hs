{-# LANGUAGE TypeFamilies #-}
module Compiler.Hoopl.Unique
  ( Unique, mkUnique
  , UniqueSet, UniqueMap
  , HooplMonad(..)
  , SimpleHooplMonad, runSimpleHooplMonad
  , HooplMonadT, runHooplMonadT

  , uniqueToInt -- exposed through GHC module only!
  )

where

import Compiler.Hoopl.Collections

import qualified Data.IntMap as M
import qualified Data.IntSet as S

-----------------------------------------------------------------------------
--		Unique
-----------------------------------------------------------------------------

data Unique = Unique { uniqueToInt ::  {-# UNPACK #-} !Int }
  deriving (Eq, Ord)

mkUnique :: Int -> Unique
mkUnique = Unique

instance Show Unique where
  show (Unique n) = show n

-----------------------------------------------------------------------------
-- UniqueSet

newtype UniqueSet = US S.IntSet deriving (Eq, Ord, Show)

instance IsSet UniqueSet where
  type KeySet UniqueSet = Unique

  nullSet (US s) = S.null s
  sizeSet (US s) = S.size s
  memberSet (Unique k) (US s) = S.member k s

  emptySet = US S.empty
  singletonSet (Unique k) = US (S.singleton k)
  insertSet (Unique k) (US s) = US (S.insert k s)
  deleteSet (Unique k) (US s) = US (S.delete k s)

  unionSet (US x) (US y) = US (S.union x y)
  differenceSet (US x) (US y) = US (S.difference x y)
  intersectionSet (US x) (US y) = US (S.intersection x y)
  isSubsetOfSet (US x) (US y) = S.isSubsetOf x y

  foldSet k z (US s) = S.fold (k . mkUnique) z s

  elemsSet (US s) = map mkUnique (S.elems s)
  fromListSet ks = US (S.fromList (map uniqueToInt ks))

-----------------------------------------------------------------------------
-- UniqueMap

newtype UniqueMap v = UM (M.IntMap v) deriving (Eq, Ord, Show)

instance IsMap UniqueMap where
  type KeyMap UniqueMap = Unique

  nullMap (UM m) = M.null m
  sizeMap (UM m) = M.size m
  memberMap (Unique k) (UM m) = M.member k m
  lookupMap (Unique k) (UM m) = M.lookup k m
  findWithDefaultMap def (Unique k) (UM m) = M.findWithDefault def k m

  emptyMap = UM M.empty
  singletonMap (Unique k) v = UM (M.singleton k v)
  insertMap (Unique k) v (UM m) = UM (M.insert k v m)
  deleteMap (Unique k) (UM m) = UM (M.delete k m)

  unionMap (UM x) (UM y) = UM (M.union x y)
  unionWithKeyMap f (UM x) (UM y) = UM (M.unionWithKey (f . mkUnique) x y)
  differenceMap (UM x) (UM y) = UM (M.difference x y)
  intersectionMap (UM x) (UM y) = UM (M.intersection x y)
  isSubmapOfMap (UM x) (UM y) = M.isSubmapOf x y

  mapMap f (UM m) = UM (M.map f m)
  mapWithKeyMap f (UM m) = UM (M.mapWithKey (f . mkUnique) m)
  foldMap k z (UM m) = M.fold k z m
  foldWithKeyMap k z (UM m) = M.foldWithKey (k . mkUnique) z m

  elemsMap (UM m) = M.elems m
  keysMap (UM m) = map mkUnique (M.keys m)
  toListMap (UM m) = [(mkUnique k, v) | (k, v) <- M.toList m]
  fromListMap assocs = UM (M.fromList [(uniqueToInt k, v) | (k, v) <- assocs])

----------------------------------------------------------------
-- Monads

class Monad m => HooplMonad m where
  freshUnique :: m Unique

newtype SimpleHooplMonad a = SHM { unSHM :: [Unique] -> (a, [Unique]) }

instance Monad SimpleHooplMonad where
  return a = SHM $ \us -> (a, us)
  m >>= k  = SHM $ \us -> let (a, us') = unSHM m us in
                              unSHM (k a) us'

instance HooplMonad SimpleHooplMonad where
  freshUnique = SHM $ \(u:us) -> (u, us)

runSimpleHooplMonad :: SimpleHooplMonad a -> a
runSimpleHooplMonad m = fst (unSHM m allUniques)

----------------------------------------------------------------

newtype HooplMonadT m a = HM { unHM :: [Unique] -> m (a, [Unique]) }

instance Monad m => Monad (HooplMonadT m) where
  return a = HM $ \us -> return (a, us)
  m >>= k  = HM $ \us -> do { (a, us') <- unHM m us; unHM (k a) us' }

instance Monad m => HooplMonad (HooplMonadT m) where
  freshUnique = HM $ \(u:us) -> return (u, us)

runHooplMonadT :: Monad m => HooplMonadT m a -> m a
runHooplMonadT m = do { (a, _) <- unHM m allUniques; return a }

allUniques :: [Unique]
allUniques = map Unique [1..]
