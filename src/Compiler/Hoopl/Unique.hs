module Compiler.Hoopl.Unique
  ( Unique
  , intOfUniq, uniqOfInt -- exposed through GHC module only!
  , HooplMonad(..)
  , SimpleHooplMonad, runSimpleHooplMonad
  , HooplMonadT, runHooplMonadT
  )

where

-----------------------------------------------------------------------------
--		Unique
-----------------------------------------------------------------------------

data Unique = Unique { intOfUniq ::  {-# UNPACK #-} !Int }
  deriving (Eq, Ord)

uniqOfInt :: Int -> Unique
uniqOfInt = Unique

instance Show Unique where
  show (Unique n) = show n

class Monad m => HooplMonad m where
  freshUnique :: m Unique

----------------------------------------------------------------

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
