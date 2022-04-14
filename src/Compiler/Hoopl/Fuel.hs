{-# LANGUAGE CPP, TypeFamilies #-}
{-# LANGUAGE DerivingVia #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif

-----------------------------------------------------------------------------
--		The fuel monad
-----------------------------------------------------------------------------

module Compiler.Hoopl.Fuel
  ( Fuel, infiniteFuel, fuelRemaining
  , withFuel
  , FuelMonad(..)
  , FuelMonadT(..)
  , CheckingFuelMonad
  , InfiniteFuelMonad
  , SimpleFuelMonad
  )
where

import Compiler.Hoopl.Unique

import Control.Applicative as AP (Applicative(..))
import Control.Monad (join)
import Control.Monad.Trans.State

class Monad m => FuelMonad m where
  getFuel :: m Fuel
  setFuel :: Fuel -> m ()

-- | Find out how much fuel remains after a computation.
-- Can be subtracted from initial fuel to get total consumption.
fuelRemaining :: FuelMonad m => m Fuel
fuelRemaining = getFuel

class FuelMonadT fm where
  runWithFuel :: (Monad m, FuelMonad (fm m)) => Fuel -> fm m a -> m a
  liftFuel    :: (Monad m, FuelMonad (fm m)) => m a -> fm m a



type Fuel = Int

withFuel :: FuelMonad m => Maybe a -> m (Maybe a)
withFuel = (fmap . fmap) join . traverse $ \ a -> getFuel >>= \ case
    0 -> pure Nothing
    f -> Just a <$ setFuel (f-1)


----------------------------------------------------------------

newtype CheckingFuelMonad m a = FM { unFM :: Fuel -> m (a, Fuel) }
  deriving (Functor)
  deriving (Applicative, Monad) via (StateT Fuel m)

instance UniqueMonad m => UniqueMonad (CheckingFuelMonad m) where
  freshUnique = FM (\f -> [(l, f) | l <- freshUnique])

instance Monad m => FuelMonad (CheckingFuelMonad m) where
  getFuel   = FM (\f -> pure (f, f))
  setFuel f = FM (\_ -> pure ((),f))

instance FuelMonadT CheckingFuelMonad where
  runWithFuel fuel m = [a | (a, _) <- unFM m fuel]
  liftFuel m = FM $ \f -> [(a, f) | a <- m]

----------------------------------------------------------------

newtype InfiniteFuelMonad m a = IFM { unIFM :: m a }
  deriving (Functor)
  deriving (Applicative, Monad) via m

instance UniqueMonad m => UniqueMonad (InfiniteFuelMonad m) where
  freshUnique = IFM freshUnique

instance Monad m => FuelMonad (InfiniteFuelMonad m) where
  getFuel   = pure infiniteFuel
  setFuel _ = pure ()

instance FuelMonadT InfiniteFuelMonad where
  runWithFuel _ = unIFM
  liftFuel = IFM

infiniteFuel :: Fuel -- effectively infinite, any, but subtractable
infiniteFuel = maxBound

type SimpleFuelMonad = CheckingFuelMonad SimpleUniqueMonad

{-
runWithFuelAndUniques :: Fuel -> [Unique] -> FuelMonad a -> a
runWithFuelAndUniques fuel uniques m = a
  where (a, _, _) = unFM m fuel uniques

freshUnique :: FuelMonad Unique
freshUnique = FM (\f (l:ls) -> (l, f, ls))
-}

