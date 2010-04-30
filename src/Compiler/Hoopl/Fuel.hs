-----------------------------------------------------------------------------
--		The fuel monad
-----------------------------------------------------------------------------

module Compiler.Hoopl.Fuel
  ( Fuel, infiniteFuel
  , withFuel
  , HooplMonad(..), freshLabel -- these belong somewhere else
  , FuelMonad(..)
  , FuelMonadT(..)
  , CheckingFuelMonad
  , InfiniteFuelMonad
  )
where

import Compiler.Hoopl.Label

class Monad m => HooplMonad m where
  getLabel :: m Label

{-# DEPRECATED getLabel "will be replaced with something based on getUnique" #-}

freshLabel :: HooplMonad m => m Label
freshLabel = getLabel

class Monad m => FuelMonad m where
  getFuel :: m Fuel
  setFuel :: Fuel -> m ()

class FuelMonadT fm where
  runWithFuel :: (Monad m, FuelMonad (fm m)) => Fuel -> fm m a -> m a


type Fuel = Int

withFuel :: FuelMonad m => Maybe a -> m (Maybe a)
withFuel Nothing  = return Nothing
withFuel (Just r) = do f <- getFuel
                       if f == 0 then return Nothing
                        else setFuel (f-1) >> return (Just r)


----------------------------------------------------------------

newtype CheckingFuelMonad m a = FM { unFM :: Fuel -> m (a, Fuel) }

instance Monad m => Monad (CheckingFuelMonad m) where
  return a = FM (\f -> return (a, f))
  fm >>= k = FM (\f -> do { (a, f') <- unFM fm f; unFM (k a) f' })

instance HooplMonad m => HooplMonad (CheckingFuelMonad m) where
  getLabel = FM (\f -> do { l <- getLabel; return (l, f) })

instance Monad m => FuelMonad (CheckingFuelMonad m) where
  getFuel   = FM (\f -> return (f,f))
  setFuel f = FM (\_ -> return ((),f))

instance FuelMonadT CheckingFuelMonad where
  runWithFuel fuel m = do { (a, _) <- unFM m fuel; return a }

----------------------------------------------------------------

newtype InfiniteFuelMonad m a = IFM { unIFM :: m a }
instance Monad m => Monad (InfiniteFuelMonad m) where
  return a = IFM $ return a
  m >>= k  = IFM $ do { a <- unIFM m; unIFM (k a) }

instance HooplMonad m => HooplMonad (InfiniteFuelMonad m) where
  getLabel = IFM $ getLabel

instance Monad m => FuelMonad (InfiniteFuelMonad m) where
  getFuel   = return infiniteFuel
  setFuel _ = return ()

instance FuelMonadT InfiniteFuelMonad where
  runWithFuel _ = unIFM

infiniteFuel :: Fuel -- effectively infinite, any, but subtractable
infiniteFuel = maxBound