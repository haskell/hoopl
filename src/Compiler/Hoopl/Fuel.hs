-----------------------------------------------------------------------------
--		The fuel monad
-----------------------------------------------------------------------------

module Compiler.Hoopl.Fuel
  ( Fuel
  , FuelMonad, withFuel, getFuel, setFuel
  , freshUnique
    
  , runWithFuel, runWithFuelAndUniques
  )
where

import Compiler.Hoopl.Unique

type Fuel    = Int

newtype FuelMonad a = FM { unFM :: Fuel -> [Unique] -> (a, Fuel, [Unique]) }

instance Monad FuelMonad where
  return x = FM (\f u -> (x,f,u))
  m >>= k  = FM (\f u -> case unFM m f u of (r,f',u') -> unFM (k r) f' u')

withFuel :: Maybe a -> FuelMonad (Maybe a)
withFuel Nothing  = return Nothing
withFuel (Just r) = FM (\f u -> if f==0 then (Nothing, f, u)
                                else (Just r, f-1, u))

getFuel :: FuelMonad Fuel
getFuel = FM (\f u -> (f,f,u))

setFuel :: Fuel -> FuelMonad ()
setFuel f = FM (\_ u -> ((), f, u))

runWithFuel :: Fuel -> FuelMonad a -> a
runWithFuel fuel m = runWithFuelAndUniques fuel allUniques m

runWithFuelAndUniques :: Fuel -> [Unique] -> FuelMonad a -> a
runWithFuelAndUniques fuel uniques m = a
  where (a, _, _) = unFM m fuel uniques

freshUnique :: FuelMonad Unique
freshUnique = FM (\f (l:ls) -> (l, f, ls))
