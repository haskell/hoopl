{-# LANGUAGE GADTs #-}

module RG
where

import Data.Maybe

import Compiler.Hoopl

-------------------------------------------------------------
-- noodling around

data MaybeC ex t where
  JustC    :: t -> MaybeC C t
  NothingC ::      MaybeC O t

data ReplacementGraph n e x = Replacement (MaybeC e Label) (Graph n e x)

theFact :: Fact e f -> MaybeC e Label -> f
theFact f NothingC = f
theFact fb (JustC l) = fromJust $ lookupFact fb l
