{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleContexts #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif

module Compiler.Hoopl.Show 
  ( showGraph, showFactBase
  )
where

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label

--------------------------------------------------------------------------------
-- Prettyprinting
--------------------------------------------------------------------------------

type Showing n = forall e x . n e x -> String
 

showGraph :: forall n e x . (NonLocal n) => Showing n -> Graph n e x -> String
showGraph node = g
  where g :: (NonLocal n) => Graph n e x -> String
        g GNil = ""
        g (GUnit block) = b block
        g (GMany g_entry g_blocks g_exit) =
            open b g_entry ++ body g_blocks ++ open b g_exit
        body blocks = concatMap b (mapElems blocks)
        b :: forall e x . Block n e x -> String
        b (BFirst  n)     = node n
        b (BMiddle n)     = node n
        b (BLast   n)     = node n ++ "\n"
        b (BCat b1 b2)    = b b1   ++ b b2
        b (BHead b1 n)    = b b1   ++ node n ++ "\n"
        b (BTail n b1)    = node n ++ b b1
        b (BClosed b1 b2) = b b1   ++ b b2

open :: (a -> String) -> MaybeO z a -> String
open _ NothingO  = ""
open p (JustO n) = p n

showFactBase :: Show f => FactBase f -> String
showFactBase = show . mapToList
