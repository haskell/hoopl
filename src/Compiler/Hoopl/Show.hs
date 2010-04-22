{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleContexts #-}

module Compiler.Hoopl.Show 
  ( showGraph
  )
where

import Compiler.Hoopl.Graph

--------------------------------------------------------------------------------
-- Prettyprinting
--------------------------------------------------------------------------------

type Showing n = forall e x . n e x -> String
 

showGraph :: forall n e x . (Edges n) => Showing n -> Graph n e x -> String
showGraph node = g
  where g :: (Edges n) => Graph n e x -> String
        g GNil = ""
        g (GUnit block) = b block
        g (GMany g_entry g_blocks g_exit) =
            open b g_entry ++ body g_blocks ++ open b g_exit
        body blocks = concatMap b (map snd $ bodyList blocks)
        b :: forall e x . Block n e x -> String
        b (ZFirst  n)     = node n
        b (ZMiddle n)     = node n
        b (ZLast   n)     = node n ++ "\n"
        b (ZCat b1 b2)    = b b1   ++ b b2
        b (ZHead b1 n)    = b b1   ++ node n ++ "\n"
        b (ZTail n b1)    = node n ++ b b1
        b (ZClosed b1 b2) = b b1   ++ b b2

open :: (a -> String) -> MaybeO z a -> String
open _ NothingO  = ""
open p (JustO n) = p n
