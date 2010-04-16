{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleContexts #-}

module Compiler.Hoopl.Debug 
  ( TraceFn , debugFwdJoins , debugBwdJoins
  )
where

import Compiler.Hoopl.Dataflow

--------------------------------------------------------------------------------
-- Debugging combinators:
-- Each combinator takes a dataflow pass and produces
-- a dataflow pass that can output debugging messages.
-- You provide the function, we call it with the applicable message.
-- 
-- The most common use case is probably to:
--  1. import Debug.Trace
--  2. pass trace as the 1st argument to the debug combinator
--------------------------------------------------------------------------------


type TraceFn = forall a . String -> a -> a
debugFwdJoins :: forall n f . Show f => TraceFn -> FwdPass n f -> FwdPass n f
debugBwdJoins :: forall n f . Show f => TraceFn -> BwdPass n f -> BwdPass n f

debugFwdJoins trace p = p { fp_lattice = debugJoins trace $ fp_lattice p }
debugBwdJoins trace p = p { bp_lattice = debugJoins trace $ bp_lattice p }

debugJoins :: Show f => TraceFn -> DataflowLattice f -> DataflowLattice f
-- JoinFun a -> JoinFun a 
debugJoins trace l@(DataflowLattice {fact_extend = extend}) = l {fact_extend = extend'}
  where
   extend' l f1@(OldFact of1) f2@(NewFact nf2) =
     case extend l f1 f2 of
       res@(NoChange, _)    -> res
       res@(SomeChange, f') ->
         trace ("Join@" ++ show l ++ ": " ++ show of1 ++ " |_| " ++ show nf2 ++ " = " ++ show f') res

--------------------------------------------------------------------------------
-- Functions we'd like to have, but don't know how to implement generically:
--------------------------------------------------------------------------------

-- type Showing n = forall e x . n e x -> String
-- debugFwdTransfers, debugFwdRewrites, debugFwdAll ::
--   forall n f . Show f => TraceFn -> Showing n -> FwdPass n f -> FwdPass n f
-- debugBwdTransfers, debugBwdRewrites, debugBwdAll ::
--   forall n f . Show f => TraceFn -> Showing n -> BwdPass n f -> BwdPass n f

