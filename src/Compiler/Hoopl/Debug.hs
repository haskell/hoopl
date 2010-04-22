{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleContexts #-}

module Compiler.Hoopl.Debug 
  ( TraceFn , debugFwdJoins , debugBwdJoins
  )
where

import Compiler.Hoopl.Dataflow

--------------------------------------------------------------------------------
-- | Debugging combinators:
-- Each combinator takes a dataflow pass and produces
-- a dataflow pass that can output debugging messages.
-- You provide the function, we call it with the applicable message.
-- 
-- The most common use case is probably to:
--
--   1. import 'Debug.Trace'
--
--   2. pass 'trace' as the 1st argument to the debug combinator
--
--   3. pass 'const true' as the 2nd argument to the debug combinator
--
-- There are two kinds of debugging messages for a join,
-- depending on whether the join is higher in the lattice than the old fact:
--   1. If the join is higher, we show:
--         + Join@L: f1 `join` f2 = f'
--      where:
--        + indicates a change
--        L is the label where the join takes place
--        f1 is the old fact at the label
--        f2 is the new fact we are joining to f1
--        f' is the result of the join
--   2. _ Join@L: f2 <= f1
--      where:
--        _ indicates no change
--        L is the label where the join takes place
--        f1 is the old fact at the label (which remains unchanged)
--        f2 is the new fact we joined with f1
--------------------------------------------------------------------------------


debugFwdJoins :: forall n f . Show f => TraceFn -> ChangePred -> FwdPass n f -> FwdPass n f
debugBwdJoins :: forall n f . Show f => TraceFn -> ChangePred -> BwdPass n f -> BwdPass n f

type TraceFn    = forall a . String -> a -> a
type ChangePred = ChangeFlag -> Bool

debugFwdJoins trace pred p = p { fp_lattice = debugJoins trace pred $ fp_lattice p }
debugBwdJoins trace pred p = p { bp_lattice = debugJoins trace pred $ bp_lattice p }

debugJoins :: Show f => TraceFn -> ChangePred -> DataflowLattice f -> DataflowLattice f
debugJoins trace showOutput l@(DataflowLattice {fact_extend = extend}) = l {fact_extend = extend'}
  where
   extend' l f1@(OldFact of1) f2@(NewFact nf2) =
     if showOutput c then trace output res else res
       where res@(c, f') = extend l f1 f2
             output = case c of
                        SomeChange -> "+ Join@" ++ show l ++ ": " ++ show of1 ++ " `join` "
                                                                  ++ show nf2 ++ " = " ++ show f'
                        NoChange   -> "_ Join@" ++ show l ++ ": " ++ show nf2 ++ " <= " ++ show of1

--------------------------------------------------------------------------------
-- Functions we'd like to have, but don't know how to implement generically:
--------------------------------------------------------------------------------

-- type Showing n = forall e x . n e x -> String
-- debugFwdTransfers, debugFwdRewrites, debugFwdAll ::
--   forall n f . Show f => TraceFn -> Showing n -> FwdPass n f -> FwdPass n f
-- debugBwdTransfers, debugBwdRewrites, debugBwdAll ::
--   forall n f . Show f => TraceFn -> Showing n -> BwdPass n f -> BwdPass n f

