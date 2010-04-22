{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleContexts #-}

module Compiler.Hoopl.Debug 
  ( TraceFn , debugFwdJoins , debugBwdJoins
  , debugFwdTransfers , debugBwdTransfers
  )
where

import Compiler.Hoopl.Dataflow
import Compiler.Hoopl.Show

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
--------------------------------------------------------------------------------


debugFwdJoins :: forall n f . Show f => TraceFn -> ChangePred -> FwdPass n f -> FwdPass n f
debugBwdJoins :: forall n f . Show f => TraceFn -> ChangePred -> BwdPass n f -> BwdPass n f

type TraceFn    = forall a . String -> a -> a
type ChangePred = ChangeFlag -> Bool

debugFwdJoins trace pred p = p { fp_lattice = debugJoins trace pred $ fp_lattice p }
debugBwdJoins trace pred p = p { bp_lattice = debugJoins trace pred $ bp_lattice p }

debugJoins :: Show f => TraceFn -> ChangePred -> DataflowLattice f -> DataflowLattice f
debugJoins trace showPred l@(DataflowLattice {fact_extend = extend}) = l {fact_extend = extend'}
  where
   extend' l f1@(OldFact of1) f2@(NewFact nf2) =
     if showPred c then trace output res else res
       where res@(c, f') = extend l f1 f2
             output = case c of
                        SomeChange -> "+ Join@" ++ show l ++ ": " ++ show of1 ++ " |_| "
                                                                  ++ show nf2 ++ " = " ++ show f'
                        NoChange   -> "_ Join@" ++ show l ++ ": " ++ show nf2 ++ " <= " ++ show of1

--------------------------------------------------------------------------------
-- Functions we'd like to have, but don't know how to implement generically:
--------------------------------------------------------------------------------

type ShowN n   = forall e x . n e x ->      String
type FPred n f = forall e x . n e x -> f        -> Bool
type BPred n f = forall e x . n e x -> Fact x f -> Bool
debugFwdTransfers::
  forall n f . Show f => TraceFn -> ShowN n -> FPred n f -> FwdPass n f -> FwdPass n f
debugFwdTransfers trace showN showPred pass = pass { fp_transfer = transfers' }
  where
    (f, m, l) = getFTransfers $ fp_transfer pass
    transfers' = mkFTransfer (wrap show f) (wrap show m) (wrap showFactBase l)
    wrap :: forall e x . (Fact x f -> String) -> (n e x -> f -> Fact x f) -> n e x -> f -> Fact x f
    wrap showOutF ft n f = if showPred n f then trace output res else res
      where
        res    = ft n f
        output = name ++ " transfer: " ++ show f ++ " -> " ++ showN n ++ " -> " ++ showOutF res
    name = fact_name (fp_lattice pass)
    
debugBwdTransfers::
  forall n f . Show f => TraceFn -> ShowN n -> BPred n f -> BwdPass n f -> BwdPass n f
debugBwdTransfers trace showN showPred pass = pass { bp_transfer = transfers' }
  where
    (f, m, l) = getBTransfers $ bp_transfer pass
    transfers' = mkBTransfer (wrap show f) (wrap show m) (wrap showFactBase l)
    wrap :: forall e x . (Fact x f -> String) -> (n e x -> Fact x f -> f) -> n e x -> Fact x f -> f
    wrap showInF ft n f = if showPred n f then trace output res else res
      where
        res    = ft n f
        output = name ++ " transfer: " ++ showInF f ++ " -> " ++ showN n ++ " -> " ++ show res
    name = fact_name (bp_lattice pass)
    

-- debugFwdTransfers, debugFwdRewrites, debugFwdAll ::
--   forall n f . Show f => TraceFn -> ShowN n -> FwdPass n f -> FwdPass n f
-- debugBwdTransfers, debugBwdRewrites, debugBwdAll ::
--   forall n f . Show f => TraceFn -> ShowN n -> BwdPass n f -> BwdPass n f

