-- | Utilities for clients of Hoopl, not used internally.

module Compiler.Hoopl.XUtil
  ( WithBot(..), addBot, addBot'
  , WithTop(..), addTop, addTop'
  , firstXfer, distributeXfer, distributeFact
  )
where

import Data.Maybe

import Compiler.Hoopl.Label
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Dataflow

-- | Adds a bottom element to a set to help form a lattice
data WithBot a = Bot | NonBot a

-- | Given a join function and a name, creates a semi lattice by
-- adding a bottom element.  A specialized version of 'addBot''.
addBot  :: String -> JoinFun a -> DataflowLattice (WithBot a)
-- | A more general case for creating a new lattice
addBot' :: String -> (Label -> OldFact a -> NewFact a -> (ChangeFlag, WithBot a))
        -> DataflowLattice (WithBot a)

addBot name join = addBot' name join'
   where join' l o n = (change, NonBot f)
            where (change, f) = join l o n

addBot' name joinx = DataflowLattice name Bot join False
  where -- careful: order of cases matters for ChangeFlag
        join _ (OldFact f)            (NewFact Bot) = (NoChange, f)
        join _ (OldFact Bot)          (NewFact f)   = (SomeChange, f)
        join l (OldFact (NonBot old)) (NewFact (NonBot new))
           = joinx l (OldFact old) (NewFact new)

instance Show a => Show (WithBot a) where
  show Bot = "_|_"
  show (NonBot a) = show a

instance Functor WithBot where
  fmap _ Bot = Bot
  fmap f (NonBot a) = NonBot (f a)



-- | Adds a top element to a set to help form a lattice
data WithTop a = Top | NonTop a

-- | Given a join function and a name, creates a semi lattice by
-- adding a top element.  A specialized version of 'addTop''.
addTop  :: String -> JoinFun a -> DataflowLattice (WithTop a)
-- | A more general case for creating a new lattice
addTop' :: String -> (Label -> OldFact a -> NewFact a -> (ChangeFlag, WithTop a))
        -> DataflowLattice (WithTop a)

addTop name join = addTop' name join'
   where join' l o n = (change, NonTop f)
            where (change, f) = join l o n

addTop' name joinx = DataflowLattice name Top join False
  where  -- careful: order of cases matters for ChangeFlag
        join _ (OldFact Top)          (NewFact f)   = (NoChange, Top)
        join _ (OldFact f)            (NewFact Top) = (SomeChange, Top)
        join l (OldFact (NonTop old)) (NewFact (NonTop new))
           = joinx l (OldFact old) (NewFact new)

instance Show a => Show (WithTop a) where
  show Top = "T"
  show (NonTop a) = show a

instance Functor WithTop where
  fmap _ Top = Top
  fmap f (NonTop a) = NonTop (f a)


----------------------------------------------------------------

-- | A utility function so that a transfer function for a first
-- node can be given just a fact; we handle the lookup.  This
-- function is planned to be made obsolete by changes in the dataflow
-- interface.

firstXfer :: Edges n => (n C O -> f -> f) -> (n C O -> FactBase f -> f)
firstXfer xfer n fb = xfer n $ fromJust $ lookupFact fb $ entryLabel n

-- | This utility function handles a common case in which a transfer function
-- produces a single fact out of a last node, which is then distributed
-- over the outgoing edges.
distributeXfer :: Edges n => (n O C -> f -> f) -> (n O C -> f -> FactBase f)
distributeXfer xfer n f = mkFactBase [ (l, xfer n f) | l <- successors n ]

-- | This utility function handles a common case in which a transfer function
-- for a last node takes the incoming fact unchanged and simply distributes
-- that fact over the outgoing edges.
distributeFact :: Edges n => n O C -> f -> FactBase f
distributeFact n f = mkFactBase [ (l, f) | l <- successors n ]
