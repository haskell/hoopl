{-# LANGUAGE GADTs, ScopedTypeVariables #-}

-- | Possibly doubly pointed lattices

module Compiler.Hoopl.Pointed
  ( Pointed(..), addPoints, addPoints', addTop, addTop'
  )
where

import Compiler.Hoopl.Graph
import Compiler.Hoopl.Label
import Compiler.Hoopl.Dataflow

-- | Adds top, bottom, or both to help form a lattice
data Pointed t b a where
  Bot   ::      Pointed t C a
  Top   ::      Pointed C b a
  PElem :: a -> Pointed t b a

-- | Given a join function and a name, creates a semi lattice by
-- adding a bottom element, and possibly a top element also.
-- A specialized version of 'addPoints''.
addPoints  :: String -> JoinFun a -> DataflowLattice (Pointed t C a)
-- | A more general case for creating a new lattice
addPoints' :: forall a t .
              String
           -> (Label -> OldFact a -> NewFact a -> (ChangeFlag, Pointed t C a))
           -> DataflowLattice (Pointed t C a)

addPoints name join = addPoints' name join'
   where join' l o n = (change, PElem f)
            where (change, f) = join l o n

addPoints' name joinx = DataflowLattice name Bot join False
  where -- careful: order of cases matters for ChangeFlag
        join :: JoinFun (Pointed t C a)
        join _ (OldFact f)            (NewFact Bot) = (NoChange, f)
        join _ (OldFact Top)          (NewFact f)   = (NoChange, Top)
        join _ (OldFact Bot)          (NewFact f)   = (SomeChange, f)
        join _ (OldFact f)            (NewFact Top) = (SomeChange, Top)
        join l (OldFact (PElem old)) (NewFact (PElem new))
           = joinx l (OldFact old) (NewFact new)


-- | Given a join function and a name, creates a semi lattice by
-- adding a top element but no bottom element.  Caller must supply the bottom 
-- element.
addTop  :: DataflowLattice a -> DataflowLattice (Pointed C O a)
-- | A more general case for creating a new lattice
addTop' :: forall a .
              String
           -> a
           -> (Label -> OldFact a -> NewFact a -> (ChangeFlag, Pointed C O a))
           -> DataflowLattice (Pointed C O a)

addTop lattice = lattice' { fact_do_logging = fact_do_logging lattice }
   where lattice' = addTop' name' (fact_bot lattice) join'
         name' = fact_name lattice ++ " + T"
         join' l o n = (change, PElem f)
            where (change, f) = fact_extend lattice l o n

addTop' name bot joinx = DataflowLattice name (PElem bot) join False
  where -- careful: order of cases matters for ChangeFlag
        join :: JoinFun (Pointed C O a)
        join _ (OldFact Top)          (NewFact f)   = (NoChange, Top)
        join _ (OldFact f)            (NewFact Top) = (SomeChange, Top)
        join l (OldFact (PElem old)) (NewFact (PElem new))
           = joinx l (OldFact old) (NewFact new)

instance Show a => Show (Pointed t b a) where
  show Bot = "_|_"
  show Top = "T"
  show (PElem a) = show a

instance Functor (Pointed t b) where
  fmap _ Bot = Bot
  fmap _ Top = Top
  fmap f (PElem a) = PElem (f a)
