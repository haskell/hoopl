{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module Ast (Proc(..), Block(..), Insn(..), Control(..), Lbl) where

import Expr

-- | A procedure has a name, a sequence of arguments, and a body,
--   which is a sequence of basic blocks. The procedure entry
--   is the first block in the body.
data Proc = Proc { name :: String, args :: [Var], body :: [Block] }

-- | A block consists of a label, a sequence of instructions,
--   and a control-transfer instruction.
data Block = Block { first :: Lbl, mids :: [Insn], last :: Control }

-- | An instruction is an assignment to a variable or a store to memory.
data Insn = Assign Var  Expr
          | Store  Expr Expr

-- | Control transfers are branches (unconditional and conditional),
--   call, and return.
--   The Call instruction takes several parameters: variables to get
--   values returned from the call, the name of the function,
--   arguments to the function, and the label for the successor
--   of the function call.
data Control = Branch Lbl
             | Cond   Expr   Lbl    Lbl
             | Call   [Var]  String [Expr] Lbl
             | Return [Expr]

-- | Labels are represented as strings in an AST.
type Lbl = String
