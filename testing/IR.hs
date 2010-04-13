{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module IR (Proc (..), Insn (..), Expr (..), Lit (..), Value (..), BinOp(..), Var,
           showG, showProc) where

import Prelude hiding (succ)

import Compiler.Hoopl
import Expr
import PP

data Value = B Bool | I Integer deriving Eq

data Proc = Proc { name :: String, args :: [Var], entry :: Label, body :: Body Insn }

data Insn e x where
  Label  :: Label  ->                               Insn C O
  Assign :: Var    -> Expr    ->                    Insn O O
  Store  :: Expr   -> Expr    ->                    Insn O O
  Branch :: Label  ->                               Insn O C
  Cond   :: Expr   -> Label   -> Label  ->          Insn O C
  Call   :: [Var]  -> String  -> [Expr] -> Label -> Insn O C
  Return :: [Expr] ->                               Insn O C

instance Edges Insn where
  entryLabel (Label l)      = l
  successors (Branch l)     = [l]
  successors (Cond _ t f)   = [t, f]
  successors (Call _ _ _ l) = [l]
  successors (Return _)     = []

--------------------------------------------------------------------------------
-- Prettyprinting
--------------------------------------------------------------------------------

showProc :: Proc -> String
showProc proc = name proc ++ tuple (args proc) ++ graph
  where
    graph  = " {\n" ++ showBody (body proc) ++ "}\n"

showG :: Graph Insn e x -> String
showG GNil = ""
showG (GUnit block) = showB block
showG (GMany g_entry g_blocks g_exit) =
  showOpen showB g_entry ++ showBody g_blocks ++ showOpen showB g_exit

showBody :: Body Insn -> String
showBody blocks = concatMap showB (map snd $ bodyList blocks)

showOpen :: (Block n e x -> String) -> MaybeO z (Block n e x) -> String
showOpen _ NothingO  = ""
showOpen p (JustO n) = p n

showB :: Block Insn e x -> String
showB (BUnit n)    = show n ++ "\n"
showB (BCat b1 b2) = showB b1 ++ showB b2

instance Show (Insn e x) where
  show (Label lbl)        = show lbl ++ ":"
  show (Assign v e)       = ind $ v ++ " = " ++ show e
  show (Store addr e)     = ind $ "m[" ++ show addr ++ "] = " ++ show e
  show (Branch lbl)       = ind $ "goto " ++ show lbl
  show (Cond e t f)       =
    ind $ "if " ++ show e ++ " then goto " ++ show t ++ " else goto " ++ show f
  show (Call ress f cargs succ) =
    ind $ tuple ress ++ " = " ++ f ++ tuple (map show cargs) ++ " goto " ++ show succ
  show (Return      rargs) = ind $ "ret " ++ tuple (map show rargs)

ind :: String -> String
ind x = "  " ++ x

instance Show Value where
  show (B b) = show b
  show (I i) = show i
