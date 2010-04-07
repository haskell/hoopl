{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module IR (Proc (..), Node (..), Exp (..), Lit (..), Value (..), BinOp(..), Var,
           showG, showProc) where

import Prelude hiding (succ)

import Compiler.Hoopl

data Exp = Lit   Lit
         | Var   Var
         | Load  Exp
         | Binop BinOp Exp Exp
data BinOp = Add | Sub | Mul | Div | Eq | Ne | Lt | Gt | Lte | Gte
type Var   = String
data Lit   = Bool Bool | Int Integer deriving Eq
data Value = B Bool    | I   Integer deriving Eq

data Proc = Proc { name :: String, args :: [Var], entry :: Label, body :: Body Node }

data Node e x where
  Label  :: Label ->                                Node C O
  Assign :: Var     -> Exp     ->                   Node O O
  Store  :: Exp     -> Exp     ->                   Node O O
  Branch :: Label   ->                              Node O C
  Cond   :: Exp     -> Label   -> Label ->          Node O C
  Call   :: [Var]   -> String  -> [Exp] -> Label -> Node O C -- String is bogus
  Return :: [Exp]   ->                              Node O C

instance Edges Node where
  entryLabel (Label l)      = l
  successors (Branch l)     = [l]
  successors (Cond _ t f)   = [t, f]
  successors (Call _ _ _ l) = [l]
  successors (Return _)     = []

-- Prettyprinting

showProc :: Proc -> String
showProc proc = name proc ++ tuple (args proc) ++ graph
  where
    graph  = " {\n" ++ showBody (body proc) ++ "}\n"

showG :: Graph Node e x -> String
showG GNil = ""
showG (GUnit block) = showB block
showG (GMany g_entry g_blocks g_exit) =
  showOpen showB g_entry ++ showBody g_blocks ++ showOpen showB g_exit

showBody :: Body Node -> String
showBody blocks = concatMap showB (map snd $ bodyList blocks)

showOpen :: (Block n e x -> String) -> MaybeO z (Block n e x) -> String
showOpen _ NothingO  = ""
showOpen p (JustO n) = p n

showB :: Block Node e x -> String
showB (BUnit n)    = show n ++ "\n"
showB (BCat b1 b2) = showB b1 ++ showB b2

instance Show (Node e x) where
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

tuple :: [String] -> String
tuple []     = "()"
tuple [a]    = "(" ++ a ++ ")"
tuple (a:as) = "(" ++ a ++ concat (map ((++) ", ") as) ++ ")"

instance Show Exp where
  show (Lit   i) = show i
  show (Var   v) = v
  show (Load  e) = "m[" ++ show e ++ "]"
  show (Binop b e1 e2) = sub e1 ++ " " ++ show b ++ " " ++ sub e2
    where sub e@(Binop _ _ _) = tuple [show e]
          sub e = show e

instance Show Lit where
  show (Int  i) = show i
  show (Bool b) = show b

instance Show Value where
  show (B b) = show b
  show (I i) = show i

instance Show BinOp where
  show Add  = "+"
  show Sub  = "-"
  show Mul  = "*"
  show Div  = "/"
  show Eq   = "="
  show Ne   = "/="
  show Gt   = ">"
  show Lt   = "<"
  show Gte  = ">="
  show Lte  = "<="
