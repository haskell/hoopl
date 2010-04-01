{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module IR (Proc (..), Node (..), Exp (..), Lit (..), Value (..), BinOp(..), Var,
           showProc) where

import qualified Data.IntMap as M
import Data.Maybe
import Prelude hiding (succ)

import Hoopl

data Exp = Lit   Lit
         | Var   Var
         | Load  Exp
         | Binop BinOp Exp Exp
data BinOp = Add | Sub | Mul | Div | Eq | Ne | Lt | Gt | Lte | Gte
type Var   = String
data Lit   = Bool Bool | Int Integer deriving Eq
data Value = B Bool    | I   Integer deriving Eq

data Proc = Proc { name :: String, args :: [Var], entry :: BlockId, body :: Graph Node C C }

data Node e x where
  Label  :: BlockId ->                                  Node C O
  Assign :: Var     -> Exp     ->                       Node O O
  Store  :: Exp     -> Exp     ->                       Node O O
  Branch :: BlockId ->                                  Node O C
  Cond   :: Exp     -> BlockId -> BlockId ->            Node O C
  Call   :: [Var]   -> String  -> [Exp]   -> BlockId -> Node O C -- String is bogus
  Return :: [Exp]   ->                                  Node O C

-- Prettyprinting

showProc :: Proc -> String
showProc proc = name proc ++ tuple (args proc) ++ graph
  where
    graph  = " {\n" ++ showG showBID (body proc) ++ "}\n"
    -- Get all the block IDs and map them to distinct integers
    showBID = show . fromJust . (findBEnv $ mkBlockEnv $ zip bids nats)
    nats = [1..] :: [Integer]
    bids = foldG getBID (body proc) []
    getBID :: forall e' x'.  Node e' x' -> [BlockId] -> [BlockId]
    getBID (Label bid)  rst = bid   : rst
    getBID (Branch bid) rst = bid   : rst
    getBID (Cond _ t f) rst = t : f : rst
    getBID _            rst = rst

foldG :: (forall e' x'. Node e' x' -> a -> a) -> Graph Node e x -> a -> a
foldG _ GNil z = z
foldG f (GUnit b) z = foldB f b z
foldG f (GMany g_entry g_blocks g_exit) z =
  foldB f g_entry $ M.fold (foldB f) (foldTail (foldB f) g_exit z) g_blocks

foldTail :: (Block n C O -> a -> a) -> Tail n x -> a -> a
foldTail _ NoTail     z = z
foldTail f (Tail _ t) z = f t z

foldB :: (forall e' x'. Node e' x' -> a -> a) -> Block Node e x -> a -> a
foldB f (BUnit n)    z = f n z
foldB f (BCat b1 b2) z = foldB f b1 (foldB f b2 z)

showG :: (BlockId -> String) -> Graph Node e x -> String
showG _ GNil = ""
showG b (GUnit block) = showB b block
showG b (GMany g_entry g_blocks g_exit) =
  showB b g_entry ++ concatMap (showB b) (map snd $ M.toList g_blocks) ++ showTail (showB b) g_exit

showTail :: (Block n C O -> String) -> Tail n x -> String
showTail _ NoTail     = ""
showTail p (Tail _ n) = p n

showB :: (BlockId -> String) -> Block Node e x -> String
showB b (BUnit n) = showNode b n ++ "\n"
showB b (BCat b1 b2) = showB b b1 ++ showB b b2


showNode :: (BlockId -> String) -> Node e x -> String
showNode b (Label bid)        = b bid ++ ":"
showNode _ (Assign v e)       = ind $ v ++ " = " ++ show e
showNode _ (Store addr e)     = ind $ "m[" ++ show addr ++ "] = " ++ show e
showNode b (Branch bid)       = ind $ "goto " ++ b bid
showNode b (Cond e t f)       =
  ind $ "if " ++ show e ++ " then goto " ++ b t ++ " else goto " ++ b f
showNode b (Call ress f cargs succ) =
  ind $ tuple ress ++ " = " ++ f ++ tuple (map show cargs) ++ " goto " ++ b succ
showNode _ (Return      rargs) = ind $ "ret " ++ tuple (map show rargs)

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
