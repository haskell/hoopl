{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module IR (Proc (..), Node (..), Exp (..), Lit (..), Value (..), BinOp(..), Var,
           showProc) where

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

instance Edges Node where
  blockId (Label bid) = bid
  blockId _           = error "GADT unreachable?"
  successors (Branch b)     = [b]
  successors (Cond _ b1 b2) = [b1, b2]
  successors (Call _ _ _ b) = [b]
  successors (Return _)     = []
  successors _              = error "GADT unreachable?"

-- Prettyprinting

showProc :: Proc -> String
showProc proc = name proc ++ tuple (args proc) ++ graph
  where
    graph  = " {\n" ++ showG showBID (body proc) ++ "}\n"
    -- Get all the block IDs and map them to distinct integers
    showBID = show . fromJust . (findBEnv $ mkBlockEnv $ zip bids nats)
    nats = [1..] :: [Integer]
    bids = foldG getBID [] (body proc)
    getBID :: forall e' x'. [BlockId] -> Node e' x' -> [BlockId]
    getBID rst (Label bid)  = bid   : rst
    getBID rst (Branch bid) = bid   : rst
    getBID rst (Cond _ t f) = t : f : rst
    getBID rst _            = rst

foldG :: (forall e' x'. a -> Node e' x' -> a) -> a -> Graph Node e x -> a
foldG _ z GNil = z
foldG f z (GMids b) = foldB f z b
foldG f z (GMany {g_entry, g_blocks, g_exit}) =
  foldLink (foldB f) (foldl (foldB f) (foldLink (foldB f) z g_exit) g_blocks) g_entry

foldLink :: (forall e' x'. a -> n e' x' -> a) -> a -> Link y (n e x) -> a
foldLink _ z ClosedLink   = z
foldLink f z (OpenLink t) = f z t

foldB :: (forall e' x'. a -> Node e' x' -> a) -> a -> Block Node e x -> a
foldB f z (BUnit n)    = f z n
foldB f z (BCat b1 b2) = foldB f (foldB f z b2) b1

showG :: (BlockId -> String) -> Graph Node e x -> String
showG _ GNil = ""
showG b (GMids block) = showB b block
showG b (GMany {g_entry, g_blocks, g_exit}) =
  showExit (showB b) g_entry ++ concatMap (showB b) g_blocks ++ showExit (showB b) g_exit

showExit :: (forall e x. n e x -> String) -> Link y (n e' x') -> String
showExit _ ClosedLink   = ""
showExit p (OpenLink n) = p n

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
