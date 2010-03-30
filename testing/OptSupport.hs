{-# OPTIONS_GHC -Wall -fno-warn-incomplete-patterns -XGADTs -XRankNTypes #-}
module OptSupport (WithTop (..), stdMapJoin, combine,
                   map_EE, map_EN, fold_EE, fold_EN, toAGraph) where

import Control.Monad
import qualified Data.Map as M
import Data.Maybe
import Prelude hiding (succ)

import Hoopl
import IR

----------------------------------------------
-- Tx as monad
--   Probably doesn't belong here, but until
--   Hoopl[1..] settles down, it'll stay here.
----------------------------------------------

-- instance Monad TxRes where
--   return x = TxRes NoChange x
--   TxRes c x >>= k = TxRes (max c c') y
--                       where TxRes c' y = k x
-- 
-- changeTx :: x -> TxRes x
-- changeTx x = TxRes SomeChange x
-- 
-- txToMaybe :: TxRes x -> Maybe x
-- txToMaybe (TxRes SomeChange x) = Just x
-- txToMaybe (TxRes NoChange   _) = Nothing
-- 
-- instance Eq ChangeFlag where
--   x == y = cmpCh x y == EQ
-- instance Ord ChangeFlag where
--   compare = cmpCh
-- 
-- cmpCh :: ChangeFlag -> ChangeFlag -> Ordering
-- cmpCh NoChange NoChange     = EQ
-- cmpCh NoChange SomeChange   = LT
-- cmpCh SomeChange NoChange   = GT
-- cmpCh SomeChange SomeChange = EQ

----------------------------------------------
-- Common lattice utility code:
----------------------------------------------

data WithTop a = Elt a | Top deriving Eq

-- It's common to represent dataflow facts as a map from locations
-- to some fact about the locations. For these maps, the join
-- operation on the map can be expressed in terms of the join
-- on each element:
stdMapJoin :: Ord k => (v -> v -> (ChangeFlag, v)) ->
                       M.Map k v -> M.Map k v -> (ChangeFlag, M.Map k v)
stdMapJoin eltJoin new old = M.foldWithKey add (NoChange, old) new
  where 
    add k new_v (ch, joinmap) =
      case M.lookup k joinmap of
        Nothing    -> (SomeChange, M.insert k new_v joinmap)
        Just old_v -> case eltJoin new_v old_v of
                        (SomeChange, v') -> (SomeChange, M.insert k v' joinmap)
                        (NoChange,   _)  -> (ch, joinmap)

----------------------------------------------
-- Combine Transformations
----------------------------------------------

-- Combine the transformations, executing the 2nd if the 1st does no rewriting.
combine :: ForwardRewrites n f -> ForwardRewrites n f -> ForwardRewrites n f
combine r1 r2 = \n f -> case r1 n f of Nothing -> r2 n f
                                       x -> x

----------------------------------------------
-- Map/Fold functions for expressions/nodes
----------------------------------------------

map_EE :: (Exp -> Maybe Exp) -> Exp      -> Maybe Exp
map_EN :: (Exp -> Maybe Exp) -> Node e x -> Maybe (Node e x)

map_EE f e@(Lit _)     = f e
map_EE f e@(Var _)     = f e
map_EE f e@(Load addr) =
  case map_EE f addr of 
    Just addr' -> Just $ fromMaybe e' (f e')
                    where e' = Load addr'
    Nothing    -> f e
map_EE f e@(Binop op e1 e2) =
  case (map_EE f e1, map_EE f e2) of
    (Nothing, Nothing) -> f e
    (e1',     e2')     -> Just $ fromMaybe e' (f e')
                    where e' = Binop op (fromMaybe e1 e1') (fromMaybe e2 e2')

map_EN _   (Label _)           = Nothing
map_EN f   (Assign v e)        = fmap (Assign v) $ f e
map_EN f   (Store addr e)      =
  case (map_EE f addr, map_EE f e) of
    (Nothing, Nothing) -> Nothing
    (addr', e') -> Just $ Store (fromMaybe addr addr') (fromMaybe e e')
map_EN _   (Branch _)          = Nothing
map_EN f   (Cond e tid fid)    =
  case f e of Just e' -> Just $ Cond e' tid fid
              Nothing -> Nothing
map_EN f   (Call rs n es succ) =
  if all isNothing es' then Nothing
  else Just $ Call rs n (map (uncurry fromMaybe) (zip es es')) succ
    where es' = map f es
map_EN f   (Return es) =
   if all isNothing es' then Nothing
   else Just $ Return (map (uncurry fromMaybe) (zip es es'))
     where es' = map f es

fold_EE :: (a -> Exp -> a) -> a -> Exp      -> a
fold_EN :: (a -> Exp -> a) -> a -> Node e x -> a

fold_EE f z e@(Lit _)         = f z e
fold_EE f z e@(Var _)         = f z e
fold_EE f z e@(Load addr)     = f (f z addr) e
fold_EE f z e@(Binop _ e1 e2) = f (f (f z e2) e1) e

fold_EN _ z (Label _)       = z
fold_EN f z (Assign _ e)    = f z e
fold_EN f z (Store addr e)  = f (f z e) addr
fold_EN _ z (Branch _)      = z
fold_EN f z (Cond e _ _)    = f z e
fold_EN f z (Call _ _ es _) = foldl f z es
fold_EN f z (Return es)     = foldl f z es

----------------------------------------------
-- Common fact/graph operations
----------------------------------------------

-- Probably not quite what we want long term
toAGraph :: Node e x -> AGraph Node e x
toAGraph n@(Label _)      = agraphOfNode n
toAGraph n@(Assign _ _)   = agraphOfNode n
toAGraph n@(Store _ _)    = agraphOfNode n
toAGraph n@(Branch _)     = agraphOfNode n
toAGraph n@(Cond _ _ _)   = agraphOfNode n
toAGraph n@(Call _ _ _ _) = agraphOfNode n
toAGraph n@(Return _)     = agraphOfNode n
