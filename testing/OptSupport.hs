{-# LANGUAGE GADTs, RankNTypes #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module OptSupport (stdMapJoin, map_VE, map_EE, map_EN, map_VN, fold_EE, fold_EN, insnToG) where

import qualified Data.Map as M
import Data.Maybe
import Prelude hiding (succ)

import Compiler.Hoopl
import IR

----------------------------------------------
-- Common lattice utility code:
----------------------------------------------

-- It's common to represent dataflow facts as a map from locations
-- to some fact about the locations. For these maps, the join
-- operation on the map can be expressed in terms of the join
-- on each element:
stdMapJoin :: Ord k => JoinFun v -> JoinFun (M.Map k v)
stdMapJoin eltJoin l (OldFact old) (NewFact new) = M.foldWithKey add (NoChange, old) new
  where 
    add k new_v (ch, joinmap) =
      case M.lookup k joinmap of
        Nothing    -> (SomeChange, M.insert k new_v joinmap)
        Just old_v -> case eltJoin l (OldFact old_v) (NewFact new_v) of
                        (SomeChange, v') -> (SomeChange, M.insert k v' joinmap)
                        (NoChange,   _)  -> (ch, joinmap)

----------------------------------------------
-- Map/Fold functions for expressions/insns
----------------------------------------------

map_VE :: (Var  -> Maybe Expr) -> (Expr     -> Maybe Expr)
map_EE :: (Expr -> Maybe Expr) -> (Expr     -> Maybe Expr)
map_EN :: (Expr -> Maybe Expr) -> (Insn e x -> Maybe (Insn e x))

map_VN :: (Var  -> Maybe Expr) -> (Insn e x -> Maybe (Insn e x))
map_VN = map_EN . map_EE . map_VE

map_VE f (Var v) = f v
map_VE _ _       = Nothing
                  

data Mapped a = Old a | New a
instance Monad Mapped where
  return = Old
  Old a >>= k = k a
  New a >>= k = asNew (k a)
    where asNew (Old a)   = New a
          asNew m@(New _) = m

makeTotal :: (a -> Maybe a) -> (a -> Mapped a)
makeTotal f a = case f a of Just a' -> New a'
                            Nothing -> Old a
makeTotalDefault :: b -> (a -> Maybe b) -> (a -> Mapped b)
makeTotalDefault b f a = case f a of Just b' -> New b'
                                     Nothing -> Old b
ifNew :: Mapped a -> Maybe a
ifNew (New a) = Just a
ifNew (Old _) = Nothing

type Mapping a b = a -> Mapped b

(/@/) :: Mapping b c -> Mapping a b -> Mapping a c
f /@/ g = \x -> g x >>= f


class HasExpressions a where
  mapAllSubexpressions :: Mapping Expr Expr -> Mapping a a

instance HasExpressions (Insn e x) where
  mapAllSubexpressions = error "urk!" (mapVars, (/@/), makeTotal, ifNew)
                           
mapVars :: (Var -> Maybe Expr) -> Mapping Expr Expr
mapVars f e@(Var x) = makeTotalDefault e f x
mapVars _ e         = return e


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
  case (f addr, f e) of
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

fold_EE :: (a -> Expr -> a) -> a -> Expr      -> a
fold_EN :: (a -> Expr -> a) -> a -> Insn e x -> a

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
-- Lift a insn to a Graph
----------------------------------------------

insnToG :: Insn e x -> Graph Insn e x
insnToG n@(Label _)      = mkFirst n
insnToG n@(Assign _ _)   = mkMiddle n
insnToG n@(Store _ _)    = mkMiddle n
insnToG n@(Branch _)     = mkLast n
insnToG n@(Cond _ _ _)   = mkLast n
insnToG n@(Call _ _ _ _) = mkLast n
insnToG n@(Return _)     = mkLast n
