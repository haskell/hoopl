{-# OPTIONS_GHC -Wall -fwarn-incomplete-patterns #-}
{-# LANGUAGE ScopedTypeVariables, GADTs, PatternGuards #-}
module Simplify (simplify) where

import Compiler.Hoopl
import IR
import OptSupport

-- Simplification ("constant folding")
simplify :: FwdRewrite Node a
simplify = deepFwdRw $ shallowFwdRw simp
  where
    simp node _ = s node >>= return . nodeToA
    s :: Node e x -> Maybe (Node e x)
    s (Cond (Lit (Bool True))  t _) = Just $ Branch t
    s (Cond (Lit (Bool False)) f _) = Just $ Branch f
    s n = map_EN (map_EE s_e) n
    s_e (Binop opr e1 e2)
      | (Just op, Lit (Int i1), Lit (Int i2)) <- (intOp opr, e1, e2) =
          Just $ Lit $ Int  $ op i1 i2
      | (Just op, Lit (Int i1), Lit (Int i2)) <- (cmpOp opr, e1, e2) =
          Just $ Lit $ Bool $ op i1 i2
    s_e _ = Nothing
    intOp Add = Just (+)
    intOp Sub = Just (-)
    intOp Mul = Just (*)
    intOp Div = Just div
    intOp _   = Nothing
    cmpOp Eq  = Just (==)
    cmpOp Ne  = Just (/=)
    cmpOp Gt  = Just (>)
    cmpOp Lt  = Just (<)
    cmpOp Gte = Just (>=)
    cmpOp Lte = Just (<=)
    cmpOp _   = Nothing
