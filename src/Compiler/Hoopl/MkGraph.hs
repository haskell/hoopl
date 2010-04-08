{-# LANGUAGE ScopedTypeVariables #-}
module Compiler.Hoopl.MkGraph
    ( AGraph, (<*>), gCatClosed
    , emptyAGraph, emptyClosedAGraph, withFreshLabels
    , mkFirst, mkMiddle, mkMiddles, mkLast, mkEntry, mkBranch, mkLabel, mkWhileDo
    , addEntrySeq, addExitSeq, catAGraphs
    , IfThenElseable(mkIfThenElse)
    , HooplNode(mkLabelNode, mkBranchNode)
    )
where

import Compiler.Hoopl.Label (Label)
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Fuel
import qualified Compiler.Hoopl.GraphUtil as U

import Control.Monad (liftM2)

type AGraph n e x = FuelMonad (Graph n e x)

infixr 3 <*>
(<*>) :: AGraph n e O -> AGraph n O x -> AGraph n e x

class Labels l where
  withFreshLabels :: (l -> AGraph n e x) -> AGraph n e x

emptyAGraph :: AGraph n O O
emptyAGraph = return GNil

emptyClosedAGraph :: AGraph n C C
emptyClosedAGraph = return $ GMany NothingO BodyEmpty NothingO

addEntrySeq    :: AGraph n O C -> AGraph n C x -> AGraph n O x
addExitSeq     :: AGraph n e C -> AGraph n C O -> AGraph n e O
gCatClosed     :: AGraph n e C -> AGraph n C x -> AGraph n e x

addEntrySeq = liftM2 U.addEntrySeq
addExitSeq  = liftM2 U.addExitSeq
gCatClosed  = liftM2 U.gCatClosed

mkFirst  :: n C O -> AGraph n C O
mkMiddle :: n O O -> AGraph n O O
mkLast   :: n O C -> AGraph n O C

mkLabel :: HooplNode n => Label -> AGraph n C O -- graph contains the label

-- below for convenience
mkMiddles :: [n O O] -> AGraph n O O
mkEntry   :: Block n O C -> AGraph n O C
mkExit    :: Block n C O -> AGraph n C O

class Edges n => HooplNode n where
  mkBranchNode :: Label -> n O C
  mkLabelNode  :: Label -> n C O

mkBranch :: HooplNode n => Label -> AGraph n O C

class IfThenElseable x where
  mkIfThenElse :: HooplNode n
               => (Label -> Label -> AGraph n O C) -- branch condition
               -> AGraph n O x   -- code in the 'then' branch
               -> AGraph n O x   -- code in the 'else' branch 
               -> AGraph n O x   -- resulting if-then-else construct
{-
  fallThroughTo :: Node n
                => Label -> AGraph n e x -> AGraph n e C
-}

mkWhileDo    :: HooplNode n
             => (Label -> Label -> AGraph n O C) -- loop condition
             -> AGraph n O O  -- body of the bloop
             -> AGraph n O O -- the final while loop

-- ================================================================
--                          IMPLEMENTATION
-- ================================================================

(<*>) = liftM2 U.gCat 

catAGraphs :: [AGraph n O O] -> AGraph n O O
catAGraphs = foldr (<*>) emptyAGraph

-------------------------------------
-- constructors

mkLabel  id     = mkFirst $ mkLabelNode id
mkBranch target = mkLast  $ mkBranchNode target
mkMiddles ms = foldr (<*>) (return GNil) (map mkMiddle ms)


{-
outOfLine (AGraph g :: AGraph n C C) = AGraph g'
  where g' :: UniqSM (Graph n O O)
        g' = do zgraph <- g
                case zgraph of
                  GF (Z.ZE_C _) _ Z.ZX_C ->
                      do id <- freshLabel "outOfLine"
                         return $ Z.mkLast (mkBranchNode id) <**> zgraph <**>
                                  Z.mkLabel id
                  _ -> panic "tried to outOfLine a graph open at one or both ends"
-}

instance IfThenElseable O where
  mkIfThenElse cbranch tbranch fbranch = do
    endif  <- freshLabel
    ltrue  <- freshLabel
    lfalse <- freshLabel
    cbranch ltrue lfalse `addEntrySeq`
      (mkLabel ltrue  <*> tbranch <*> mkBranch endif) `gCatClosed`
      (mkLabel lfalse <*> fbranch <*> mkBranch endif) `gCatClosed`
      mkLabel endif

{-
  fallThroughTo id g = g <*> mkBranch id
-}

instance IfThenElseable C where
  mkIfThenElse cbranch tbranch fbranch = do
    ltrue  <- freshLabel
    lfalse <- freshLabel
    cbranch ltrue lfalse `gCatClosed`
       mkLabel ltrue  <*> tbranch `gCatClosed`
       mkLabel lfalse <*> fbranch
{-
  fallThroughTo _ g = g
-}

mkWhileDo cbranch body = do
  test <- freshLabel
  head <- freshLabel
  endwhile <- freshLabel
     -- Forrest Baskett's while-loop layout
  mkBranch test `gCatClosed`
    mkLabel head <*> body <*> mkBranch test `gCatClosed`
    mkLabel test <*> cbranch head endwhile  `gCatClosed`
    mkLabel endwhile

-------------------------------------
-- Debugging

{-
pprAGraph :: (Outputable m, LastNode l, Outputable l) => AGraph n e x -> UniqSM SDoc
pprAGraph g = graphOfAGraph g >>= return . ppr
-}

{-
Note [Branch follows branch]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Why do we say it's ok for a Branch to follow a Branch?
Because the standard constructor mkLabel-- has fall-through
semantics. So if you do a mkLabel, you finish the current block,
giving it a label, and start a new one that branches to that label.
Emitting a Branch at this point is fine: 
       goto L1; L2: ...stuff... 
-}


instance Labels Label where
  withFreshLabels f = freshLabel >>= f

instance (Labels l1, Labels l2) => Labels (l1, l2) where
  withFreshLabels f = withFreshLabels $ \l1 ->
                      withFreshLabels $ \l2 ->
                      f (l1, l2)

instance (Labels l1, Labels l2, Labels l3) => Labels (l1, l2, l3) where
  withFreshLabels f = withFreshLabels $ \l1 ->
                      withFreshLabels $ \l2 ->
                      withFreshLabels $ \l3 ->
                      f (l1, l2, l3)

instance (Labels l1, Labels l2, Labels l3, Labels l4) => Labels (l1, l2, l3, l4) where
  withFreshLabels f = withFreshLabels $ \l1 ->
                      withFreshLabels $ \l2 ->
                      withFreshLabels $ \l3 ->
                      withFreshLabels $ \l4 ->
                      f (l1, l2, l3, l4)


mkExit   block = return $ GMany NothingO      BodyEmpty (JustO block)
mkEntry  block = return $ GMany (JustO block) BodyEmpty NothingO

mkFirst  = mkExit  . BUnit
mkLast   = mkEntry . BUnit
mkMiddle = return  . GUnit . BUnit
