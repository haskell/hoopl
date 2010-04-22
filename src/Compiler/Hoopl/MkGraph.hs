{-# LANGUAGE ScopedTypeVariables, GADTs #-}
module Compiler.Hoopl.MkGraph
    ( AGraph, graphOfAGraph
    , (<*>), (|*><*|), catAGraphs, addEntrySeq, addExitSeq, addBlocks, unionBlocks
    , emptyAGraph, emptyClosedAGraph, withFreshLabels
    , mkFirst, mkMiddle, mkMiddles, mkLast, mkBranch, mkLabel, mkWhileDo
    , IfThenElseable(mkIfThenElse)
    , mkEntry, mkExit
    , HooplNode(mkLabelNode, mkBranchNode)
    )
where

import Compiler.Hoopl.Label (Label)
import Compiler.Hoopl.Graph
import Compiler.Hoopl.Fuel
import qualified Compiler.Hoopl.GraphUtil as U

import Control.Monad (liftM2)

newtype AGraph n e x = A { graphOfAGraph :: FuelMonad (Graph n e x) }

class Labels l where
  withFreshLabels :: (l -> AGraph n e x) -> AGraph n e x

emptyAGraph :: AGraph n O O
emptyAGraph = A $ return GNil

emptyClosedAGraph :: AGraph n C C
emptyClosedAGraph = A $ return $ GMany NothingO BodyEmpty NothingO

{-|
As noted in the paper, we can define a single, polymorphic type of 
splicing operation with the very polymorphic type
@
  AGraph n e a -> AGraph n a x -> AGraph n e x
@
However, we feel that this operation is a bit /too/ polymorphic,
and that it's too easy for clients to use it blindly without 
thinking.  We therfore split it into several operations:

  * The '<*>' operator is true concatenation, for connecting open graphs.

  * The operators 'addEntrySeq' or 'addExitSeq' allow a client to add
    an entry or exit sequence to a graph that is closed at the entry or 
    exit.

  * The operator 'addBlocks' adds a set of basic blocks (represented as
    a closed/closed 'AGraph' to an existing graph, without changing the shape
    of the existing graph.  In some cases, it's necessary to introduce 
    a branch and a label to 'get around' the blocks added, so this operator, 
    and other functions based on it, requires a 'HooplNode' type-class constraint.
    (In GHC 6.12 this operator was called 'outOfLine'.)

  * The operator 'unionBlocks' takes the union of two sets of basic blocks,
    each of which is represented as a closed/closed 'AGraph'.  It is not 
    redundant with 'addBlocks', because 'addBlocks' requires a 'HooplNode'
    constraint but 'unionBlocks' does not.

  * The operator |*><*| splices two graphs at a closed point. The
    vertical bar stands for "closed point" just as the angle brackets
    above stand for "open point".  Unlike the <*> operator, the |*><*|
    can create a control-flow graph with dangling outedges or
    unreachable blocks.  The operator must be used carefully, so we
    have chosen a long name on purpose, to help call people's
    attention to what they're doing.

  * We have discussed a dynamic assertion about dangling outedges and
    unreachable blocks, but nothing is implemented yet.

There is some redundancy in this representation (any instance of
'addEntrySeq' is also an instance of either 'addExitSeq' or 'addBlocks'),
but because the different operators restrict polymorphism in different ways, 
we felt some redundancy would be appropriate.

-}



infixl 3 <*>
infixl 2 |*><*|
(<*>)    :: AGraph n e O -> AGraph n O x -> AGraph n e x
(|*><*|) :: AGraph n e C -> AGraph n C x -> AGraph n e x


addEntrySeq    :: AGraph n O C -> AGraph n C x -> AGraph n O x
addExitSeq     :: AGraph n e C -> AGraph n C O -> AGraph n e O
addBlocks      :: HooplNode n
               => AGraph n e x -> AGraph n C C -> AGraph n e x
unionBlocks    :: AGraph n C C -> AGraph n C C -> AGraph n C C

liftA2 :: (Graph  n a b -> Graph  n c d -> Graph  n e f)
       -> (AGraph n a b -> AGraph n c d -> AGraph n e f)

liftA2 f (A g) (A g') = A (liftM2 f g g')

addEntrySeq = liftA2 U.gSplice
addExitSeq  = liftA2 U.gSplice
unionBlocks = liftA2 U.gSplice

addBlocks (A g) (A blocks) = A $ g >>= \g -> blocks >>= add g
  where add :: HooplNode n => Graph n e x -> Graph n C C -> FuelMonad (Graph n e x)
        add (GMany e body x) (GMany NothingO body' NothingO) =
          return $ GMany e (body `BodyCat` body') x
        add g@GNil      blocks = spliceOO g blocks
        add g@(GUnit _) blocks = spliceOO g blocks
        spliceOO :: HooplNode n => Graph n O O -> Graph n C C -> FuelMonad(Graph n O O)
        spliceOO g blocks = graphOfAGraph $ withFreshLabels $ \l ->
          A (return g) <*> mkBranch l |*><*| A (return blocks) |*><*| mkLabel l


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

(<*>)    = liftA2 U.gSplice 
(|*><*|) = liftA2 U.gSplice 
catAGraphs :: [AGraph n O O] -> AGraph n O O
catAGraphs = foldr (<*>) emptyAGraph


-------------------------------------
-- constructors

mkLabel  id     = mkFirst $ mkLabelNode id
mkBranch target = mkLast  $ mkBranchNode target
mkMiddles ms = foldr (<*>) emptyAGraph (map mkMiddle ms)

instance IfThenElseable O where
  mkIfThenElse cbranch tbranch fbranch = withFreshLabels $ \(endif, ltrue, lfalse) ->
    cbranch ltrue lfalse |*><*|
      mkLabel ltrue  <*> tbranch <*> mkBranch endif |*><*|
      mkLabel lfalse <*> fbranch <*> mkBranch endif |*><*|
      mkLabel endif

{-
  fallThroughTo id g = g <*> mkBranch id
-}

instance IfThenElseable C where
  mkIfThenElse cbranch tbranch fbranch = withFreshLabels $ \(ltrue, lfalse) ->
    cbranch ltrue lfalse |*><*|
       mkLabel ltrue  <*> tbranch |*><*|
       mkLabel lfalse <*> fbranch
{-
  fallThroughTo _ g = g
-}

mkWhileDo cbranch body = withFreshLabels $ \(test, head, endwhile) ->
     -- Forrest Baskett's while-loop layout
  mkBranch test |*><*|
    mkLabel head <*> body <*> mkBranch test |*><*|
    mkLabel test <*> cbranch head endwhile  |*><*|
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
  withFreshLabels f = A $ freshLabel >>= (graphOfAGraph . f)

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


mkExit   block = A $ return $ GMany NothingO      BodyEmpty (JustO block)
mkEntry  block = A $ return $ GMany (JustO block) BodyEmpty NothingO

mkFirst  = mkExit  . ZFirst
mkLast   = mkEntry . ZLast
mkMiddle = A . return  . GUnit . ZMiddle
