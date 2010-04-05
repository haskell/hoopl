{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies #-}

{- Notes about the genesis of Hoopl5
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As well as addressing your concerns I had some of my own:

* In Hoopl4, a closed/closed graph starts with a distinguished
  closed/closed block (the entry block).  But this block is
  *un-labelled*.  That means that there is no way to branch back to
  the entry point of a procedure, which seems a bit unclean.

* In general I have to admit that it does seem a bit unintuitive to
  have block that is
	a) closed on entry, but
	b) does not have a label

* If you look at MkZipCfgCmm you'll see stuff like this:
     mkCmmIfThen e tbranch
       = withFreshLabel "end of if"     $ \endif ->
         withFreshLabel "start of then" $ \tid ->
         mkCbranch e tid endif <*>
         mkLabel tid   <*> tbranch <*> mkBranch endif <*>
         mkLabel endif

   We are trying to present a user model *graphs* as
	a sequence, connected by <*>,
	of little graphs
   Moreover, one of the little graphs is (mkLabel BlockId), and I
   don't see how to make a graph for that in Hoopl4.

   (Norman I know that this may be what you have been trying to say
   about "graphs under construction" for some time, but looking at
   MkZipCfgCmm made it far more concrete for me.)


Specifically, in Hoopl5:

* The ARF type is no longer overloaded over the LiftNode class.  
  It has a simple and beautiful type.

* I put the BlockId back in a first node, as John wanted.

* To make it possible to branch to the label of the entry block of a
  Graph it does make sense to put that block in the Graph that is
  the main payload of the graph

* That militates in favour of a Maybe-kind-of-thing on entry to a
  Graph, just as Norman wanted.  It's called Head, dual to Tail.

* However I am Very Very Keen to maintain the similar properties of
  nodes, blocks, graphs; and in particular the single point of entry.
  (For a multi-entry procedure, the procedure can be represented by a
  Graph plus a bunch of BlockIds, rather than a Graph.)  So I
  made the Head contain the BlockId of the entry point.

* The Graph in a Graph is a finite map, as you wanted.  Notice
  that this embodies an invariant: a BlockId must map to a block whose
  entry point is that BlockId.

* I've added a layer, using arfBlocks/arbBlocks.  Admittedly the
  type doesn't fit the same pattern, but it's useful structuring

* You should think of a Graph as a user-visible type; perhaps
  this is the kind of graph that might form the body of a procedure.
  Moreover, perhaps rewriteAndAnlyseForward should take a Graph
  rather than a Graph, and call arbBlocks.

* With that in mind I was happy to introduce the analogous invariant
  for the exit block in Tail; it is very very convenient to have that
  BlockId (cached though it may be) to hand.

* Because graphs are made out of blocks, it's easy to have a
  constructor for the empty ggraph, and we don't need any stinkikng
  smart constructor to keep nil in its place.  But if we moved nil to
  blocks, we'd need a smart constructor for graphs *and* one for
  blocks.  (Because unlike graphs, blocks *are* made from other
  blocks.


-}

module Hoopl5 where

import qualified Data.IntMap as M
import qualified Data.IntSet as S

-----------------------------------------------------------------------------
--		Graphs
-----------------------------------------------------------------------------

data O
data C

-- Blocks are always non-empty
data Block n e x where
  BUnit :: n e x -> Block n e x
  BCat  :: Block n e O -> Block n O x -> Block n e x

data Graph n e x where
  GNil  :: Graph n O O
  GUnit :: Block n O O -> Graph n O O
  GMany :: IfOpen e (Block n O C) -> BlockMap (Block n C C)
        -> IfOpen x (Block n C O) -> Graph n e x

data IfOpen e thing where
  IsOpen    :: thing -> IfOpen O thing
  IsNotOpen ::          IfOpen C thing

-----------------------------------------------------------------------------
--		Defined here but not used
-----------------------------------------------------------------------------

-- Singletons
--   OO   GUnit
--   CO   GMany (NoHead l) [] (Tail l b)
--   OC   GMany (Head b)   []  NoTail
--   CC   GMany (NoHead l) [b] NoTail

class Edges thing where
  closedId :: thing e x -> IfClosed e BlockId
  successors :: thing e C -> [BlockId]

instance Edges n => Edges (Block n) where
  closedId (BUnit n) = closedId n
  closedId (b `BCat` _) = closedId b
  successors (BUnit n)   = successors n
  successors (BCat _ b)  = successors b

data IfClosed e thing where
  IsClosed    :: thing -> IfClosed C thing
  IsNotClosed ::          IfClosed O thing


-----------------------------------------------------------------------------
--	RG: an internal data type for graphs under construction
--          TOTALLY internal to Hoopl
-----------------------------------------------------------------------------

-- "RG" stands for "rewritten graph", and embodies
-- both the result graph and its internal facts

data RL n f x where
  RL     :: BlockId -> f -> RG n f C x -> RL n f x
  RLMany :: GraphWithFacts n f -> RL n f C

data RG n f e x where	-- Will have facts too in due course
  RGNil   :: RG n f a a
  RGBlock :: Block n e x -> RG n f e x
  RGCatO  :: RG n f e O -> RG n f O x -> RG n f e x
  RGCatC  :: RG n f e C -> RL n f x   -> RG n f e x

type GraphWithFacts n f = (BlockMap (Block n C C), FactBase f)
  -- A Graph together with the facts for that graph
  -- The domains of the two maps should be identical

-- 'normalise' converts a closed/closed result graph into a Graph
-- It uses three auxiliary functions, 
-- specialised for various argument shapes
normRL :: RL n f C -> GraphWithFacts n f
normRL (RL l f b)  = normRG l f b
normRL (RLMany bg) = bg

normRL_O :: RL n f O -> RG n f O C -> GraphWithFacts n f
normRL_O (RL l f b) rg = normRG_O l f b rg

normRG :: BlockId -> f -> RG n f C C -> GraphWithFacts n f
normRG l f (RGBlock b)      = unitBWF l f b
normRG l f (RGCatO rg1 rg2) = normRG_O l f rg1 rg2
normRG l f (RGCatC rg1 rg2) = normRG l f rg1 `unionBWF` normRL rg2

normRG_O :: BlockId -> f -> RG n f C O -> RG n f O C -> GraphWithFacts n f
-- normalise (rg1 `RGCatO` rg2)
normRG_O l f (RGBlock b)      rg  = normB l f b rg
normRG_O l f (RGCatO rg1 rg2) rg3 = normRG_O l f rg1 (rg2 `RGCatO` rg3)
normRG_O l f (RGCatC rg1 rg2) rg3 = normRG l f rg1 `unionBWF` normRL_O rg2 rg3

normB :: BlockId -> f -> Block n C O -> RG n f O C -> GraphWithFacts n f
-- normalise (Block b `RGCatO` rg2)
normB l f b1 (RGBlock b2)     = unitBWF l f (b1 `BCat` b2)
normB l f b  (RGCatO rg1 rg2) = normB_O l f b rg1 rg2
normB l f b  (RGCatC rg1 rg2) = normB  l f b rg1 `unionBWF` normRL rg2

normB_O :: BlockId -> f -> Block n C O -> RG n f O O -> RG n f O C
        -> GraphWithFacts n f
-- normalise (Block b `RGCatO` rg2 `RGCatO` rg3)
normB_O l f  b  RGNil           rg  = normB l f b rg
normB_O l f bh (RGBlock bt)     rg  = normB l f (bh `BCat` bt) rg
normB_O l f b  (RGCatC rg1 rg2) rg3 = normB l f b rg1 `unionBWF` normRL_O rg2 rg3
normB_O l f b  (RGCatO rg1 rg2) rg3 = normB_O l f b rg1 (rg2 `RGCatO` rg3)

noBWF :: GraphWithFacts n f
noBWF = (noBlocks, noFacts)

unitBWF :: BlockId -> f -> Block n C C -> GraphWithFacts n f
unitBWF lbl f b = (unitBlock lbl b, unitFactBase lbl f)

unionBWF :: GraphWithFacts n f -> GraphWithFacts n f -> GraphWithFacts n f
unionBWF (bg1, fb1) (bg2, fb2) = (bg1 `unionBlocks` bg2, fb1 `unionFactBase` fb2)

-----------------------------------------------------------------------------
--		DataflowLattice
-----------------------------------------------------------------------------

data DataflowLattice a = DataflowLattice  { 
  fact_name       :: String,                   -- Documentation
  fact_bot        :: a,                        -- Lattice bottom element
  fact_extend     :: a -> a -> (ChangeFlag,a), -- Lattice join plus change flag
  fact_do_logging :: Bool                      -- log changes
}

data ChangeFlag = NoChange | SomeChange

-----------------------------------------------------------------------------
--		The main Hoopl API
-----------------------------------------------------------------------------

type ForwardTransfer n f 
  = forall e x. f -> n e x -> TailFactF x f 

type ForwardRewrite n f 
  = forall e x. f -> n e x -> Maybe (AGraph n e x)

type family   TailFactF x f :: *
type instance TailFactF C f = [(BlockId, f)] 
type instance TailFactF O f = f

data AGraph n e x = AGraph 	-- Stub for now


-----------------------------------------------------------------------------
--      TxFactBase: a FactBase with ChangeFlag information
-----------------------------------------------------------------------------

-- The TxFactBase is an accumulating parameter, threaded through all
-- the analysis/transformation of each block in the g_blocks of a grpah.
-- It carries a ChangeFlag with it, and a set of BlockIds
-- to monitor. Updates to other BlockIds don't affect the ChangeFlag
data TxFactBase n f
  = TxFB { tfb_fbase :: FactBase f

         , tfb_cha   :: ChangeFlag
         , tfb_bids  :: BlockSet   -- Update change flag iff these blocks change
                                   -- These are BlockIds of the *original* 
                                   -- (not transformed) blocks

         , tfb_blks  :: GraphWithFacts n f  -- Transformed blocks
    }

updateFact :: DataflowLattice f -> BlockSet
           -> (BlockId, f)
           -> (ChangeFlag, FactBase f) 
           -> (ChangeFlag, FactBase f)
-- Update a TxFactBase, setting the change flag iff
--   a) the new fact adds information...
--   b) for a block in the BlockSet in the TxFactBase
updateFact lat lbls (lbl, new_fact) (cha, fbase)
  | NoChange <- cha2        = (cha,        fbase)
  | lbl `elemBlockSet` lbls = (SomeChange, new_fbase)
  | otherwise               = (cha,        new_fbase)
  where
    old_fact = lookupFact lat fbase lbl
    (cha2, res_fact) = fact_extend lat old_fact new_fact
    new_fbase = extendFactBase fbase lbl res_fact

fixpoint :: forall n f. 
            DataflowLattice f
         -> (BlockId -> Block n C C -> FactBase f 
                     -> FuelMonad ([(BlockId,f)], RL n f C))
         -> [(BlockId, Block n C C)]
         -> FactBase f 
         -> FuelMonad (FactBase f, GraphWithFacts n f)
fixpoint lat do_block blocks init_fbase
  = do { fuel <- getFuel  
       ; tx_fb <- loop fuel init_fbase
       ; return (tfb_fbase tx_fb `deleteFromFactBase` blocks, tfb_blks tx_fb) }
	     -- The successors of the Graph are the the BlockIds for which
	     -- we have facts, that are *not* in the blocks of the graph
  where
    tx_blocks :: [(BlockId, Block n C C)] 
              -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    tx_blocks []     tx_fb = return tx_fb
    tx_blocks ((lbl,blk):bs) tx_fb = do { tx_fb1 <- tx_block lbl blk tx_fb
                                        ; tx_blocks bs tx_fb1 }

    tx_block :: BlockId -> Block n C C 
             -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    tx_block lbl blk (TxFB { tfb_fbase = fbase, tfb_bids = lbls
                           , tfb_blks = blks, tfb_cha = cha })
      = do { (out_facts, rg) <- do_block lbl blk fbase
           ; let (cha',fbase') = foldr (updateFact lat lbls) (cha,fbase) out_facts
                 f = lookupFact lat fbase lbl
		-- tfb_blks will be discarded unless we have 
		-- reached a fixed point, so it doesn't matter
		-- whether we get f from fbase or fbase'
           ; return (TxFB { tfb_bids = extendBlockSet lbls lbl
                          , tfb_blks = normRL rg `unionBWF` blks
                          , tfb_fbase = fbase', tfb_cha = cha' }) }

    loop :: Fuel -> FactBase f -> FuelMonad (TxFactBase n f)
    loop fuel fbase 
      = do { let init_tx_fb = TxFB { tfb_fbase = fbase
                                   , tfb_cha   = NoChange
                                   , tfb_blks  = noBWF
                                   , tfb_bids  = emptyBlockSet }
           ; tx_fb <- tx_blocks blocks init_tx_fb
           ; case tfb_cha tx_fb of
               NoChange   -> return tx_fb
               SomeChange -> do { setFuel fuel; loop fuel (tfb_fbase tx_fb) } }

-----------------------------------------------------------------------------
--		Transfer functions
-----------------------------------------------------------------------------

-- Keys to the castle: a generic transfer function for each shape
-- Here's the idea: we start with single-n transfer functions,
-- move to basic-block transfer functions (we have exactly four shapes),
-- then finally to graph transfer functions (which requires iteration).

type ARF thing n f = forall e x. f -> thing e x -> FuelMonad (TailFactF x f, RG n f e x)

type ARF_Node  n f = ARF n         n f
type ARF_Block n f = ARF (Block n) n f
type ARF_Graph n f = ARF (Graph n) n f
-----------------------------------------------------------------------------

arfNodeNoRW :: forall n f. ForwardTransfer n f -> ARF_Node n f
 -- Lifts ForwardTransfer to ARF_Node; simple transfer only
arfNodeNoRW transfer_fn f node
  = return (transfer_fn f node, RGBlock (BUnit node))

arfNode :: forall n f.
           Edges n
        => DataflowLattice f
        -> ForwardTransfer n f
        -> ForwardRewrite n f
        -> ARF_Node n f
        -> ARF_Node n f
-- Lifts (ForwardTransfer,ForwardRewrite) to ARF_Node; 
-- this time we do rewriting as well. 
-- The ARF_Graph parameters specifies what to do with the rewritten graph
arfNode lattice transfer_fn rewrite_fn arf_node f node
  = do { mb_g <- withFuel (rewrite_fn f node)
       ; case mb_g of
           Nothing -> arfNodeNoRW transfer_fn f node
      	   Just ag -> do { g <- graphOfAGraph ag
      		         ; arfGraph lattice arf_node f g } }

arfBlock :: forall n f. ARF_Node n f -> ARF_Block n f
-- Lift from nodes to blocks
arfBlock arf_node f (BUnit node)   = arf_node f node
arfBlock arf_node f (BCat hd mids) = do { (f1,g1) <- arfBlock arf_node f  hd
                                        ; (f2,g2) <- arfBlock arf_node f1 mids
	                                ; return (f2, g1 `RGCatO` g2) }

arfBlocks :: forall n f. DataflowLattice f 
          -> ARF_Node n f -> FactBase f -> BlockMap (Block n C C) 
          -> FuelMonad (FactBase f, GraphWithFacts n f)
		-- Outgoing factbase is restricted to BlockIds *not* in
		-- in the Graph; the facts for BlockIds
		-- *in* the Graph are in the GraphWithFacts
arfBlocks lattice arf_node init_fbase blocks
  = fixpoint lattice do_block 
             (forwardBlockList (factBaseBlockIds init_fbase) blocks) 
             init_fbase
  where
    do_block :: BlockId -> Block n C C -> FactBase f
             -> FuelMonad ([(BlockId,f)], RL n f C)
    do_block l blk fbase = do { let f = lookupFact lattice fbase l
                              ; (fs, rg) <- arfBlock arf_node f blk
			      ; return (fs, RL l f rg) }

arfGraph :: forall n f. Edges n => DataflowLattice f -> ARF_Node n f -> ARF_Graph n f
-- Lift from blocks to graphs
arfGraph _       _        f GNil        = return (f, RGNil)
arfGraph _       arf_node f (GUnit blk) = arfBlock arf_node f blk
arfGraph lattice arf_node f (GMany entry blks exit)
  = do { (f1, entry') <- arf_entry f entry
       ; (f2, blks')  <- arfBlocks lattice arf_node (mkFactBase f1) blks
       ; (f3, exit')  <- arf_exit f2 exit 
       ; return (f3, entry' `RGCatC` RLMany blks' `RGCatC` exit') }
  where
    arf_entry :: f -> IfOpen e (Block n O C)
              -> FuelMonad ([(BlockId,f)], RG n f e C)
    arf_entry fh IsNotOpen   = return ([], RGNil)
    arf_entry fh (IsOpen b) = arfBlock arf_node fh b

    arf_exit :: FactBase f -> IfOpen x (Block n C O)
             -> FuelMonad (TailFactF x f, RL n f x)
    arf_exit fb IsNotOpen    = return (factBaseList fb, RLMany noBWF)
    arf_exit fb (IsOpen blk) = do { let ft = lookupFact lattice fb lt
                                  ; (f1, rg) <- arfBlock arf_node ft blk
                                  ; return (f1, RL lt ft rg) }
      where IsClosed lt :: IfClosed C BlockId = closedId blk

forwardBlockList :: [BlockId] -> BlockMap (Block n C C) -> [(BlockId,Block n C C)]
-- This produces a list of blocks in order suitable for forward analysis.
-- ToDo: Do a topological sort to improve convergence rate of fixpoint
--       This will require a (HavingSuccessors l) class constraint
forwardBlockList  _ blks = blocksToList blks

----------------------------------------------------------------
--       The pièce de resistance: cunning transfer functions
----------------------------------------------------------------

pureAnalysis :: Edges n => DataflowLattice f -> ForwardTransfer n f -> ARF_Graph n f
pureAnalysis lattice f = arfGraph lattice (arfNodeNoRW f)

analyseAndRewriteFwd
   :: forall n f.
      Edges n
   => DataflowLattice f
   -> ForwardTransfer n f
   -> ForwardRewrite n f
   -> RewritingDepth
   -> FactBase f
   -> BlockMap (Block n C C)
   -> FuelMonad (BlockMap (Block n C C), FactBase f)

data RewritingDepth = RewriteShallow | RewriteDeep
-- When a transformation proposes to rewrite a node, 
-- you can either ask the system to
--  * "shallow": accept the new graph, analyse it without further rewriting
--  * "deep": recursively analyse-and-rewrite the new graph

analyseAndRewriteFwd lattice transfers rewrites depth facts graph
  = do { (_, gwf) <- arfBlocks lattice arf_node facts graph
       ; return gwf }
  where 
    arf_node, rec_node :: ARF_Node n f
    arf_node = arfNode lattice transfers rewrites rec_node

    rec_node = case depth of
                RewriteShallow -> arfNodeNoRW transfers
                RewriteDeep    -> arf_node

-----------------------------------------------------------------------------
--		Backward rewriting
-----------------------------------------------------------------------------

type BackwardTransfer n f 
  = forall e x. TailFactB x f -> n e x -> f 
type BackwardRewrite n f 
  = forall e x. TailFactB x f -> n e x -> Maybe (AGraph n e x)

type ARB thing n f = forall e x. TailFactB x f -> thing e x
                              -> FuelMonad (f, RG n f e x)

type family   TailFactB x f :: *
type instance TailFactB C f = FactBase f
type instance TailFactB O f = f

type ARB_Node  n f = ARB n         n f
type ARB_Block n f = ARB (Block n) n f
type ARB_Graph n f = ARB (Graph n) n f

arbNodeNoRW :: forall n f . BackwardTransfer n f -> ARB_Node n f
-- Lifts BackwardTransfer to ARB_Node; simple transfer only
arbNodeNoRW transfer_fn f node
  = return (transfer_fn f node, RGBlock (BUnit node))

arbNode :: forall n f.
           Edges n
        => DataflowLattice f
        -> BackwardTransfer n f
        -> BackwardRewrite n f
        -> ARB_Node n f
        -> ARB_Node n f
-- Lifts (BackwardTransfer,BackwardRewrite) to ARB_Node; 
-- this time we do rewriting as well. 
-- The ARB_Graph parameters specifies what to do with the rewritten graph
arbNode lattice transfer_fn rewrite_fn arf_node f node
  = do { mb_g <- withFuel (rewrite_fn f node)
       ; case mb_g of
           Nothing -> arbNodeNoRW transfer_fn f node
      	   Just ag -> do { g <- graphOfAGraph ag
      		         ; arbGraph lattice arf_node f (closedId node) g } }

arbBlock :: forall n f. ARB_Node n f -> ARB_Block n f
-- Lift from nodes to blocks
arbBlock arb_node f (BUnit node) = arb_node f node
arbBlock arb_node f (BCat b1 b2) = do { (f2,g2) <- arbBlock arb_node f  b2
                                      ; (f1,g1) <- arbBlock arb_node f2 b1
	                              ; return (f1, g1 `RGCatO` g2) }


arbBlocks :: forall n f. DataflowLattice f 
          -> ARB_Node n f -> FactBase f
          -> BlockMap (Block n C C) -> FuelMonad (FactBase f, GraphWithFacts n f)
arbBlocks lattice arb_node init_fbase blocks
  = fixpoint lattice do_block 
             (backwardBlockList (factBaseBlockIds init_fbase) blocks) 
             init_fbase
  where
    do_block :: BlockId -> Block n C C -> FactBase f
             -> FuelMonad ([(BlockId,f)], RL n f C)
    do_block l b fbase = do { (fb, rg) <- arbBlock arb_node fbase b
			    ; let f = lookupFact lattice fbase l
                            ; return ([(l,fb)], RL l f rg) }

arbGraph :: forall n f e x. 
            Edges n
         => DataflowLattice f
         -> ARB_Node n f
         -> TailFactB x f
         -> IfClosed e BlockId
         -> Graph n e x
         -> FuelMonad (f, RG n f e x)
arbGraph _       _        f _    GNil        = return (f, RGNil)
arbGraph _       arb_node f _   (GUnit blk) = arbBlock arb_node f blk
arbGraph lattice arb_node f eid (GMany entry blks exit)
  = do { (f1, exit')  <- arb_exit f exit
       ; (f2, blks')  <- arbBlocks lattice arb_node f1 blks
       ; (f3, entry') <- arb_entry f2 eid entry 
       ; return (f3, entry' `RGCatC` RLMany blks' `RGCatC` exit') }
  where
    arb_entry :: FactBase f -> IfClosed e BlockId -> IfOpen e (Block n O C) 
              -> FuelMonad (f, RG n f e C)
    arb_entry fbase (IsClosed eid) IsNotOpen = return (lookupFact lattice fbase eid,
                                                       RGNil)
    arb_entry fbase IsNotClosed (IsOpen blk) = arbBlock arb_node fbase blk

    arb_exit :: TailFactB x f -> IfOpen x (Block n C O)
             -> FuelMonad (FactBase f, RL n f x)
    arb_exit ft IsNotOpen        = return (ft, RLMany noBWF)
    arb_exit ft (IsOpen blk) = do { (f1, rg) <- arbBlock arb_node ft blk
                                     ; return (mkFactBase [(lt,f1)], RL lt f1 rg) }
      where IsClosed lt :: IfClosed C BlockId = closedId blk

backwardBlockList :: [BlockId] -> BlockMap (Block n C C) -> [(BlockId,Block n C C)]
-- This produces a list of blocks in order suitable for backward analysis.
backwardBlockList _ blks = blocksToList blks

analyseAndRewriteBwd
   :: forall n f.
      Edges n
   => DataflowLattice f
   -> BackwardTransfer n f
   -> BackwardRewrite n f
   -> RewritingDepth
   -> FactBase f
   -> BlockMap (Block n C C)
   -> FuelMonad (BlockMap (Block n C C), FactBase f)

analyseAndRewriteBwd lattice transfers rewrites depth facts graph
  = do { (_, gwf) <- arbBlocks lattice arb_node facts graph
       ; return gwf }
  where 
    arb_node, rec_node :: ARB_Node n f
    arb_node = arbNode lattice transfers rewrites rec_node

    rec_node = case depth of
                RewriteShallow -> arbNodeNoRW transfers
                RewriteDeep    -> arb_node

-----------------------------------------------------------------------------
--		The fuel monad
-----------------------------------------------------------------------------

type Uniques = Int
type Fuel    = Int

newtype FuelMonad a = FM { unFM :: Fuel -> Uniques -> (a, Fuel, Uniques) }

instance Monad FuelMonad where
  return x = FM (\f u -> (x,f,u))
  m >>= k  = FM (\f u -> case unFM m f u of (r,f',u') -> unFM (k r) f' u')

withFuel :: Maybe a -> FuelMonad (Maybe a)
withFuel Nothing  = return Nothing
withFuel (Just r) = FM (\f u -> if f==0 then (Nothing, f, u)
                                else (Just r, f-1, u))

getFuel :: FuelMonad Fuel
getFuel = FM (\f u -> (f,f,u))

setFuel :: Fuel -> FuelMonad ()
setFuel f = FM (\_ u -> ((), f, u))

graphOfAGraph :: AGraph node e x -> FuelMonad (Graph node e x)
graphOfAGraph = error "urk" 	-- Stub

-----------------------------------------------------------------------------
--		BlockId, FactBase, BlockSet
-----------------------------------------------------------------------------

type BlockId = Int

mkBlockId :: Int -> BlockId
mkBlockId uniq = uniq

----------------------
type BlockMap a = M.IntMap a

noBlocks :: BlockMap (Block n C C)
noBlocks = M.empty

unitBlock :: BlockId -> Block n C C -> BlockMap (Block n C C)
unitBlock = M.singleton

addBlock :: BlockId -> Block n C C -> BlockMap (Block n C C) -> BlockMap (Block n C C)
addBlock = M.insert

unionBlocks :: BlockMap (Block n C C) -> BlockMap (Block n C C) -> BlockMap (Block n C C)
unionBlocks = M.union

blocksToList :: BlockMap (Block n C C) -> [(BlockId,Block n C C)]
blocksToList = M.toList

----------------------
type FactBase a = M.IntMap a

noFacts :: FactBase f
noFacts = M.empty

mkFactBase :: [(BlockId, f)] -> FactBase f
mkFactBase prs = M.fromList prs

unitFactBase :: BlockId -> f -> FactBase f
unitFactBase = M.singleton

lookupFact :: DataflowLattice f -> FactBase f -> BlockId -> f
lookupFact lattice env blk_id 
  = case M.lookup blk_id env of
      Just f  -> f
      Nothing -> fact_bot lattice

extendFactBase :: FactBase f -> BlockId -> f -> FactBase f
extendFactBase env blk_id f = M.insert blk_id f env

unionFactBase :: FactBase f -> FactBase f -> FactBase f
unionFactBase = M.union

factBaseBlockIds :: FactBase f -> [BlockId]
factBaseBlockIds = M.keys

factBaseList :: FactBase f -> [(BlockId, f)]
factBaseList = M.toList 

deleteFromFactBase :: FactBase f -> [(BlockId,a)] -> FactBase f
deleteFromFactBase fb blks = foldr (M.delete . fst) fb blks

----------------------
type BlockSet = S.IntSet

emptyBlockSet :: BlockSet
emptyBlockSet = S.empty

extendBlockSet :: BlockSet -> BlockId -> BlockSet
extendBlockSet bids bid = S.insert bid bids

elemBlockSet :: BlockId -> BlockSet -> Bool
elemBlockSet bid bids = S.member bid bids

blockSetElems :: BlockSet -> [BlockId]
blockSetElems = S.toList

minusBlockSet :: BlockSet -> BlockSet -> BlockSet
minusBlockSet = S.difference

unionBlockSet :: BlockSet -> BlockSet -> BlockSet
unionBlockSet = S.union

mkBlockSet :: [BlockId] -> BlockSet
mkBlockSet = S.fromList

----------------------------------------------------------------
--
--   DROPPINGS follow...
--
----------------------------------------------------------------
{-

data OCFlag oc where
  IsOpen   :: OCFlag O
  IsClosed :: OCFlag C

class IsOC oc where
  ocFlag :: OCFlag oc

instance IsOC O where
  ocFlag = IsOpen
instance IsOC C where
  ocFlag = IsClosed

mkIfThenElse :: forall n x. IsOC x 
             => (BlockId -> BlockId -> n O C)	-- The conditional branch instruction
             -> (BlockId -> n C O)		-- Make a head node 
	     -> (BlockId -> n O C)		-- Make an unconditional branch
	     -> Graph n O x -> Graph n O x	-- Then and else branches
	     -> [BlockId]			-- Block supply
             -> Graph n O x			-- The complete thing
mkIfThenElse mk_cbranch mk_lbl mk_branch then_g else_g (tl:el:jl:_)
  = case (ocFlag :: OCFlag x) of
      IsOpen   -> gUnitOC (mk_cbranch tl el)
                  `pCat` (mk_lbl_g tl `pCat` then_g `pCat` mk_branch_g jl)
                  `pCat` (mk_lbl_g el `pCat` else_g `pCat` mk_branch_g jl)
                  `pCat` (mk_lbl_g jl)
      IsClosed -> gUnitOC (mk_cbranch tl el)
                  `pCat` (mk_lbl_g tl `pCat` then_g)
                  `pCat` (mk_lbl_g el `pCat` else_g)
  where
    mk_lbl_g :: BlockId -> Graph n C O
    mk_lbl_g lbl = gUnitCO (mk_lbl lbl)
    mk_branch_g :: BlockId -> Graph n O C
    mk_branch_g lbl = gUnitOC (mk_branch lbl)

gUnitCO :: n C O -> Graph n C O
gUnitCO n = GMany (IsNotOpen) noBlocks (IsOpen (BUnit n))

gUnitOC :: n O C -> Graph n O C
gUnitOC n = GMany (IsOpen (BUnit n)) noBlocks IsNotOpen
-}



bFilter :: forall n. (n O O -> Bool) -> Block n C C -> Block n C C
bFilter keep (BUnit n)  = BUnit n
bFilter keep (BCat h t) = bFilterH h (bFilterT t)
  where
    bFilterH :: Block n C O -> Block n O C -> Block n C C
    bFilterH (BUnit n)    rest = BUnit n `BCat` rest
    bFilterH (h `BCat` m) rest = bFilterH h (bFilterM m rest)

    bFilterT :: Block n O C -> Block n O C
    bFilterT (BUnit n)    = BUnit n
    bFilterT (m `BCat` t) = bFilterM m (bFilterT t)

    bFilterM :: Block n O O -> Block n O C -> Block n O C
    bFilterM (BUnit n) rest | keep n    = BUnit n `BCat` rest
                            | otherwise = rest 
    bFilterM (b1 `BCat` b2) rest = bFilterM b1 (bFilterM b2 rest)


pCat :: Edges n => Graph n e a -> Graph n a x -> Graph n e x
pCat GNil g2 = g2
pCat g1 GNil = g1

pCat (GUnit b1) (GUnit b2)             
  = GUnit (b1 `BCat` b2)

pCat (GUnit b) (GMany (IsOpen e) bs x) 
  = GMany (IsOpen (b `BCat` e)) bs x

pCat (GMany e bs (IsOpen x)) (GUnit b2) 
   = GMany e bs (IsOpen (x `BCat` b2))

pCat (GMany e1 bs1 (IsOpen x1)) (GMany (IsOpen e2) bs2 x2)
   = GMany e1 (add (x1 `BCat` e2) bs1 `unionBlocks` bs2) x2
  where add b = addBlock id b
          where IsClosed id :: IfClosed C BlockId = closedId b

pCat (GMany e1 bs1 IsNotOpen) (GMany IsNotOpen bs2 x2)
   = GMany e1 (bs1 `unionBlocks` bs2) x2
