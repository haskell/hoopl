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
  Graph it does make sense to put that block in the BlockGraph that is
  the main payload of the graph

* That militates in favour of a Maybe-kind-of-thing on entry to a
  Graph, just as Norman wanted.  It's called Head, dual to Tail.

* However I am Very Very Keen to maintain the similar properties of
  nodes, blocks, graphs; and in particular the single point of entry.
  (For a multi-entry procedure, the procedure can be represented by a
  BlockGraph plus a bunch of BlockIds, rather than a Graph.)  So I
  made the Head contain the BlockId of the entry point.

* The BlockGraph in a Graph is a finite map, as you wanted.  Notice
  that this embodies an invariant: a BlockId must map to a block whose
  entry point is that BlockId.

* I've added a layer, using arfBlocks/arbBlocks.  Admittedly the
  type doesn't fit the same pattern, but it's useful structuring

* You should think of a BlockGraph as a user-visible type; perhaps
  this is the kind of graph that might form the body of a procedure.
  Moreover, perhaps rewriteAndAnlyseForward should take a BlockGraph
  rather than a Graph, and call arbBlocks.

* With that in mind I was happy to introduce the analogous invariant
  for the exit block in Tail; it is very very convenient to have that
  BlockId (cached though it may be) to hand.
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

type BlockGraph n = BlockMap (Block n C C)
  -- Invariant: BlockId bid maps to a block whose entryBlockId is bid

data Graph n e x where
  GNil  :: Graph n O O
  GUnit :: Block n O O -> Graph n O O
  GMany :: Head e (Block n O C) -> BlockGraph n
        -> Tail x (Block n C O) -> Graph n e x
  -- If Head is NoHead, then BlockGraph is non-empty

data Head e thing where
  NoHead :: BlockId -> Head C thing
  Head   :: thing -> Head O thing

data Tail x thing where
  NoTail :: Tail C thing
  Tail   :: BlockId -> thing -> Tail O thing
  -- Invariant: the BlockId is the entryBlockId of the block

-- Singletons
--   OO   GUnit
--   CO   GMany (NoHead l) [] (Tail l b)
--   OC   GMany (Head b)   []  NoTail
--   CC   GMany (NoHead l) [b] NoTail

gCat :: Graph n e a -> Graph n a x -> Graph n e x
gCat GNil g2 = g2
gCat g1 GNil = g1

gCat (GUnit b1) (GUnit b2)             
  = GUnit (b1 `BCat` b2)

gCat (GUnit b) (GMany (Head e) bs x) 
  = GMany (Head (b `BCat` e)) bs x

gCat (GMany e bs (Tail bid x)) (GUnit b2) 
   = GMany e bs (Tail bid (x `BCat` b2))

gCat (GMany e1 bs1 (Tail bid x1)) (GMany (Head e2) bs2 x2)
   = GMany e1 (addBlock bid (x1 `BCat` e2) bs1 `unionBlocks` bs2) x2

gCat (GMany e1 bs1 NoTail) (GMany (NoHead _) bs2 x2)
   = GMany e1 (bs1 `unionBlocks` bs2) x2

class Edges thing where
  entryBlockId :: thing C x -> BlockId
  successors :: thing e C -> [BlockId]

instance Edges n => Edges (Block n) where
  entryBlockId (BUnit n) = entryBlockId n
  entryBlockId (b `BCat` _) = entryBlockId b
  successors (BUnit n)   = successors n
  successors (BCat _ b)  = successors b

instance Edges n => Edges (Graph n) where
  entryBlockId (GMany (NoHead bid) _ _) = bid
  successors (GMany h bg NoTail) 
     = blockSetElems (all_succs `minusBlockSet` all_blk_ids)
     where 
       (bids, blks) = unzip (blocksToList bg)
       bg_succs = mkBlockSet [bid | b <- blks, bid <- successors b]
       all_succs :: BlockSet
       all_succs = case h of
                     NoHead _ -> bg_succs
                     Head b   -> bg_succs `unionBlockSet` mkBlockSet (successors b)
       all_blk_ids = mkBlockSet bids

forwardBlockList, backwardBlockList :: BlockGraph n -> [(BlockId,Block n C C)]
-- This produces a list of blocks in order suitable for forward analysis.
-- ToDo: Do a topological sort to improve convergence rate of fixpoint
--       This will require a (HavingSuccessors l) class constraint
forwardBlockList blks = blocksToList blks
backwardBlockList blks = blocksToList blks

-----------------------------------------------------------------------------
--	RG: an internal data type for graphs under construction
--          TOTALLY internal to Hoopl
-----------------------------------------------------------------------------

-- "RG" stands for "result graph", and will ultimately embody
-- both the result graph and its internal facts

data RG n e x where	-- Will have facts too in due course
  RGNil   :: RG n O O
  RGBlock :: Block n e x -> RG n e x
  RGMany  :: Head e (RG n O C) -> BlockGraphWithFacts n
          -> Tail x (RG n C O) -> RG n e x
  RGCat   :: RG n e O -> RG n O x -> RG n e x

type BlockGraphWithFacts n = BlockGraph n

-- normalise converts a closed/closed result graph into a BlockGraph
-- It uses three auxiliary functions, 
-- specialised for various argument shapes
normalise :: BlockId -> RG n C C -> BlockGraphWithFacts n
normalise _ (RGMany _ bg _) = bg
normalise l (RGBlock b)     = unitBlock l b
normalise l (RGCat rg1 rg2) = normalise2 l rg1 rg2

normalise2 :: BlockId -> RG n C O -> RG n O C -> BlockGraphWithFacts n
-- normalise (rg1 `RGCat` rg2)
normalise2 l (RGCat rg1 rg2) rg3 = normalise2 l rg1 (rg2 `RGCat` rg3)
normalise2 _ (RGMany (NoHead _) bg1 (Tail lt rgt)) rg2
  = bg1 `unionBlocks` normalise2 lt rgt rg2
normalise2 l (RGBlock b)  rg = normaliseB l b rg

normaliseB :: BlockId -> Block n C O -> RG n O C -> BlockGraphWithFacts n
-- normalise (Block b `RGCat` rg2)
normaliseB l b (rg1 `RGCat` rg2) = normaliseB2 l b rg1 rg2
normaliseB lh bh (RGBlock bt)    = unitBlock lh (bh `BCat` bt)
normaliseB l b1 (RGMany (Head rg2) bg NoTail) 
  = normaliseB l b1 rg2 `unionBlocks` bg

normaliseB2 :: BlockId -> Block n C O -> RG n O O -> RG n O C -> BlockGraphWithFacts n
-- normalise (Block b `RGCat` rg2 `RGCat` rg3)
normaliseB2 l b RGNil rg3 = normaliseB l b rg3
normaliseB2 l b (RGCat rg1 rg2) rg3
  = normaliseB2 l b rg1 (rg2 `RGCat` rg3)
normaliseB2 lh bh (RGBlock bt) rg
  = normaliseB lh (bh `BCat` bt) rg
normaliseB2 lh bh (RGMany (Head rg1) bg (Tail lt rg2)) rg3
  = normaliseB lh bh rg1 `unionBlocks`
    bg                   `unionBlocks`
    normalise2 lt rg2 rg3

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

type ForwardTransfers n f 
  = forall e x. f -> n e x -> TailFactF x f 

type ForwardRewrites n f 
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

         , tfb_blks  :: BlockGraph n  -- Transformed blocks
    }

updateFact :: DataflowLattice f -> (BlockId, f)
           -> TxFactBase n f -> TxFactBase n f
-- Update a TxFactBase, setting the change flag iff
--   a) the new fact adds information...
--   b) for a block in the BlockSet in the TxFactBase
updateFact lat (bid, new_fact) tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = bids})
  | NoChange <- cha2        = tx_fb
  | bid `elemBlockSet` bids = tx_fb { tfb_fbase = new_fbase, tfb_cha = SomeChange }
  | otherwise               = tx_fb { tfb_fbase = new_fbase }
  where
    old_fact = lookupFact lat fbase bid
    (cha2, res_fact) = fact_extend lat old_fact new_fact
    new_fbase = extendFactBase fbase bid res_fact

updateFacts :: DataflowLattice f 
	    -> BlockId
            -> (FactBase f -> FuelMonad ([(BlockId,f)], RG n C C))
            -> TxFactBase n f -> FuelMonad (TxFactBase n f)
-- Works regardless of direction
updateFacts lat lbl fb_trans
    tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = lbls, tfb_blks = blks })
  = do { (out_facts, graph) <- fb_trans fbase
       ; let tx_fb' = tx_fb { tfb_bids = extendBlockSet lbls lbl
                            , tfb_blks = normalise lbl graph `unionBlocks` blks }
       ; return (foldr (updateFact lat) tx_fb' out_facts) }

fixpoint :: forall n f. 
                 (TxFactBase n f -> FuelMonad (TxFactBase n f))
              -> (FactBase f     -> FuelMonad (TxFactBase n f))
fixpoint tx_fb_trans init_fbase
  = do { fuel <- getFuel  
       ; loop fuel init_fbase }
  where
    loop :: Fuel -> FactBase f -> FuelMonad (TxFactBase n f)
    loop fuel fbase 
      = do { tx_fb <- tx_fb_trans (TxFB { tfb_fbase = fbase
                                        , tfb_cha = NoChange
                                        , tfb_blks = noBlocks
                                        , tfb_bids = emptyBlockSet })
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

type ARF thing n f = forall e x. f -> thing e x -> FuelMonad (TailFactF x f, RG n e x)

type ARF_Node  n f = ARF n         n f
type ARF_Block n f = ARF (Block n) n f
type ARF_Graph n f = ARF (Graph n) n f
-----------------------------------------------------------------------------

arfNodeNoRW :: forall n f. ForwardTransfers n f -> ARF_Node n f
 -- Lifts ForwardTransfers to ARF_Node; simple transfer only
arfNodeNoRW transfer_fn f node
  = return (transfer_fn f node, RGBlock (BUnit node))

arfNode :: forall n f.
       	  DataflowLattice f
        -> ForwardTransfers n f
        -> ForwardRewrites n f
        -> ARF_Node n f
        -> ARF_Node n f
-- Lifts (ForwardTransfers,ForwardRewrites) to ARF_Node; 
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
	                                ; return (f2, g1 `RGCat` g2) }

arfBlocks :: forall n f. DataflowLattice f 
          -> ARF_Node n f -> FactBase f -> BlockGraph n 
          -> FuelMonad (FactBase f, BlockGraphWithFacts n)
		-- Outgoing factbase is restricted to BlockIds *not* in
		-- in the BlockGraph; the facts for BlockIds
		-- *in* the BlockGraph are in the BlockGraphWithFacts
arfBlocks lattice arf_node init_fbase blocks
  = do { tx_fb <- fixpoint (ft_blocks_once (forwardBlockList blocks)) init_fbase
       ; return (tfb_fbase tx_fb `deleteFromFactBase` blocks, tfb_blks tx_fb) }
	     -- The successors of the Graph are the the BlockIds for which
	     -- we have facts, that are *not* in the blocks of the graph
  where
    ft_block_once :: (BlockId, Block n C C) -> TxFactBase n f
                  -> FuelMonad (TxFactBase n f)
    ft_block_once (bid, b) = updateFacts lattice bid $ \fbase ->
                             arfBlock arf_node (lookupFact lattice fbase bid) b

    ft_blocks_once :: [(BlockId, Block n C C)] 
                   -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    ft_blocks_once []     tx_fb = return tx_fb
    ft_blocks_once (b:bs) tx_fb = do { tx_fb1 <- ft_block_once b tx_fb
                                     ; ft_blocks_once bs tx_fb1 }

arfGraph :: forall n f. DataflowLattice f -> ARF_Node n f -> ARF_Graph n f
-- Lift from blocks to graphs
arfGraph _       _         f GNil       = return (f, RGNil)
arfGraph _       arf_node f (GUnit blk) = arfBlock arf_node f blk
arfGraph lattice arf_node f (GMany entry blks exit)
  = do { (f1, entry') <- ft_entry f entry
       ; (f2, blks')  <- arfBlocks lattice arf_node (mkFactBase f1) blks
       ; (f3, exit')  <- ft_exit f2 exit 
       ; return (f3, RGMany entry' blks' exit') }
  where
    ft_entry :: f -> Head e (Block n O C) 
             -> FuelMonad ([(BlockId,f)], Head e (RG n O C))
    ft_entry fh (NoHead lh) = return ([(lh,fh)], NoHead lh)
    ft_entry fh (Head b) = do { (fs, rg) <- arfBlock arf_node fh b
                              ; return (fs, Head rg) }

    ft_exit :: FactBase f -> Tail x (Block n C O)
            -> FuelMonad (TailFactF x f, Tail x (RG n C O))
    ft_exit ft NoTail
      = return (factBaseList ft, NoTail)
    ft_exit ft (Tail lt blk)
      = do { (f1, rg) <- arfBlock arf_node (lookupFact lattice ft lt) blk
           ; return (f1, Tail lt rg) }

----------------------------------------------------------------
--       The pièce de resistance: cunning transfer functions
----------------------------------------------------------------

pureAnalysis :: DataflowLattice f -> ForwardTransfers n f -> ARF_Graph n f
pureAnalysis lattice f = arfGraph lattice (arfNodeNoRW f)

analyseAndRewriteFwd
   :: forall n f. 
      DataflowLattice f
   -> ForwardTransfers n f
   -> ForwardRewrites n f
   -> RewritingDepth
   -> ARF_Graph n f

data RewritingDepth = RewriteShallow | RewriteDeep
-- When a transformation proposes to rewrite a node, 
-- you can either ask the system to
--  * "shallow": accept the new graph, analyse it without further rewriting
--  * "deep": recursively analyse-and-rewrite the new graph

analyseAndRewriteFwd lattice transfers rewrites depth
  = arfGraph lattice arf_node
  where 
    arf_node, rec_node :: ARF_Node n f
    arf_node = arfNode lattice transfers rewrites rec_node

    rec_node = case depth of
                RewriteShallow -> arfNodeNoRW transfers
                RewriteDeep    -> arf_node

-----------------------------------------------------------------------------
--		Backward rewriting
-----------------------------------------------------------------------------

type BackwardTransfers n f 
  = forall e x. TailFactB x f -> n e x -> f 
type BackwardRewrites n f 
  = forall e x. TailFactB x f -> n e x -> Maybe (AGraph n e x)

type ARB thing n f = forall e x. TailFactB x f -> thing e x
                              -> FuelMonad (f, RG n e x)

type family   TailFactB x f :: *
type instance TailFactB C f = FactBase f
type instance TailFactB O f = f

type ARB_Node  n f = ARB n         n f
type ARB_Block n f = ARB (Block n) n f
type ARB_Graph n f = ARB (Graph n) n f

arbNodeNoRW :: forall n f . BackwardTransfers n f -> ARB_Node n f
-- Lifts BackwardTransfers to ARB_Node; simple transfer only
arbNodeNoRW transfer_fn f node
  = return (transfer_fn f node, RGBlock (BUnit node))

arbNode :: forall n f.
           DataflowLattice f
        -> BackwardTransfers n f
        -> BackwardRewrites n f
        -> ARB_Node n f
        -> ARB_Node n f
-- Lifts (BackwardTransfers,BackwardRewrites) to ARB_Node; 
-- this time we do rewriting as well. 
-- The ARB_Graph parameters specifies what to do with the rewritten graph
arbNode lattice transfer_fn rewrite_fn arf_node f node
  = do { mb_g <- withFuel (rewrite_fn f node)
       ; case mb_g of
           Nothing -> arbNodeNoRW transfer_fn f node
      	   Just ag -> do { g <- graphOfAGraph ag
      		         ; arbGraph lattice arf_node f g } }

arbBlock :: forall n f. ARB_Node n f -> ARB_Block n f
-- Lift from nodes to blocks
arbBlock arb_node f (BUnit node) = arb_node f node
arbBlock arb_node f (BCat b1 b2) = do { (f2,g2) <- arbBlock arb_node f  b2
                                      ; (f1,g1) <- arbBlock arb_node f2 b1
	                              ; return (f1, g1 `RGCat` g2) }


arbBlocks :: forall n f. DataflowLattice f 
          -> ARB_Node n f -> FactBase f
          -> BlockGraph n -> FuelMonad (FactBase f, BlockGraphWithFacts n)
arbBlocks lattice arb_node init_fbase blocks
  = do { tx_fb <- fixpoint (bt_blocks_once (backwardBlockList blocks)) init_fbase
       ; return (tfb_fbase tx_fb `deleteFromFactBase` blocks, tfb_blks tx_fb) }
  where
    bt_block_once :: (BlockId, Block n C C) -> TxFactBase n f
                  -> FuelMonad (TxFactBase n f)
    bt_block_once (l, b) = updateFacts lattice l $ \fbase ->
                           do { (fb, rg) <- arbBlock arb_node fbase b
                              ; return ([(l,fb)], rg) }

    bt_blocks_once :: [(BlockId, Block n C C)] 
                   -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    bt_blocks_once []     tx_fb = return tx_fb
    bt_blocks_once (b:bs) tx_fb = do { tx_fb1 <- bt_block_once b tx_fb
                                     ; bt_blocks_once bs tx_fb1 }

arbGraph :: forall n f. DataflowLattice f -> ARB_Node n f -> ARB_Graph n f
arbGraph _       _         f GNil       = return (f, RGNil)
arbGraph _       arb_node f (GUnit blk) = arbBlock arb_node f blk
arbGraph lattice arb_node f (GMany entry blks exit)
  = do { (f1, exit')  <- bt_exit f exit
       ; (f2, blks')  <- arbBlocks lattice arb_node f1 blks
       ; (f3, entry') <- bt_entry f2 entry 
       ; return (f3, RGMany entry' blks' exit') }
  where
    bt_entry :: FactBase f -> Head e (Block n O C)
    	     -> FuelMonad (f, Head e (RG n O C))
    bt_entry fbase (NoHead l) = return (lookupFact lattice fbase l, NoHead l)
    bt_entry fbase (Head blk) = do { (fh, rg) <- arbBlock arb_node fbase blk
                                   ; return (fh, Head rg) }

    bt_exit :: TailFactB x f -> Tail x (Block n C O)
            -> FuelMonad (FactBase f, Tail x (RG n C O))
    bt_exit ft (Tail lt blk) = do { (f1, rg) <- arbBlock arb_node ft blk
                                  ; return (mkFactBase [(lt,f1)], Tail lt rg) }
    bt_exit ft NoTail        = return (ft, NoTail)

analyseAndRewriteBwd
   :: forall n f. 
      DataflowLattice f
   -> BackwardTransfers n f
   -> BackwardRewrites n f
   -> RewritingDepth
   -> ARB_Graph n f

analyseAndRewriteBwd lattice transfers rewrites depth
  = arbGraph lattice arb_node
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

noBlocks :: BlockGraph n
noBlocks = M.empty

unitBlock :: BlockId -> Block n C C -> BlockGraph n
unitBlock = M.singleton

addBlock :: BlockId -> Block n C C -> BlockGraph n -> BlockGraph n
addBlock = M.insert

unionBlocks :: BlockGraph n -> BlockGraph n -> BlockGraph n
unionBlocks = M.union

blocksToList :: BlockGraph n -> [(BlockId,Block n C C)]
blocksToList = M.toList

----------------------
type FactBase a = M.IntMap a

noFacts :: FactBase f
noFacts = M.empty

mkFactBase :: [(BlockId, f)] -> FactBase f
mkFactBase prs = M.fromList prs

lookupFact :: DataflowLattice f -> FactBase f -> BlockId -> f
lookupFact lattice env blk_id 
  = case M.lookup blk_id env of
      Just f  -> f
      Nothing -> fact_bot lattice

extendFactBase :: FactBase f -> BlockId -> f -> FactBase f
extendFactBase env blk_id f = M.insert blk_id f env

unionFactBase :: FactBase f -> FactBase f -> FactBase f
unionFactBase = M.union

factBaseList :: FactBase f -> [(BlockId, f)]
factBaseList = M.toList 

deleteFromFactBase :: FactBase f -> BlockMap a -> FactBase f
deleteFromFactBase = M.difference

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
