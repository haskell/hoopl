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
  Graph, just as Norman wanted.

* However I am Very Very Keen to maintain the similar properties of
  nodes, blocks, graphs; and in particular the single point of entry.
  (For a multi-entry procedure, the procedure can be represented by a
  BlockGraph plus a bunch of BlockIds, rather than a Graph.)  So I
  made the Head contain the BlockId of the entry point.

* The BlockGraph in a Graph is a finite map, as you wanted.  Notice
  that this embodies an invariant: a BlockId must map to a block whose
  entry point is that BlockId.

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
  GMany :: Head n e -> BlockGraph n
	-> Tail n x -> Graph n e x
  -- If Head is NoHead, then BlockGraph is non-empty

data Head n e where
  NoHead :: BlockId -> Head n C
  Head   :: Block n O C -> Head n O

data Tail n x where
  NoTail :: Tail n C
  Tail   :: BlockId -> Block n C O -> Tail n O
  -- Invariant: the BlockId is the entryBlockId of the block

-- Singletons
--   OO   GUnit
--   CO   GMany (NoHead l) [] (Tail l b)
--   OC   GMany (Head b)   []  NoTail
--   CC   GMany (NoHead l) [b] NoTail

gUnitOO :: Block n O O -> Graph n O O
gUnitOO b = GUnit b

gUnitOC :: Block n O C -> Graph n O C
gUnitOC b = GMany (Head b) noBlocks NoTail

gUnitCO :: Edges n => Block n C O -> Graph n C O
gUnitCO b = GMany (NoHead l) noBlocks (Tail l b)
          where
            l = entryBlockId b

gUnitCC :: Edges n => Block n C C -> Graph n C C
gUnitCC b = GMany (NoHead l) (addBlock l b noBlocks) NoTail
          where
            l = entryBlockId b

flattenG :: Graph n C C -> BlockGraph n
flattenG (GMany _ bs _ ) = bs

ecGraph :: Graph n e C -> (Head n e, BlockGraph n)
ecGraph (GMany e bs _) = (e, bs)

cxGraph :: Graph n C O -> (BlockGraph n, Tail n O)
cxGraph (GMany _ bs tail) = (bs, tail)

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
--	PG: an internal data type for graphs under construction
--          TOTALLY internal to Hoopl
-----------------------------------------------------------------------------

data OCFlag oc where
  IsOpen   :: OCFlag O
  IsClosed :: OCFlag C

class IsOC oc where
  ocFlag :: OCFlag oc

instance IsOC O where
  ocFlag = IsOpen
instance IsOC C where
  ocFlag = IsClosed

type BlockGraphWithFacts n f = (BlockGraph n, FactBase f)	-- Domains are identical

data PG n e x where	-- Will have facts too in due course
  PGNil   :: PG n O O
  PGBlock :: Block n e x -> PG n e x
  PGMany  :: Head n e -> BlockGraph n
	  -> Tail n x -> PG n e x
  PGCat   :: PG n e O -> PG n O x -> PG n e x

normalise :: forall n e x. (IsOC e, IsOC x, Edges n)
          => PG n e x -> Graph n e x
-- We confidently expect to specialise this four ways
normalise PGNil             = GNil
normalise (PGMany hd bg tl) = GMany hd bg tl
normalise (PGCat pg1 pg2)   = normalise pg1 `gCat` normalise pg2
normalise (PGBlock b)
  = case (ocFlag :: OCFlag e) of
      IsOpen -> case (ocFlag :: OCFlag x) of
                    IsOpen   -> gUnitOO b
		    IsClosed -> gUnitOC b
      IsClosed -> case (ocFlag :: OCFlag x) of
                    IsOpen   -> gUnitCO b
                    IsClosed -> gUnitCC b
  where
    e_flag = ocFlag :: OCFlag e
    x_flag = ocFlag :: OCFlag x

  
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

factBaseInFacts :: DataflowLattice f -> TxFactBase n f -> BlockId -> f
factBaseInFacts lattice (TxFB { tfb_fbase = fbase }) bid
  = lookupFact lattice fbase bid

factBaseOutFacts :: TxFactBase n f -> [(BlockId,f)]
factBaseOutFacts (TxFB { tfb_fbase = fbase, tfb_bids = bids }) 
  = [ (bid, f) | (bid, f) <- factBaseList fbase
               , not (bid `elemBlockSet` bids) ]
  -- The successors of the Graph are the the BlockIds for which
  -- we hvae facts, that are *not* in the blocks of the graph

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

updateFacts :: Edges n
            => DataflowLattice f 
	    -> BlockId
            -> (FactBase f -> FuelMonad ([(BlockId,f)], PG n C C))
            -> TxFactBase n f -> FuelMonad (TxFactBase n f)
-- Works regardless of direction
updateFacts lat bid fb_trans
    tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = bids, tfb_blks = blks })
  = do { (out_facts, graph) <- fb_trans fbase
       ; let tx_fb' = tx_fb { tfb_bids = extendBlockSet bids bid
                            , tfb_blks = flattenG (normalise graph) `unionBlocks` blks }
       ; return (foldr (updateFact lat) tx_fb' out_facts) }

-----------------------------------------------------------------------------
--		The Trans arrow
-----------------------------------------------------------------------------

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

type ARF thing n f = forall e x. f -> thing e x
                              -> FuelMonad (TailFactF x f, PG n e x)

type ARF_Node  n f = ARF n         n f
type ARF_Block n f = ARF (Block n) n f
type ARF_Graph n f = ARF (Graph n) n f
-----------------------------------------------------------------------------

arfNodeTransfer :: forall n f. ForwardTransfers n f -> ARF_Node n f
 -- Lifts ForwardTransfers to ARF_Node; simple transfer only
arfNodeTransfer transfer_fn f node
  = return (transfer_fn f node, PGBlock (BUnit node))
arfNodeRewrite :: forall n f.
                  ForwardTransfers n f
               -> ForwardRewrites n f
               -> ARF_Graph n f
               -> ARF_Node n f
-- Lifts (ForwardTransfers,ForwardRewrites) to ARF_Node; 
-- this time we do rewriting as well. 
-- The ARF_Graph parameters specifies what to do with the rewritten graph
arfNodeRewrite transfer_fn rewrite_fn graph_trans f node
  = do { mb_g <- withFuel (rewrite_fn f node)
       ; case mb_g of
           Nothing -> arfNodeTransfer transfer_fn f node
      	   Just ag -> do { g <- graphOfAGraph ag
      		         ; graph_trans f g } }

arfBlock :: forall n f. ARF_Node n f -> ARF_Block n f
-- Lift from nodes to blocks
arfBlock arf_node f (BUnit node)   = arf_node f node
arfBlock arf_node f (BCat hd mids) = do { (f1,g1) <- arfBlock arf_node f  hd
                                        ; (f2,g2) <- arfBlock arf_node f1 mids
	                                ; return (f2, g1 `PGCat` g2) }

arfGraph :: forall n f. Edges n
                     => DataflowLattice f -> ARF_Block n f -> ARF_Graph n f
-- Lift from blocks to graphs
arfGraph lattice arf_block f GNil        = return (f, PGNil)
arfGraph lattice arf_block f (GUnit blk) = arf_block f blk
arfGraph lattice arf_block f (GMany entry blocks exit)
  = do { (f1, entry', bs1) <- ft_entry f entry
       ; tx_fb             <- ft_blocks blocks (mkFactBase f1)
       ; (f3, bs2, exit')  <- ft_exit tx_fb exit 
       ; let final_bs = bs1 `unionBlocks` tfb_blks tx_fb `unionBlocks` bs2
       ; return (f3, PGMany entry' final_bs exit') }
  where
    ft_entry :: f -> Head n e -> FuelMonad ([(BlockId,f)], Head n e, BlockGraph n)
    ft_entry f (NoHead l) = return ([(l,f)], NoHead l, noBlocks)
    ft_entry f (Head b) = do { (fs, pg) <- arf_block f b
			     ; let GMany h bs _ = normalise pg
                             ; return (fs, h, bs) }

	-- It's a bit disgusting that the TxFactBase has to be
        -- preserved as far as the Tail block, becaues the TxFactBase
        -- is really concerned with the fixpoint calculation
        -- But I can't see any other tidy way to compute the 
        -- LastOutFacts in the NoTail case
    ft_exit :: TxFactBase n f -> Tail n x
            -> FuelMonad (TailFactF x f, BlockGraph n, Tail n x)
    ft_exit f NoTail
      = return (factBaseOutFacts f, noBlocks, NoTail)
    ft_exit f (Tail bid blk)
      = do { (f1, pg) <- arf_block (factBaseInFacts lattice f bid) blk
	   ; let GMany _ bs exit = normalise pg
           ; return (f1, bs, exit) }

    ft_block_once :: (BlockId, Block n C C) -> TxFactBase n f
                  -> FuelMonad (TxFactBase n f)
    ft_block_once (bid, b) = updateFacts lattice bid $ \fbase ->
                             arf_block (lookupFact lattice fbase bid) b

    ft_blocks_once :: [(BlockId, Block n C C)] 
                   -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    ft_blocks_once []     tx_fb = return tx_fb
    ft_blocks_once (b:bs) tx_fb = do { tx_fb1 <- ft_block_once b tx_fb
                                     ; ft_blocks_once bs tx_fb1 }

    ft_blocks :: BlockGraph n -> FactBase f -> FuelMonad (TxFactBase n f)
    ft_blocks blocks = fixpoint (ft_blocks_once (forwardBlockList blocks))

----------------------------------------------------------------
--       The pièce de resistance: cunning transfer functions
----------------------------------------------------------------

pureAnalysis :: Edges n => DataflowLattice f -> ForwardTransfers n f -> ARF_Graph n f
pureAnalysis lattice f = arfGraph lattice (arfBlock (arfNodeTransfer f))

analyseAndRewriteFwd
   :: forall n f. Edges n
   => DataflowLattice f
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
  = anal_rewrite
  where 
    anal_rewrite, anal_only, arf_rec :: ARF_Graph n f

    anal_rewrite = arfGraph lattice $ arfBlock $ 
                   arfNodeRewrite transfers rewrites arf_rec

    anal_only    = arfGraph lattice $ arfBlock $ 
                   arfNodeTransfer transfers

    arf_rec = case depth of
                RewriteShallow -> anal_only
                RewriteDeep    -> anal_rewrite
{-
-----------------------------------------------------------------------------
--		Backward rewriting
-----------------------------------------------------------------------------

type BackwardTransfers n f 
  = forall e x. TailFactB x f -> n e x -> f 
type BackwardRewrites n f 
  = forall e x. TailFactB x f -> n e x -> Maybe (AGraph n e x)

type ARB thing n f = forall e x. LiftNode x 
                              => TailFactB x f -> thing e x
                              -> FuelMonad (f, Graph n e x)

type family   TailFactB x f :: *
type instance TailFactB C f = FactBase f
type instance TailFactB O f = f

type ARB_Node  n f = ARB n         n f
type ARB_Block n f = ARB (Block n) n f
type ARB_Graph n f = ARB (Graph n) n f

arbNodeTransfer :: forall n f . BackwardTransfers n f -> ARB_Node n f
-- Lifts BackwardTransfers to ARB_Node; simple transfer only
arbNodeTransfer transfer_fn f node
  = return (transfer_fn f node, liftNode node)

arbNodeRewrite :: forall n f.
                  BackwardTransfers n f
               -> BackwardRewrites n f
               -> ARB_Graph n f
               -> ARB_Node n f
-- Lifts (BackwardTransfers,BackwardRewrites) to ARB_Node; 
-- this time we do rewriting as well. 
-- The ARB_Graph parameters specifies what to do with the rewritten graph
arbNodeRewrite transfer_fn rewrite_fn graph_trans f node
  = do { mb_g <- withFuel (rewrite_fn f node)
       ; case mb_g of
           Nothing -> arbNodeTransfer transfer_fn f node
      	   Just ag -> do { g <- graphOfAGraph ag
      		         ; graph_trans f g } }

arbBlock :: forall n f. ARB_Node n f -> ARB_Block n f
-- Lift from nodes to blocks
arbBlock arb_node f (BUnit node) = arb_node f node
arbBlock arb_node f (BCat b1 b2) = do { (f2,g2) <- arbBlock arb_node f  b2
                                      ; (f1,g1) <- arbBlock arb_node f2 b1
	                              ; return (f1, g1 `gCat` g2) }

arbGraph :: forall n f. DataflowLattice f -> ARB_Block n f -> ARB_Graph n f
arbGraph lattice arb_block f GNil        = return (f, GNil)
arbGraph lattice arb_block f (GUnit blk) = arb_block f blk
arbGraph lattice arb_block f (GMany entry blocks exit)
  = do { (f1, bs2, exit')  <- bt_exit f exit
       ; tx_fb             <- bt_blocks blocks f1
       ; (f3, entry_g)     <- arb_block (tfb_fbase tx_fb) entry 
       ; let (entry', bs1) = ecGraph entry_g
             final_bs = bs1 `unionBlocks` tfb_blks tx_fb `unionBlocks` bs2
       ; return (f3, GMany entry' final_bs exit') }
  where
	-- It's a bit disgusting that the TxFactBase has to be
        -- preserved as far as the Tail block, becaues the TxFactBase
        -- is really concerned with the fixpoint calculation
        -- But I can't see any other tidy way to compute the 
        -- LastOutFacts in the NoTail case
    bt_exit :: TailFactB x f -> Tail n x
            -> FuelMonad (FactBase f, BlockGraph n, Tail n x)
    bt_exit f (Tail bid blk)
      = do { (f1, g) <- arb_block f blk
	   ; let (bs, exit) = cxGraph bid g
           ; return (mkFactBase [(bid,f1)], bs, exit) }
    bt_exit f NoTail
      = return (f, noBlocks, NoTail)

    bt_block_once :: (BlockId, Block n C C) -> TxFactBase n f
                  -> FuelMonad (TxFactBase n f)
    bt_block_once (bid, b) = updateFacts lattice bid $ \fbase ->
                             do { (f, g) <- arb_block fbase b
                                ; return ([(bid,f)], g) }

    bt_blocks_once :: [(BlockId,Block n C C)] 
                   -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    bt_blocks_once []     tx_fb = return tx_fb
    bt_blocks_once (b:bs) tx_fb = do { tx_fb' <- bt_block_once b tx_fb
                                     ; bt_blocks_once bs tx_fb' }

    bt_blocks :: BlockGraph n -> FactBase f -> FuelMonad (TxFactBase n f)
    bt_blocks blocks = fixpoint (bt_blocks_once (backwardBlockList blocks))

analyseAndRewriteBwd
   :: forall n f. 
      DataflowLattice f
   -> BackwardTransfers n f
   -> BackwardRewrites n f
   -> RewritingDepth
   -> ARB_Graph n f

analyseAndRewriteBwd lattice transfers rewrites depth
  = anal_rewrite
  where 
    anal_rewrite, anal_only, arb_rec :: ARB_Graph n f

    anal_rewrite = arbGraph lattice $ arbBlock $ 
                   arbNodeRewrite transfers rewrites arb_rec

    anal_only    = arbGraph lattice $ arbBlock $ 
                   arbNodeTransfer transfers

    arb_rec = case depth of
                RewriteShallow -> anal_only
                RewriteDeep    -> anal_rewrite

-}

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
factBaseList env = M.toList env


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
