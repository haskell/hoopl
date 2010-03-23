{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies #-}

module Hoopl4 where

import qualified Data.IntMap as M
import qualified Data.IntSet as S

-----------------------------------------------------------------------------
--		Graphs
-----------------------------------------------------------------------------

data ZOpen
data ZClosed

type O = ZOpen
type C = ZClosed

-- Blocks are always non-empty
data Block n e x where
  BUnit :: n e x -> Block n e x
  BCat  :: Block n e O -> Block n O x -> Block n e x

type LBlocks n = [LBlock n C]
data LBlock n x = LB BlockId (Block n C x)

data Graph n e x where
  GNil  :: Graph n O O
  GUnit :: Block n e O -> Graph n e O
  GMany   { g_entry  :: Block n e C
          , g_blocks :: LBlocks n
	  , g_exit   :: Tail n x } :: Graph n e x

   -- If a graph has a Tail, then that tail is the only  
   -- exit from the graph, even if the Tail is closed
   -- See the definition of successors!

data Tail n x where
  NoTail :: Tail n C
  Tail   :: BlockId -> Block n C O -> Tail n O

class LiftNode x where
   liftNode :: n e x -> Graph n e x
instance LiftNode ZClosed where
   liftNode n = GMany (BUnit n) [] NoTail
instance LiftNode ZOpen where
   liftNode n = GUnit (BUnit n)

class Edges thing where
  successors :: thing e C -> [BlockId]

instance Edges n => Edges (Block n) where
  successors (BUnit n)  = successors n
  successors (BCat _ b) = successors b

instance Edges n => Edges (Graph n) where
  successors (GMany b bs NoTail) 
     = blockSetElems (all_succs `minusBlockSet` all_blk_ids)
     where 
       all_succs   = mkBlockSet (successors b ++ [bid | LB _ b <- bs, bid <- successors b])
       all_blk_ids = mkBlockSet [bid | LB bid _ <- bs]


ecGraph :: Graph n e C -> (Block n e C, LBlocks n)
ecGraph (GMany b bs NoTail) = (b, bs)

cxGraph :: BlockId -> Graph n C O -> (LBlocks n, Tail n O)
cxGraph bid (GUnit b)          = ([], Tail bid b)
cxGraph bid (GMany be bs tail) = (LB bid be:bs, tail)

flattenG :: BlockId -> Graph n C C -> LBlocks n
flattenG bid (GMany e bs NoTail) = LB bid e : bs

gCat :: Graph n e O -> Graph n O x -> Graph n e x
























gCat GNil g2 = g2
gCat g1 GNil = g1

gCat (GUnit b1) (GUnit b2)             
  = GUnit (b1 `BCat` b2)

gCat (GUnit b) (GMany e bs x) 
  = GMany (b `BCat` e) bs x

gCat (GMany e bs (Tail bid x)) (GUnit b2) 
   = GMany e bs (Tail bid (x `BCat` b2))

gCat (GMany e1 bs1 (Tail bid x1)) (GMany e2 bs2 x2)
   = GMany e1 (LB bid (x1 `BCat` e2) : bs1 ++ bs2) x2

forwardBlockList, backwardBlockList :: LBlocks n -> LBlocks n
-- This produces a list of blocks in order suitable for forward analysis.
-- ToDo: Do a topological sort to improve convergence rate of fixpoint
--       This will require a (HavingSuccessors l) class constraint
forwardBlockList blks = blks
backwardBlockList blks = blks

-----------------------------------------------------------------------------
--		DataflowLattice
-----------------------------------------------------------------------------

data DataflowLattice a = DataflowLattice  { 
  fact_name       :: String,                 -- Documentation
  fact_bot        :: a,                      -- Lattice bottom element
  fact_add_to     :: a -> a -> TxRes a,      -- Lattice join plus change flag
  fact_do_logging :: Bool                    -- log changes
}

data ChangeFlag = NoChange | SomeChange
data TxRes a = TxRes ChangeFlag a

-----------------------------------------------------------------------------
--		The main Hoopl API
-----------------------------------------------------------------------------

type ForwardTransfers n f 
  = forall e x. n e x -> f -> TailFactF x f 

type ForwardRewrites n f 
  = forall e x. n e x -> f -> Maybe (AGraph n e x)

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
data TxFactBase n fact 
  = TxFB { tfb_fbase :: FactBase fact

         , tfb_cha   :: ChangeFlag
         , tfb_bids  :: BlockSet   -- Update change flag iff these blocks change
                                   -- These are BlockIds of the *original* 
                                   -- (not transformed) blocks

         , tfb_blks  :: LBlocks n   -- Transformed blocks
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
    TxRes cha2 res_fact = fact_add_to lat old_fact new_fact
    new_fbase = extendFactBase fbase bid res_fact

updateFacts :: Edges n
            => DataflowLattice f 
	    -> BlockId
            -> (FactBase f -> FuelMonad (Graph n C C, [(BlockId,f)]))
            -> TxFactBase n f -> FuelMonad (TxFactBase n f)
-- Works regardless of direction
updateFacts lat bid fb_trans
    tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = bids, tfb_blks = blks })
  = do { (graph, out_facts) <- fb_trans fbase
       ; let tx_fb' = tx_fb { tfb_bids = extendBlockSet bids bid
                            , tfb_blks = flattenG bid graph ++ blks }
       ; return (foldr (updateFact lat) tx_fb' out_facts) }

-----------------------------------------------------------------------------
--		The Trans arrow
-----------------------------------------------------------------------------

type Trans a b = a -> FuelMonad b 
 -- Transform a into b, with facts of type f
 -- Deals with optimsation fuel and unique supply too
  
(>>>) :: Trans a b -> Trans b c -> Trans a c
-- Compose two dataflow transfers in sequence
(dft1 >>> dft2) f = do { f1 <- dft1 f; f2 <- dft2 f1; return f2 }

liftTrans :: (a->b) -> Trans a b
liftTrans f x = return (f x)

idTrans :: Trans a a
idTrans x = return x

fixpointTrans :: forall n f. 
                 (TxFactBase n f -> FuelMonad (TxFactBase n f))
              -> (FactBase f     -> FuelMonad (TxFactBase n f))
fixpointTrans tx_fb_trans init_fbase
  = do { fuel <- getFuel  
       ; loop fuel init_fbase }
  where
    loop :: Fuel -> FactBase f -> FuelMonad (TxFactBase n f)
    loop fuel fbase 
      = do { tx_fb <- tx_fb_trans (TxFB { tfb_fbase = fbase
                                        , tfb_cha = NoChange
                                        , tfb_blks = []
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

type ARF thing n f = forall e x. LiftNode x 
                              => thing e x -> f 
                              -> FuelMonad (Graph n e x, TailFactF x f)

type ARF_Node  n f = ARF n         n f
type ARF_Block n f = ARF (Block n) n f
type ARF_Graph n f = ARF (Graph n) n f
-----------------------------------------------------------------------------

arfNodeTransfer :: forall n f . ForwardTransfers n f -> ARF_Node n f
-- Lifts ForwardTransfers to ARF_Node; simple transfer only
arfNodeTransfer transfer_fn node f
  = return (liftNode node, transfer_fn node f)

arfNodeRewrite :: forall n f.
                  ForwardTransfers n f
               -> ForwardRewrites n f
               -> ARF_Graph n f
               -> ARF_Node n f
-- Lifts (ForwardTransfers,ForwardRewrites) to ARF_Node; 
-- this time we do rewriting as well. 
-- The ARF_Graph parameters specifies what to do with the rewritten graph
arfNodeRewrite transfer_fn rewrite_fn graph_trans node f
  = do { mb_g <- withFuel (rewrite_fn node f)
       ; case mb_g of
           Nothing -> arfNodeTransfer transfer_fn node f
      	   Just g  -> do { g' <- graphOfAGraph g
      		         ; graph_trans g' f } }

arfBlock :: forall n f. ARF_Node n f -> ARF_Block n f
-- Lift from nodes to blocks
arfBlock arf_node (BUnit node)   f = arf_node node f
arfBlock arf_node (BCat hd mids) f = do { (g1,f1) <- arfBlock arf_node hd f
                                        ; (g2,f2) <- arfBlock arf_node mids f1
	                                ; return (g1 `gCat` g2, f2) }

arfGraph :: forall n f. Edges n => DataflowLattice f -> ARF_Block n f -> ARF_Graph n f
-- Lift from blocks to graphs
arfGraph lattice arf_block GNil        f = return (GNil, f)
arfGraph lattice arf_block (GUnit blk) f = arf_block blk f
arfGraph lattice arf_block (GMany entry blocks exit) f
  = do { (entry_g, f1)     <- arf_block entry f
       ; tx_fb             <- ft_blocks blocks (mkFactBase f1)
       ; (bs2, exit', f3)  <- ft_exit exit tx_fb 
       ; let (entry', bs1) = ecGraph entry_g
       ; return (GMany entry' (bs1 ++ tfb_blks tx_fb ++ bs2) exit', f3) }
  where
	-- It's a bit disgusting that the TxFactBase has to be
        -- preserved as far as the Tail block, becaues the TxFactBase
        -- is really concerned with the fixpoint calculation
        -- But I can't see any other tidy way to compute the 
        -- LastOutFacts in the NoTail case
    ft_exit :: Tail n x  -> TxFactBase n f
            -> FuelMonad (LBlocks n, Tail n x, TailFactF x f)
    ft_exit (Tail bid blk) f 
      = do { (g, f1) <- arf_block blk (factBaseInFacts lattice f bid)
	   ; let (bs, exit) = cxGraph bid g
           ; return (bs, exit, f1) }
    ft_exit NoTail f 
      = return ([], NoTail, factBaseOutFacts f)

    ft_block_once :: LBlock n C -> TxFactBase n f
                  -> FuelMonad (TxFactBase n f)
    ft_block_once (LB bid b) = updateFacts lattice bid $ \fbase ->
                               arf_block b (lookupFact lattice fbase bid)

    ft_blocks_once :: LBlocks n -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    ft_blocks_once blks = foldr ((>>>) . ft_block_once) idTrans blks

    ft_blocks :: LBlocks n -> FactBase f -> FuelMonad (TxFactBase n f)
    ft_blocks blocks = fixpointTrans (ft_blocks_once (forwardBlockList blocks))

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

analyseAndRewriteFwd depth lattice transfers rewrites
  = arf_graph_cunning
  where 
    arf_graph_base, arf_graph_cunning, arf_graph_recurse :: ARF_Graph n f

    arf_graph_base    = arfGraph lattice $ arfBlock $ 
                        arfNodeTransfer transfers
    arf_graph_cunning = arfGraph lattice $ arfBlock $ 
                        arfNodeRewrite transfers rewrites arf_graph_recurse

    arf_graph_recurse = case depth of
                          RewriteShallow -> arf_graph_base
                          RewriteDeep    -> arf_graph_cunning

-----------------------------------------------------------------------------
--		Backward rewriting
-----------------------------------------------------------------------------

type BackwardTransfers n f 
  = forall e x. n e x -> TailFactB x f -> f 
type BackwardRewrites n f 
  = forall e x. n e x -> TailFactB x f -> Maybe (AGraph n e x)

type ARB thing n f = forall e x. LiftNode x 
                              => thing e x -> TailFactB x f 
                              -> FuelMonad (Graph n e x, f)

type family   TailFactB x f :: *
type instance TailFactB C f = FactBase f
type instance TailFactB O f = f

type ARB_Node  n f = ARB n         n f
type ARB_Block n f = ARB (Block n) n f
type ARB_Graph n f = ARB (Graph n) n f

arbNodeTransfer :: forall n f . BackwardTransfers n f -> ARB_Node n f
-- Lifts BackwardTransfers to ARB_Node; simple transfer only
arbNodeTransfer transfer_fn node f
  = return (liftNode node, transfer_fn node f)

arbNodeRewrite :: forall n f.
                  BackwardTransfers n f
               -> BackwardRewrites n f
               -> ARB_Graph n f
               -> ARB_Node n f
-- Lifts (BackwardTransfers,BackwardRewrites) to ARB_Node; 
-- this time we do rewriting as well. 
-- The ARB_Graph parameters specifies what to do with the rewritten graph
arbNodeRewrite transfer_fn rewrite_fn graph_trans node f
  = do { mb_g <- withFuel (rewrite_fn node f)
       ; case mb_g of
           Nothing -> arbNodeTransfer transfer_fn node f
      	   Just g  -> do { g' <- graphOfAGraph g
      		         ; graph_trans g' f } }

arbBlock :: forall n f. ARB_Node n f -> ARB_Block n f
-- Lift from nodes to blocks
arbBlock arb_node (BUnit node) f = arb_node node f
arbBlock arb_node (BCat b1 b2) f = do { (g2,f2) <- arbBlock arb_node b2 f
                                      ; (g1,f1) <- arbBlock arb_node b1 f2
	                              ; return (g1 `gCat` g2, f1) }

arbGraph :: forall n f. Edges n => DataflowLattice f -> ARB_Block n f -> ARB_Graph n f
arbGraph lattice arb_block GNil        f = return (GNil, f)
arbGraph lattice arb_block (GUnit blk) f = arb_block blk f
arbGraph lattice arb_block (GMany entry blocks exit) f
  = do { (bs2, exit', f1)  <- bt_exit exit f
       ; tx_fb             <- bt_blocks blocks f1
       ; (entry_g, f3)     <- arb_block entry (tfb_fbase tx_fb)
       ; let (entry', bs1) = ecGraph entry_g
       ; return (GMany entry' (bs1 ++ tfb_blks tx_fb ++ bs2) exit', f3) }
  where
	-- It's a bit disgusting that the TxFactBase has to be
        -- preserved as far as the Tail block, becaues the TxFactBase
        -- is really concerned with the fixpoint calculation
        -- But I can't see any other tidy way to compute the 
        -- LastOutFacts in the NoTail case
    bt_exit :: Tail n x -> TailFactB x f
            -> FuelMonad (LBlocks n, Tail n x, FactBase f)
    bt_exit (Tail bid blk) f 
      = do { (g, f1) <- arb_block blk f
	   ; let (bs, exit) = cxGraph bid g
           ; return (bs, exit, mkFactBase [(bid,f1)]) }
    bt_exit NoTail f 
      = return ([], NoTail, f)

    bt_block_once :: LBlock n C -> TxFactBase n f
                  -> FuelMonad (TxFactBase n f)
    bt_block_once (LB bid b) = updateFacts lattice bid $ \fbase ->
                               do { (g, f) <- arb_block b fbase
                                  ; return (g, [(bid,f)]) }

    bt_blocks_once :: LBlocks n -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    bt_blocks_once blks = foldr ((>>>) . bt_block_once) idTrans blks

    bt_blocks :: LBlocks n -> FactBase f -> FuelMonad (TxFactBase n f)
    bt_blocks blocks = fixpointTrans (bt_blocks_once (backwardBlockList blocks))

analyseAndRewriteBwd
   :: forall n f. Edges n
   => DataflowLattice f
   -> BackwardTransfers n f
   -> BackwardRewrites n f
   -> RewritingDepth
   -> ARB_Graph n f

analyseAndRewriteBwd depth lattice transfers rewrites
  = arb_graph_cunning
  where 
    arb_graph_base, arb_graph_cunning, arb_graph_recurse :: ARB_Graph n f

    arb_graph_base    = arbGraph lattice (arbBlock arb_node_base)
    arb_graph_cunning = arbGraph lattice (arbBlock arb_node_cunning)
    arb_graph_recurse = case depth of
                          RewriteShallow -> arb_graph_base
                          RewriteDeep    -> arb_graph_cunning

    arb_node_base, arb_node_cunning :: ARB_Node n f
    arb_node_base    = arbNodeTransfer transfers
    arb_node_cunning = arbNodeRewrite  transfers rewrites arb_graph_recurse


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
type FactBase a = M.IntMap a

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

mkBlockSet :: [BlockId] -> BlockSet
mkBlockSet = S.fromList
