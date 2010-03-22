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
	  , g_exit   :: Exit n x } :: Graph n e x

   -- If a graph has a Tail, then that tail is the only  
   -- exit from the graph, even if the Tail is closed
   -- See the definition of successors!

data Exit n x where
  NoTail :: Exit n C
  Tail   :: BlockId -> Block n C O -> Exit n O

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

cxGraph :: BlockId -> Graph n C O -> (LBlocks n, Exit n O)
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

forwardBlockList :: LBlocks n -> LBlocks n
-- This produces a list of blocks in order suitable for forward analysis.
-- ToDo: Do a topological sort to improve convergence rate of fixpoint
--       This will require a (HavingSuccessors l) class constraint
forwardBlockList blks = blks

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
  = forall e x. n e x -> InFact e f -> OutFact x f 

type ForwardRewrites n f 
  = forall e x. n e x -> InFact e f -> Maybe (AGraph n e x)

type InFact e f = f

type family   OutFact x f :: *
type instance OutFact C f = OutFactC f
type instance OutFact O f = f

type InFactC  fact = BlockId -> fact
type OutFactC fact = [(BlockId, fact)] 

data AGraph n e x = AGraph 	-- Stub for now


-----------------------------------------------------------------------------
--      TxFactBase: a FactBase with ChangeFlag information
-----------------------------------------------------------------------------

-- The TxFactBase is an accumulating parameter, threaded through all
-- the analysis/transformation of each block in the g_blocks of a grpah.
-- It carries a ChangeFlag with it, and a set of BlockIds
-- to monitor. Updates to other BlockIds don't affect the ChangeFlag
data TxFactBase n fact 
  = TxFB { tfb_fbase :: BlockEnv fact

         , tfb_cha   :: ChangeFlag
         , tfb_bids  :: BlockSet   -- Update change flag iff these blocks change
                                   -- These are BlockIds of the *original* 
                                   -- (not transformed) blocks

         , tfb_blks  :: LBlocks n   -- Transformed blocks
    }

factBaseInFacts :: DataflowLattice f -> TxFactBase n f -> BlockId -> f
factBaseInFacts lattice (TxFB { tfb_fbase = fbase }) bid
  = lookupBEnv lattice fbase bid

factBaseOutFacts :: TxFactBase n f -> OutFactC f
factBaseOutFacts (TxFB { tfb_fbase = fbase, tfb_bids = bids }) 
  = [ (bid, f) | (bid, f) <- blockEnvList fbase
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
    old_fact = lookupBEnv lat fbase bid
    TxRes cha2 res_fact = fact_add_to lat old_fact new_fact
    new_fbase = extendBEnv fbase bid res_fact

updateFacts :: Edges n
            => DataflowLattice f 
            -> GFT_Block n f
            -> LBlock n C
            -> Trans (TxFactBase n f) (TxFactBase n f)
updateFacts lat (GFT block_trans) (LB bid blk)
    tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = bids, tfb_blks = blks })
  = do { (graph, out_facts) <- block_trans blk (lookupBEnv lat fbase bid)
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
                 Trans (TxFactBase n f) (TxFactBase n f) 
              -> Trans (OutFactC f)     (TxFactBase n f)
fixpointTrans tx_fb_trans out_facts
  = do { fuel <- getFuel  
       ; loop fuel (mkBlockEnv out_facts) }
  where
    loop :: Fuel -> Trans (BlockEnv f) (TxFactBase n f)
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

newtype GFT thing n f = GFT (GFTR thing n f)
type GFTR thing n f = forall e x. LiftNode x 
                               => thing e x -> Trans (InFact e f) 
                                                     (Graph n e x, OutFact x f)

type GFT_Node  n f = GFT n         n f
type GFT_Block n f = GFT (Block n) n f
type GFT_Graph n f = GFT (Graph n) n f
-----------------------------------------------------------------------------

gftNodeTransfer :: forall n f . ForwardTransfers n f -> GFT_Node n f
-- Lifts ForwardTransfers to GFT_Node; simple transfer only
gftNodeTransfer base_trans = GFT node_trans
    where 
      node_trans :: GFTR n n f
      node_trans node f = return (liftNode node, base_trans node f)

gftNodeRewrite :: forall n f.
                  ForwardTransfers n f
               -> ForwardRewrites n f
               -> GFT_Graph n f
               -> GFT_Node n f
-- Lifts (ForwardTransfers,ForwardRewrites) to GFT_Node; 
-- this time we do rewriting as well. 
-- The GFT_Graph parameters specifies what to do with the rewritten graph
gftNodeRewrite transfers rewrites (GFT graph_trans) 
  = GFT node_rewrite
  where
    node_trans :: GFTR n n f
    node_trans node f = return (liftNode node, transfers node f)

    node_rewrite :: GFTR n n f
    node_rewrite node f  
       = case rewrites node f of
      	   Nothing -> node_trans node f
      	   Just g  -> do { out <- fuelExhausted
      	    		    ; if out then 
                              node_trans node f
      	    		      else do { decrementFuel
      	    		              ; g' <- graphOfAGraph g
      	    		              ; graph_trans g' f } }

gftBlock :: forall n f. GFT_Node n f -> GFT_Block n f
-- Lift from nodes to blocks
gftBlock (GFT node_trans) = GFT block_trans
  where 
    block_trans :: GFTR (Block n) n f
    block_trans (BUnit node)   f = node_trans node f
    block_trans (BCat hd mids) f = do { (g1,f1) <- block_trans hd f
                                      ; (g2,f2) <- block_trans mids f1
	                              ; return (g1 `gCat` g2, f2) }


gftGraph :: forall n f. Edges n => DataflowLattice f -> GFT_Block n f -> GFT_Graph n f
-- Lift from blocks to graphs
gftGraph lattice gft_block@(GFT block_trans) = GFT graph_trans
  where
    graph_trans :: GFTR (Graph n) n f
    graph_trans GNil        f = return (GNil, f)
    graph_trans (GUnit blk) f = block_trans blk f
    graph_trans (GMany entry blocks exit) f
      = do { (entry_g, f1)     <- block_trans entry f
           ; tx_fb             <- ft_blocks blocks f1
           ; (bs2, exit', f3)  <- ft_exit exit tx_fb 
	   ; let (entry', bs1) = ecGraph entry_g
           ; return (GMany entry' (bs1 ++ tfb_blks tx_fb ++ bs2) exit', f3) }

	-- It's a bit disgusting that the TxFactBase has to be
        -- preserved as far as the Exit block, becaues the TxFactBase
        -- is really concerned with the fixpoint calculation
        -- But I can't see any other tidy way to compute the 
        -- LastOutFacts in the NoTail case
    ft_exit :: Exit n x  -> Trans (TxFactBase n f) 
                                  (LBlocks n, Exit n x, OutFact x f)
    ft_exit (Tail bid blk) f 
      = do { (g, f1) <- block_trans blk (factBaseInFacts lattice f bid)
	   ; let (bs, exit) = cxGraph bid g
           ; return (bs, exit, f1) }
    ft_exit NoTail f 
      = return ([], NoTail, factBaseOutFacts f)

    ft_block_once :: LBlock n C -> Trans (TxFactBase n f) (TxFactBase n f)
    ft_block_once blk = updateFacts lattice gft_block blk

    ft_blocks_once :: LBlocks n -> Trans (TxFactBase n f) (TxFactBase n f)
    ft_blocks_once blks = foldr ((>>>) . ft_block_once) idTrans blks

    ft_blocks :: LBlocks n -> Trans (OutFactC f) (TxFactBase n f)
    ft_blocks blocks = fixpointTrans (ft_blocks_once (forwardBlockList blocks))

----------------------------------------------------------------
--       The pièce de resistance: cunning transfer functions
----------------------------------------------------------------

pureAnalysis :: Edges n => DataflowLattice f -> ForwardTransfers n f -> GFT_Graph n f
pureAnalysis lattice = gftGraph lattice . gftBlock . gftNodeTransfer

analyseAndRewrite
   :: forall n f. Edges n
   => RewritingDepth
   -> DataflowLattice f
   -> ForwardTransfers n f
   -> ForwardRewrites n f
   -> GFT_Graph n f

data RewritingDepth = RewriteShallow | RewriteDeep
-- When a transformation proposes to rewrite a node, 
-- you can either ask the system to
--  * "shallow": accept the new graph, analyse it without further rewriting
--  * "deep": recursively analyse-and-rewrite the new graph

analyseAndRewrite depth lattice transfers rewrites
  = gft_graph_cunning
  where 
    gft_graph_base, gft_graph_cunning, gft_graph_recurse :: GFT_Graph n f

    gft_graph_base    = gftGraph lattice (gftBlock gft_node_base)
    gft_graph_cunning = gftGraph lattice (gftBlock gft_node_cunning)
    gft_graph_recurse = case depth of
                          RewriteShallow -> gft_graph_base
                          RewriteDeep    -> gft_graph_cunning

    gft_node_base, gft_node_cunning :: GFT_Node n f
    gft_node_base    = gftNodeTransfer transfers
    gft_node_cunning = gftNodeRewrite  transfers rewrites gft_graph_recurse

-----------------------------------------------------------------------------
--		The fuel monad
-----------------------------------------------------------------------------

type Uniques = Int
type Fuel    = Int

newtype FuelMonad a = FM { unFM :: Fuel -> Uniques -> (a, Fuel, Uniques) }

instance Monad FuelMonad where
  return x = FM (\f u -> (x,f,u))
  m >>= k  = FM (\f u -> case unFM m f u of (r,f',u') -> unFM (k r) f' u')

fuelExhausted :: FuelMonad Bool
fuelExhausted = FM (\f u -> (f <= 0, f, u))

decrementFuel :: FuelMonad ()
decrementFuel = FM (\f u -> ((), f-1, u))

getFuel :: FuelMonad Fuel
getFuel = FM (\f u -> (f,f,u))

setFuel :: Fuel -> FuelMonad ()
setFuel f = FM (\_ u -> ((), f, u))

graphOfAGraph :: AGraph node e x -> FuelMonad (Graph node e x)
graphOfAGraph = error "urk" 	-- Stub

-----------------------------------------------------------------------------
--		BlockId, BlockEnv, BlockSet
-----------------------------------------------------------------------------

type BlockId = Int

mkBlockId :: Int -> BlockId
mkBlockId uniq = uniq

type BlockEnv a = M.IntMap a

mkBlockEnv :: [(BlockId, a)] -> BlockEnv a
mkBlockEnv prs = M.fromList prs

lookupBEnv :: DataflowLattice f -> BlockEnv f -> BlockId -> f
lookupBEnv lattice env blk_id 
  = case M.lookup blk_id env of
      Just f  -> f
      Nothing -> fact_bot lattice

extendBEnv :: BlockEnv f -> BlockId -> f -> BlockEnv f
extendBEnv env blk_id f = M.insert blk_id f env

blockEnvList :: BlockEnv f -> [(BlockId, f)]
blockEnvList env = M.toList env

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
