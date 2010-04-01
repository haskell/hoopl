{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies #-}

-- This version uses type families to express the functional dependency
-- between the open/closed-ness of the input graph and the type of the
-- input fact expected for a graph of that shape

module CunningTransfers( pureAnalysis, analyseAndRewrite ) where

import qualified Data.IntMap as M
import qualified Data.IntSet as S

-----------------------------------------------------------------------------
--		Graphs
-----------------------------------------------------------------------------

data ZOpen
data ZClosed

type O = ZOpen
type C = ZClosed

-- This data type is NOT MENTIONED in the rest of the code.
-- It's just an example to how how we can embed our existing
-- middle/last idea into the new story
data ZNode m l e x where
  ZFirst :: BlockId -> ZNode m l C O
  ZMid   :: m 	    -> ZNode m l O O
  ZLast  :: l 	    -> ZNode m l O C

data ZBlock node e x where
  ZBOne :: node e x -> ZBlock node e x
  ZCat  :: ZBlock node e O -> ZBlock node O x -> ZBlock node e x

type Block node = ZBlock node C C

data ZGraph node e x where
  ZGMany { zg_entry  :: ZBlock node e C
     	 , zg_blocks :: BlockEnv (Block node)
     	 , zg_exit   :: ZBlock node C x } :: ZGraph node e x
  ZGOne  { zg_mids   :: ZBlock node O O } :: ZGraph node O O 
  ZGNil                                   :: ZGraph node O O

type Graph node = ZGraph node C C

forwardBlockList :: BlockEnv (Block node) -> [(BlockId, Block node)]
-- This produces a list of blocks in order suitable for forward analysis.
-- ToDo: Do a topological sort to improve convergence rate of fixpoint
--       This will require a (HavingSuccessors l) class constraint
forwardBlockList env = M.toList env

-----------------------------------------------------------------------------
--		DataflowLattice
-----------------------------------------------------------------------------

data DataflowLattice a = DataflowLattice  { 
  fact_name       :: String,                 -- Documentation
  fact_bot        :: a,                      -- Lattice bottom element
  fact_add_to     :: a -> a -> TxRes a,      -- Lattice join plus change flag
  fact_do_logging :: Bool                    -- log changes
}

-----------------------------------------------------------------------------
--		The main Hoopl API
-----------------------------------------------------------------------------

data ForwardTransfers node f 
  = ForwardTransfers
      { ft_trans   :: forall e x. node e x -> InT e f -> OutT x f } 

data ForwardRewrites node f 
  = ForwardRewrites
      { fr_rw :: forall e x. node e x -> InT e f -> Maybe (AGraph node e x) } 

type family   InT e f :: *
type instance InT C f = FactBase f
type instance InT O f = f

type family   OutT x f :: *
type instance OutT C f = OutFacts f
type instance OutT O f = f

newtype OutFacts fact = OutFacts [(BlockId, fact)] 
newtype FactBase fact = FactBase (BlockEnv fact)

data AGraph node e x = AGraph 	-- Stub for now


-----------------------------------------------------------------------------
--      TxFactBase: a FactBase with ChangeFlag information
-----------------------------------------------------------------------------

-- A TxFactBase carries a ChangeFlag with it, and a set of BlockIds
-- to monitor. Updates to other BlockIds don't affect the ChangeFlag
data TxFactBase fact 
  = TxFB { tfb_fbase :: FactBase fact
         , tfb_cha   :: ChangeFlag
         , tfb_bids  :: BlockSet  -- Update change flag iff these blocks change
    }

updateFact :: DataflowLattice f -> (BlockId, f)
           -> TxFactBase f -> TxFactBase f
-- Update a TxFactBase, setting the change flag iff
--   a) the new fact adds information...
--   b) for a block in the BlockSet in the TxFactBase
updateFact lat (bid, new_fact) tx_fb@(TxFB { tfb_fbase = FactBase fbase, tfb_bids = bids})
  | NoChange <- cha2        = tx_fb
  | bid `elemBlockSet` bids = tx_fb { tfb_fbase = new_fbase, tfb_cha = SomeChange }
  | otherwise               = tx_fb { tfb_fbase = new_fbase }
  where
    old_fact = lookupBEnv fbase bid `orElse` fact_bot lat
    TxRes cha2 res_fact = fact_add_to lat old_fact new_fact
    new_fbase = FactBase (extendBEnv fbase bid res_fact)

updateFacts :: DataflowLattice f -> BlockId
            -> Trans (FactBase f)   (OutFacts f)
            -> Trans (TxFactBase f) (TxFactBase f)
updateFacts lat bid thing_inside tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = bids })
  = do { OutFacts out_facts <- thing_inside fbase
       ; let tx_fb' = tx_fb { tfb_bids = extendBlockSet bids bid }
       ; return (foldr (updateFact lat) tx_fb out_facts) }

-----------------------------------------------------------------------------
--		The Trans arrow
-----------------------------------------------------------------------------

type Trans a b = a -> FuelMonad b
 -- Transform a into b, with facts of type f
 -- Deals with optimsation fuel and unique supply too
  
(>>>) :: Trans a b -> Trans b c -> Trans a c
-- Compose two dataflow transfers in sequence
(dft1 >>> dft2) f1 = do { f2 <- dft1 f1; dft2 f2 }

liftTrans :: (a->b) -> Trans a b
liftTrans f x = return (f x)

idTrans :: Trans a a
idTrans x = return x

fixpointTrans :: forall f. Trans (TxFactBase f) (TxFactBase f) 
                        -> Trans (OutFacts f)   (FactBase f)
fixpointTrans thing_inside (OutFacts out_facts)
  = loop (FactBase (mkBlockEnv out_facts))
  where
    loop :: Trans (FactBase f) (FactBase f)
    loop fbase = do { tx_fb <- thing_inside (TxFB { tfb_fbase = fbase
                                                  , tfb_cha = NoChange
                                                  , tfb_bids = emptyBlockSet })
                    ; case tfb_cha tx_fb of
                        NoChange   -> return fbase
                        SomeChange -> loop (tfb_fbase tx_fb) }

-----------------------------------------------------------------------------
--		Transfer functions
-----------------------------------------------------------------------------

-- Keys to the castle: a generic transfer function for each shape
-- Here's the idea: we start with single-node transfer functions,
-- move to basic-block transfer functions (we have exactly four shapes),
-- then finally to graph transfer functions (which requires iteration).

data GFT thing fact 
  = GFT { gft_trans :: forall e x. thing e x -> Trans (InT e fact) (OutT x fact) }

type GFT_Node  node = GFT node
type GFT_Block node = GFT (ZBlock node)
type GFT_Graph node = GFT (ZGraph node)
----------------------------------------------------------------------------------------------

gftNode :: forall node f . ForwardTransfers node f -> GFT_Node node f
-- Injection from the external interface into the internal representation
gftNode (ForwardTransfers { ft_trans = base_trans })
  = GFT { gft_trans = node_trans }
    where 
      node_trans :: node e x -> Trans (InT e f) (OutT x f)
      node_trans node f = return (base_trans node f)

gftBlock :: forall node f. GFT_Node node f -> GFT_Block node f
-- Lift from nodes to blocks
gftBlock (GFT { gft_trans = node_trans })
  = GFT { gft_trans  = block_trans }
  where 
    block_trans :: ZBlock node e x -> Trans (InT e f) (OutT x f)
    block_trans (ZBOne node)     = node_trans node
    block_trans (ZCat head mids) = block_trans head >>> block_trans mids

gftGraph :: forall node f. DataflowLattice f -> GFT_Block node f -> GFT_Graph node f
-- Lift from blocks to graphs
gftGraph lattice (GFT { gft_trans = block_trans })
  = GFT { gft_trans = graph_trans }
  where
	-- These functions are orgasmically beautiful
    graph_trans :: ZGraph node e x -> Trans (InT e f) (OutT x f)
    graph_trans ZGNil        = idTrans
    graph_trans (ZGOne mids) = block_trans mids
    graph_trans (ZGMany { zg_entry = entry, zg_blocks = blocks, zg_exit = exit })
      = block_trans entry >>> ft_blocks blocks >>> block_trans exit

    ft_blocks :: BlockEnv (Block node) -> Trans (OutFacts f) (FactBase f)
    ft_blocks blocks = fixpointTrans (ft_blocks_once (forwardBlockList blocks))

    ft_blocks_once :: [(BlockId, Block node)] -> Trans (TxFactBase f) (TxFactBase f)
    ft_blocks_once blks = foldr ((>>>) . ft_block_once) idTrans blks

    ft_block_once :: (BlockId, Block node)
                  -> Trans (TxFactBase f) (TxFactBase f)
    ft_block_once (blk_id, blk) = updateFacts lattice blk_id (block_trans blk)



----------------------------------------------------------------
--       The pièce de resistance: cunning transfer functions
----------------------------------------------------------------

pureAnalysis :: DataflowLattice f -> ForwardTransfers node f -> GFT_Graph node f
pureAnalysis lattice = gftGraph lattice . gftBlock . gftNode 

analyseAndRewrite
   :: forall node f . 
      RewritingDepth
   -> DataflowLattice f
   -> ForwardTransfers node f
   -> ForwardRewrites node f
   -> GFT_Graph node f

data RewritingDepth = RewriteShallow | RewriteDeep
-- When a transformation proposes to rewrite a node, 
-- you can either ask the system to
--  * "shallow": accept the new graph, analyse it without further rewriting
--  * "deep": recursively analyse-and-rewrite the new graph

analyseAndRewrite depth lattice transfers rewrites
  = gft_graph_cunning
  where 
    gft_graph_base, gft_graph_cunning, gft_graph_recurse :: GFT_Graph node f

    gft_graph_base    = gftGraph lattice (gftBlock gft_node_base)
    gft_graph_cunning = gftGraph lattice (gftBlock gft_node_cunning)
    gft_graph_recurse = case depth of
                          RewriteShallow -> gft_graph_base
                          RewriteDeep    -> gft_graph_cunning

    gft_node_base, gft_node_cunning :: GFT_Node node f
    gft_node_base    = gftNode transfers
    gft_node_cunning = GFT { gft_trans  = cunning_trans }

    cunning_trans :: node e x -> Trans (InT e f) (OutT x f)
    cunning_trans node = tryRewrite (fr_rw rewrites node)
                                    (gft_trans gft_graph_recurse)
                                    (gft_trans gft_node_base node) 


-----------------------------------------------------------------------------
--		Rewriting
-----------------------------------------------------------------------------

{-
data GRT co oo oc cc fact 
  = GRT { grt_lat :: DataflowLattice fact
       	, grt_co  :: co -> Trans (FactBase fact) (fact, Graph C O m l)
       	, grt_oo  :: oo -> Trans fact            (fact, Graph O O m l)
       	, grt_oc  :: oc -> Trans fact            (OutFacts fact)
       	, gRt_cc  :: cc -> Trans (FactBase fact) (OutFacts fact) }
-}

-----------------------------------------------------------------------------
--		BlockId, BlockEnv, BlockSet
-----------------------------------------------------------------------------

type BlockId = Int

mkBlockId :: Int -> BlockId
mkBlockId uniq = uniq

type BlockEnv a = M.IntMap a

mkBlockEnv :: [(BlockId, a)] -> BlockEnv a
mkBlockEnv prs = M.fromList prs

lookupBEnv :: BlockEnv f -> BlockId -> Maybe f
lookupBEnv env blk_id = M.lookup blk_id env

extendBEnv :: BlockEnv f -> BlockId -> f -> BlockEnv f
extendBEnv env blk_id f = M.insert blk_id f env

type BlockSet = S.IntSet

emptyBlockSet :: BlockSet
emptyBlockSet = S.empty

extendBlockSet :: BlockSet -> BlockId -> BlockSet
extendBlockSet bids bid = S.insert bid bids

elemBlockSet :: BlockId -> BlockSet -> Bool
elemBlockSet bid bids = S.member bid bids

-----------------------------------------------------------------------------
--		TxRes and ChangeFlags
-----------------------------------------------------------------------------

data ChangeFlag = NoChange | SomeChange
data TxRes a = TxRes ChangeFlag a


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

-----------
tryRewrite :: (a -> (Maybe (AGraph node e x)))	-- The rewriter
           -> (ZGraph node e x -> Trans a r)	-- Rewrite succeeds
           -> Trans a r				-- Rewrite fails
           -> Trans a r
tryRewrite rewriter do_yes do_no a
  = case (rewriter a) of
      Nothing -> do_no a
      Just g  -> do { out <- fuelExhausted
       		    ; if out then do_no a
       		      else do { decrementFuel
       		              ; g' <- graphOfAGraph g
       		              ; do_yes g' a } }

graphOfAGraph :: AGraph node e x -> FuelMonad (ZGraph node e x)
graphOfAGraph = error "urk" 	-- Stub

-----------------------------------------------------------------------------
--		Utility functions
-----------------------------------------------------------------------------

orElse :: Maybe a -> a -> a
orElse (Just x) _ = x
orElse Nothing  y = y
