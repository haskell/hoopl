{-# LANGUAGE ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards #-}

module CunningTransfers where

import qualified Data.IntMap as M
import qualified Data.IntSet as S

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
--		Graphs
-----------------------------------------------------------------------------

data ZOpen
data ZClosed

type O = ZOpen
type C = ZClosed

data ZBlock e x m l where
  ZFirst :: BlockId -> ZBlock C O m l
  ZMid   :: m 	    -> ZBlock O O m l
  ZLast  :: l 	    -> ZBlock O C m l
  ZCat   :: ZBlock e O m l -> ZBlock O x m l -> ZBlock e x m l

type ZHead = ZBlock C O
type ZMids = ZBlock O O
type ZTail = ZBlock O C
type Block = ZBlock C C

data ZGraph e x m l where
  ZGMany { zg_entry  :: ZBlock e C m l
     	 , zg_blocks :: BlockEnv (Block m l)
     	 , zg_exit   :: ZBlock C x m l } :: ZGraph e x m l
  ZGOne  { zg_mids :: ZMids m l }        :: ZGraph O O m l
  ZGNil                                  :: ZGraph O O m l

type Graph = ZGraph C C

forwardBlockList :: BlockEnv (Block m l) -> [(BlockId, Block m l)]
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
--		TxRes and ChangeFlags
-----------------------------------------------------------------------------

data ChangeFlag = NoChange | SomeChange
data TxRes a = TxRes ChangeFlag a


-----------------------------------------------------------------------------
--		The main Hoopl API
-----------------------------------------------------------------------------

data ForwardTransfers m l f 
  = ForwardTransfers
      { ft_lattice :: DataflowLattice f
      , ft_first   :: BlockId -> f -> f
      , ft_middle  :: m       -> f -> f
      , ft_last    :: l       -> f -> OutFacts f
      } 

data ForwardRewrites m l f 
  = ForwardRewrites
      { fr_first  :: BlockId -> f -> Maybe (AGraph C O m l)
      , fr_middle :: m       -> f -> Maybe (AGraph O O m l)
      , fr_last   :: l       -> f -> Maybe (AGraph O C m l)
      , fr_exit   ::            f -> Maybe (AGraph O O m l)
      } 

data AGraph e x m l = AGraph 	-- Stub for now

-----------------------------------------------------------------------------
--		The FactBase
-----------------------------------------------------------------------------

type FactBase fact = BlockEnv fact

getFact :: DataflowLattice fact -> FactBase fact -> BlockId -> fact
getFact lat fb id = lookupBEnv fb id `orElse` fact_bot lat


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
updateFact lat (bid, new_fact) tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = bids})
  | NoChange <- cha2        = tx_fb
  | bid `elemBlockSet` bids = tx_fb { tfb_fbase = new_fbase, tfb_cha = SomeChange }
  | otherwise               = tx_fb { tfb_fbase = new_fbase }
  where
    old_fact = lookupBEnv fbase bid `orElse` fact_bot lat
    TxRes cha2 res_fact = fact_add_to lat old_fact new_fact
    new_fbase = extendBEnv fbase bid res_fact

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
  = loop (mkBlockEnv out_facts)
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

data GFT co oo oc cc fact 
  = GFT { gft_lat :: DataflowLattice fact
       	, gft_co  :: co -> Trans (FactBase fact) fact
       	, gft_oo  :: oo -> Trans fact            fact
       	, gft_oc  :: oc -> Trans fact            (OutFacts fact)
       	, gft_cc  :: cc -> Trans (FactBase fact) (OutFacts fact) }
            
newtype OutFacts fact = OutFacts [(BlockId, fact)] 

  
----------------------------------------------------------------------------------------------
--                       closed/open      open/open        open/closed      closed/closed
----------------------------------------------------------------------------------------------
type GFT_Node  m l f = GFT BlockId          m                l                Void             f
type GFT_Block m l f = GFT (ZHead m l)      (ZMids m l)      (ZTail m l)      (Block m l)      f
type GFT_Graph m l f = GFT (ZGraph C O m l) (ZGraph O O m l) (ZGraph O C m l) (ZGraph C C m l) f
----------------------------------------------------------------------------------------------

data Void  -- There is no closed/closed node

gftNode :: forall m l f . ForwardTransfers m l f -> GFT_Node m l f
-- Injection from the external interface into the internal representation
gftNode (ForwardTransfers { ft_lattice = lattice
                          , ft_first  = first_fn
                          , ft_middle = middle_fn
                          , ft_last   = last_fn })
  = GFT { gft_lat = lattice
        , gft_co  = ft_first
        , gft_oo  = ft_middle 
        , gft_oc  = ft_last
        , gft_cc  = error "f_cc for node is undefined" }
    where 
      ft_first blk_id fb  = return (first_fn  blk_id (getFact lattice fb blk_id))
      ft_middle node fact = return (middle_fn node fact)
      ft_last node fact   = return (last_fn   node fact)

gftBlock :: forall m l f. GFT_Node m l f -> GFT_Block m l f
-- Lift from nodes to blocks
gftBlock (GFT { gft_lat = lat, gft_co = ft_first
               , gft_oo = ft_middle, gft_oc = ft_last })
  = GFT { gft_lat = lat
       	, gft_co  = ft_head 
       	, gft_oo  = ft_mids
       	, gft_oc  = ft_tail
       	, gft_cc  = ft_block }
  where 
    ft_head :: ZBlock C O m l -> Trans (FactBase f) f
    ft_head (ZFirst blk_id)  = ft_first blk_id
    ft_head (ZCat head mids) = ft_head head >>> ft_mids mids

    ft_mids :: ZBlock O O m l -> Trans f f
    ft_mids (ZMid node)  = ft_middle node
    ft_mids (ZCat m1 m2) = ft_mids m1 >>> ft_mids m2

    ft_tail :: ZBlock O C m l -> Trans f (OutFacts f)
    ft_tail (ZLast node)     = ft_last node
    ft_tail (ZCat mids tail) = ft_mids mids >>> ft_tail tail

    ft_block :: ZBlock C C m l -> Trans (FactBase f) (OutFacts f)
    ft_block (ZCat head tail) = ft_head head >>> ft_tail tail

gftGraph :: forall m l f. GFT_Block m l f -> GFT_Graph m l f
-- Lift from blocks to graphs
gftGraph (GFT { gft_lat = lat
               , gft_co = ft_head, gft_oo = ft_mids
               , gft_oc = ft_tail, gft_cc = ft_block })
  = GFT { gft_lat = lat
        , gft_co  = ft_co
        , gft_oo  = ft_oo
        , gft_oc  = ft_oc
        , gft_cc  = ft_cc }
  where
	-- These functions are orgasmically beautiful
    ft_co :: ZGraph C O m l -> Trans (FactBase f) f
    ft_co (ZGMany { zg_entry = entry, zg_blocks = blocks, zg_exit = exit })
      = ft_block entry >>> ft_blocks blocks >>> ft_head exit

    ft_oo :: ZGraph O O m l -> Trans f f
    ft_oo ZGNil        = idTrans
    ft_oo (ZGOne mids) = ft_mids mids
    ft_oo (ZGMany { zg_entry = entry, zg_blocks = blocks, zg_exit = exit })
      = ft_tail entry >>> ft_blocks blocks >>> ft_head exit

    ft_oc :: ZGraph O C m l -> Trans f (OutFacts f)
    ft_oc (ZGMany { zg_entry = entry, zg_blocks = blocks, zg_exit = exit })
      = ft_tail entry >>> ft_blocks blocks >>> ft_block exit

    ft_cc :: ZGraph C C m l -> Trans (FactBase f) (OutFacts f)
    ft_cc (ZGMany { zg_entry = entry, zg_blocks = blocks, zg_exit = exit })
      = ft_block entry >>> ft_blocks blocks >>> ft_block exit

    ft_blocks :: BlockEnv (Block m l) -> Trans (OutFacts f) (FactBase f)
    ft_blocks blocks = fixpointTrans (ft_blocks_once (forwardBlockList blocks))

    ft_blocks_once :: [(BlockId, Block m l)] -> Trans (TxFactBase f) (TxFactBase f)
    ft_blocks_once blks = foldr ((>>>) . ft_block_once) idTrans blks

    ft_block_once :: (BlockId, Block m l)
                  -> Trans (TxFactBase f) (TxFactBase f)
    ft_block_once (blk_id, blk) = updateFacts lat blk_id (ft_block blk)


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

graphOfAGraph :: AGraph e x m l -> FuelMonad (ZGraph e x m l)
graphOfAGraph = error "urk" 	-- Stub

-----------------------------------------------------------------------------
--		Utility functions
-----------------------------------------------------------------------------

orElse :: Maybe a -> a -> a
orElse (Just x) _ = x
orElse Nothing  y = y



----------------------------------------------------------------
--       The pièce de resistance: cunning transfer functions
----------------------------------------------------------------

pureAnalysis :: ForwardTransfers m l f -> GFT_Graph m l f
pureAnalysis = gftGraph . gftBlock . gftNode

analyseAndRewrite
   :: forall m l f . 
      RewritingDepth
   -> ForwardTransfers m l f
   -> ForwardRewrites m l f
   -> GFT_Graph m l f

data RewritingDepth = RewriteShallow | RewriteDeep
-- When a transformation proposes to rewrite a node, 
-- you can either ask the system to
--  * "shallow": accept the new graph, analyse it without further rewriting
--  * "deep": recursively analyse-and-rewrite the new graph


analyseAndRewrite depth transfers rewrites
  = gft_graph_cunning
  where 
    lat = ft_lattice transfers

    gft_graph_base, gft_graph_cunning, gft_graph_recurse :: GFT_Graph m l f

    gft_graph_base    = gftGraph (gftBlock gft_node_base)
    gft_graph_cunning = gftGraph (gftBlock gft_node_cunning)
    gft_graph_recurse = case depth of
                          RewriteShallow -> gft_graph_base
                          RewriteDeep    -> gft_graph_cunning

    gft_node_base, gft_node_cunning :: GFT_Node m l f
    gft_node_base    = gftNode transfers
    gft_node_cunning = GFT { gft_lat = lat
        	   	   , gft_co  = cunning_first
        	   	   , gft_oo  = cunning_middle 
        	   	   , gft_oc  = cunning_last
        	   	   , gft_cc  = error "f_cc for node is undefined" }

    cunning_first :: BlockId -> Trans (FactBase f) f
    cunning_first bid = tryRewrite (rw_first bid)
                                   (gft_co gft_graph_recurse)
                                   (gft_co gft_node_base bid) 

    rw_first :: BlockId -> FactBase f -> Maybe (AGraph C O m l)
    rw_first bid fb = fr_first rewrites bid (getFact lat fb bid)

    cunning_middle :: m -> Trans f f
    cunning_middle mid = tryRewrite (fr_middle rewrites mid)
                                    (gft_oo gft_graph_recurse)
                                    (gft_oo gft_node_base mid)

    cunning_last :: l -> Trans f (OutFacts f)
    cunning_last last = tryRewrite (fr_last rewrites last)
                                   (gft_oc gft_graph_recurse)
                                   (gft_oc gft_node_base last)

-----------
tryRewrite :: (a -> (Maybe (AGraph e x m l)))	-- The rewriter
           -> (ZGraph e x m l -> Trans a r)	-- Rewrite succeeds
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
