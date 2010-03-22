{-# OPTIONS_GHC -Wall -fno-warn-incomplete-patterns #-}
-- With GHC 6.10 we get bogus incomplete-pattern warnings
-- It's fine in 6.12
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, 
             PatternGuards, TypeFamilies #-}

-- This version uses type families to express the functional dependency
-- between the open/closed-ness of the input graph and the type of the
-- input fact expected for a graph of that shape

module Hoopl (BlockId, O, C, Block (..), Graph (..), Link (..), AGraph, InFact (..),
              BlockEnv, findBEnv, mkBlockEnv, lookupFact, Edges (..), ChangeFlag (..),
              analyseAndRewrite, RewritingDepth (..), mkFactBase, agraphOfNode, runFuelMonad,
              TxRes (..), DataflowLattice (..), ForwardTransfers, ForwardRewrites) where

import qualified Data.IntMap as M
import qualified Data.IntSet as S

-----------------------------------------------------------------------------
--		Graphs
-----------------------------------------------------------------------------

data ZOpen
data ZClosed

type O = ZOpen
type C = ZClosed

data OCFlag oc where
  IsOpen   :: OCFlag O
  IsClosed :: OCFlag C

class IsOC oc where
  ocFlag :: OCFlag oc

instance IsOC ZOpen where
  ocFlag = IsOpen
instance IsOC ZClosed where
  ocFlag = IsClosed

----------------------
-- Blocks are always non-empty
data Block n e x where
  BUnit :: n e x -> Block n e x
  BCat  :: Block n e O -> Block n O x -> Block n e x

----------------------
type Blocks n = [Block n C C]

unionBlocks :: Blocks n    -> Blocks n -> Blocks n
addBlock    :: Block n C C -> Blocks n -> Blocks n

unionBlocks = (++)
addBlock = (:)

----------------------
data Graph n e x where
  GNil  :: Graph n a a
  GMids :: Block n O O -> Graph n O O
  GMany { g_entry  :: Link e (Block n O C)
        , g_blocks :: Blocks n
        , g_exit   :: Link x (Block n C O) } :: Graph n e x

data Link shape thing where
  ClosedLink :: Link C thing
  OpenLink   :: thing -> Link O thing

gCat :: Graph n e a -> Graph n a x -> Graph n e x
gCat GNil g2 = g2
gCat g1 GNil = g1

gCat (GMids b1) (GMids b2) = GMids $ b1 `BCat` b2

gCat (GMids b1) (GMany (OpenLink entry) bs x) = GMany (OpenLink (b1 `BCat` entry)) bs x
gCat (GMany e bs (OpenLink exit)) (GMids b2) = GMany e bs (OpenLink (exit `BCat` b2))

gCat (GMany e1 bs1 ClosedLink) (GMany ClosedLink bs2 x2) = GMany e1 bs x2
  where bs = bs1 `unionBlocks` bs2

gCat (GMany e1 bs1 (OpenLink head)) (GMany (OpenLink tail) bs2 x2)
  = GMany e1 bs x2
  where bs = addBlock (head `BCat` tail) $ bs1 `unionBlocks` bs2

gCat _ _ = error "Should be statically impossible"

class Edges thing where
  blockId    :: thing C x -> BlockId
  successors :: thing e C -> [BlockId]

instance Edges n => Edges (Block n) where
  blockId    (BUnit n)  = blockId n
  blockId    (BCat b _) = blockId b
  successors (BUnit n)  = successors n
  successors (BCat _ b) = successors b

forwardBlockList :: Blocks n -> Blocks n
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

type family   InFact e f :: *
type instance InFact C f = InFactC f
type instance InFact O f = f

type InFactC  f = FactBase f
type OutFactC f = FactBase f

type OutFact x f = InFact x f
{-
type family   OutFact x f :: *
type instance OutFact C f = OutFactC f
type instance OutFact O f = f
type OutFactC f = FactBase f
-}

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

         , tfb_blks  :: Graph n C C   -- Transformed blocks
    }

factBaseInFacts :: TxFactBase n f -> InFactC f
factBaseInFacts (TxFB { tfb_fbase = fbase }) 
  = fbase

factBaseOutFacts :: TxFactBase n f -> OutFactC f
factBaseOutFacts (TxFB { tfb_fbase = fbase }) 
  = fbase

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
            -> GFT_Block n f
            -> Block n C C
            -> Trans (TxFactBase n f) (TxFactBase n f)
updateFacts lat (GFT block_trans) blk
    tx_fb@(TxFB { tfb_fbase = fbase, tfb_bids = bids, tfb_blks = graph_so_far })
  = do { (graph, out_facts) <- block_trans blk fbase
       ; let tx_fb' = tx_fb { tfb_bids = extendBlockSet bids (blockId blk)
                            , tfb_blks = graph `gCat` graph_so_far }
       ; return (foldr (updateFact lat) tx_fb' (factBaseList out_facts)) }
		-- We are expecting the out_facts to be small...

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
       ; loop fuel out_facts }
  where
    loop :: Fuel -> Trans (FactBase f) (TxFactBase n f)
    loop fuel fbase 
      = do { tx_fb <- tx_fb_trans (TxFB { tfb_fbase = fbase
                                        , tfb_cha = NoChange
                                        , tfb_blks = GNil
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
type GFTR thing n f = forall e x. (IsOC e, IsOC x)
                               => thing e x 
                               -> InFact e f
                               -> FuelMonad (Graph n e x, OutFact x f)

type GFT_Node  n f = GFT n         n f
type GFT_Block n f = GFT (Block n) n f
type GFT_Graph n f = GFT (Graph n) n f
-----------------------------------------------------------------------------

nodeGraph :: forall n e x. (IsOC e, IsOC x) => n e x -> Graph n e x
nodeGraph = mkG (ocFlag :: OCFlag e) (ocFlag :: OCFlag x)
  where
    mkG :: OCFlag e -> OCFlag x -> n e x -> Graph n e x
    mkG IsOpen   IsOpen   n = GMids (BUnit n)
    mkG IsOpen   IsClosed n = GMany (OpenLink (BUnit n)) []        ClosedLink
    mkG IsClosed IsOpen   n = GMany ClosedLink           []        (OpenLink (BUnit n))
    mkG IsClosed IsClosed n = GMany ClosedLink           [BUnit n] ClosedLink
 
gftNodeTransfer :: forall n f . ForwardTransfers n f -> GFT_Node n f
-- Lifts ForwardTransfers to GFT_Node; simple transfer only
gftNodeTransfer base_trans = GFT node_trans
    where 
      node_trans :: GFTR n n f
      node_trans node f = return (nodeGraph node, base_trans node f)

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
    node_trans node f = return (nodeGraph node, transfers node f)

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
    graph_trans (GMids blk) f = block_trans blk f
    graph_trans (GMany entry blocks exit) f
      = do { (entry', f1)  <- entry_trans entry f
           ; tx_fb         <- blocks_trans blocks f1
           ; (exit', f3)   <- exit_trans exit tx_fb 
           ; return (entry' `gCat` tfb_blks tx_fb `gCat` exit', f3) }

    entry_trans :: Link e (Block n O C)
                -> Trans (InFact e f) (Graph n e C, FactBase f)
    entry_trans ClosedLink     f = return (GNil, f)
    entry_trans (OpenLink blk) f = block_trans blk f

	-- It's a bit disgusting that the TxFactBase has to be
        -- preserved as far as the Exit block, becaues the TxFactBase
        -- is really concerned with the fixpoint calculation
        -- But I can't see any other tidy way to compute the 
        -- LastOutFacts in the NoTail case
    exit_trans :: Link x (Block n C O)
               -> Trans (TxFactBase n f) (Graph n C x, OutFact x f)
    exit_trans ClosedLink f = return (GNil, factBaseOutFacts f)
    exit_trans (OpenLink blk) f = block_trans blk (factBaseInFacts f)

    block_once :: Block n C C -> Trans (TxFactBase n f) (TxFactBase n f)
    block_once blk = updateFacts lattice gft_block blk

    blocks_once :: Blocks n -> Trans (TxFactBase n f) (TxFactBase n f)
    blocks_once blks = foldr ((>>>) . block_once) idTrans blks

    blocks_trans :: [Block n C C] -> Trans (FactBase f) (TxFactBase n f)
    blocks_trans blocks = fixpointTrans (blocks_once (forwardBlockList blocks))

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

runFuelMonad :: (IsOC e, IsOC x) => GFT (Graph n) n f -> Graph n e x -> InFact e f -> Fuel -> Uniques -> Graph n e x
runFuelMonad (GFT f) g fact fuel uniqs = g'
  where fm = f g fact
        ((g', _), _, _) = unFM fm fuel uniqs

fuelExhausted :: FuelMonad Bool
fuelExhausted = FM (\f u -> (f <= 0, f, u))

decrementFuel :: FuelMonad ()
decrementFuel = FM (\f u -> ((), f-1, u))

getFuel :: FuelMonad Fuel
getFuel = FM (\f u -> (f,f,u))

setFuel :: Fuel -> FuelMonad ()
setFuel f = FM (\_ u -> ((), f, u))

getUnique :: FuelMonad Uniques
getUnique = FM (\f u -> (u, f, u+1))

-----------------------------------------------------------------------------
--      AGraphs
-----------------------------------------------------------------------------

type AGraph n e x = FuelMonad (Graph n e x)

graphOfAGraph :: AGraph node e x -> FuelMonad (Graph node e x)
graphOfAGraph a = a

-- Expedient, but not what we really want:
agraphOfNode :: (IsOC e, IsOC x) => n e x -> AGraph n e x
agraphOfNode = return . nodeGraph

-----------------------------------------------------------------------------
--		BlockId, BlockEnv, BlockSet
-----------------------------------------------------------------------------

type BlockId = Int

mkBlockId :: Int -> BlockId
mkBlockId uniq = uniq

type FactBase a = M.IntMap a
type BlockEnv a = FactBase a

mkBlockEnv, mkFactBase :: [(BlockId, f)] -> FactBase f
mkFactBase prs = M.fromList prs
mkBlockEnv = mkFactBase

lookupFact :: DataflowLattice f -> FactBase f -> BlockId -> f
lookupFact lattice env blk_id 
  = case M.lookup blk_id env of
      Just f  -> f
      Nothing -> fact_bot lattice

findBEnv :: BlockEnv a -> BlockId -> Maybe a
findBEnv env blk_id = M.lookup blk_id env


extendFactBase :: FactBase f -> BlockId -> f -> FactBase f
extendFactBase env blk_id f = M.insert blk_id f env

unionFactBase :: FactBase f -> FactBase f -> FactBase f
unionFactBase = M.union

factBaseList :: FactBase f -> [(BlockId, f)]
factBaseList env = M.toList env

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
