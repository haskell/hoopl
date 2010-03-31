{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies #-}

{- Notes about the genesis of Hoopl7
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Hoopl7 has the following major chages

a) GMany has symmetric entry and exit
b) GMany closed-entry does not record a BlockId
c) GMany open-exit does not record a BlockId
d) The body of a GMany is called Body
e) A Body is just a list of blocks, not a map. I've argued
   elsewhere that this is consistent with (c)

This was made possible by

* ForwardTransfer looks like this:
    type ForwardTransfer n f
      = forall e x. n e x -> Fact e f -> Fact x f 
    type family   Fact x f :: *
    type instance Fact C f = FactBase f
    type instance Fact O f = f

  Note that the incoming fact is a Fact (not just 'f' as in Hoopl5,6).
  It's up to the *transfer function* to look up the appropriate fact
  in the FactBase for a closed-entry node.  Example:
	constProp (Label l) fb = lookupFact fb l
  That is how Hoopl can avoid having to know the block-id for the
  first node: it defers to the client.

  [Side note: that means the client must know about 
  bottom, in case the looupFact returns Nothing]

* Note also that ForwardTransfer *returns* a Fact too;
  that is, the types in both directions are symmetrical.
  Previously we returned a [(BlockId,f)] but I could not see
  how to make everything line up if we do this.

  Indeed, the main shortcoming of Hoopl7 is that we are more
  or less forced into this uniform representation of the facts
  flowing into or out of a closed node/block/graph, whereas
  previously we had more flexibility.

  In exchange the code is neater, with fewer distinct types.
  And morally a FactBase is equivalent to [(BlockId,f)] and
  nearly equivalent to (BlockId -> f).

* I've realised that forwardBlockList and backwardBlockList
  both need (Edges n), and that goes everywhere.
-}

module Hoopl7 where

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

data Body n where
  BodyEmpty :: Body n
  BodyUnit  :: Block n C C -> Body n
  BodyCat   :: Body n -> Body n -> Body n

data Graph n e x where
  GNil  :: Graph n O O
  GUnit :: Block n O O -> Graph n O O
  GMany :: Link e (Block n O C) 
        -> Body n
        -> Link x (Block n C O)
        -> Graph n e x

data Link ex t where
  OpenLink   :: t -> Link O t
  ClosedLink ::      Link C t

-------------------------------
class Edges thing where
  entryBlockId :: thing C x -> BlockId
  successors :: thing e C -> [BlockId]

instance Edges n => Edges (Block n) where
  entryBlockId (BUnit n) = entryBlockId n
  entryBlockId (b `BCat` _) = entryBlockId b
  successors (BUnit n)   = successors n
  successors (BCat _ b)  = successors b

------------------------------
addBlock :: Block n C C -> Body n -> Body n
addBlock b body = BodyUnit b `BodyCat` body

bodyList :: Edges n => Body n -> [(BlockId,Block n C C)]
bodyList body = go body []
  where
    go BodyEmpty       bs = bs
    go (BodyUnit b)    bs = (entryBlockId b, b) : bs
    go (BodyCat b1 b2) bs = go b1 (go b2 bs)

-----------------------------------------------------------------------------
--		Defined here but not used
-----------------------------------------------------------------------------

-- Singletons
--   OO   GUnit
--   CO   GMany (ClosedLink l) [] (OpenLink b)
--   OC   GMany (OpenLink b)   []  ClosedLink
--   CC   GMany (ClosedLink l) [b] ClosedLink

gCat :: Graph n e a -> Graph n a x -> Graph n e x
gCat GNil g2 = g2
gCat g1 GNil = g1

gCat (GUnit b1) (GUnit b2)             
  = GUnit (b1 `BCat` b2)

gCat (GUnit b) (GMany (OpenLink e) bs x) 
  = GMany (OpenLink (b `BCat` e)) bs x

gCat (GMany e bs (OpenLink x)) (GUnit b2) 
   = GMany e bs (OpenLink (x `BCat` b2))

gCat (GMany e1 bs1 (OpenLink x1)) (GMany (OpenLink e2) bs2 x2)
   = GMany e1 (addBlock (x1 `BCat` e2) bs1 `BodyCat` bs2) x2

gCat (GMany e1 bs1 ClosedLink) (GMany ClosedLink bs2 x2)
   = GMany e1 (bs1 `BodyCat` bs2) x2

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


------------------------------
data OCFlag oc where
  IsOpen   :: OCFlag O
  IsClosed :: OCFlag C

class IsOC oc where
  ocFlag :: OCFlag oc

instance IsOC O where
  ocFlag = IsOpen
instance IsOC C where
  ocFlag = IsClosed

mkIfThenElse :: forall n x. (Edges n, IsOC x)
             => (BlockId -> BlockId -> n O C)	-- The conditional branch instruction
             -> (BlockId -> n C O)		-- Make a head node 
	     -> (BlockId -> n O C)		-- Make an unconditional branch
	     -> Graph n O x -> Graph n O x	-- Then and else branches
	     -> [BlockId]			-- Block supply
             -> Graph n O x			-- The complete thing
mkIfThenElse mk_cbranch mk_lbl mk_branch then_g else_g (tl:el:jl:_)
  = case (ocFlag :: OCFlag x) of
      IsOpen   -> gUnitOC (mk_cbranch tl el)
                  `gCat` (mk_lbl_g tl `gCat` then_g `gCat` mk_branch_g jl)
                  `gCat` (mk_lbl_g el `gCat` else_g `gCat` mk_branch_g jl)
                  `gCat` (mk_lbl_g jl)
      IsClosed -> gUnitOC (mk_cbranch tl el)
                  `gCat` (mk_lbl_g tl `gCat` then_g)
                  `gCat` (mk_lbl_g el `gCat` else_g)
  where
    mk_lbl_g :: BlockId -> Graph n C O
    mk_lbl_g lbl = gUnitCO (mk_lbl lbl)
    mk_branch_g :: BlockId -> Graph n O C
    mk_branch_g lbl = gUnitOC (mk_branch lbl)

gUnitCO :: n C O -> Graph n C O
gUnitCO n = GMany ClosedLink BodyEmpty (OpenLink (BUnit n))

gUnitOC :: n O C -> Graph n O C
gUnitOC n = GMany (OpenLink (BUnit n)) BodyEmpty ClosedLink

-----------------------------------------------------------------------------
--	RG: an internal data type for graphs under construction
--          TOTALLY internal to Hoopl
-----------------------------------------------------------------------------

data RG n f e x where	-- Will have facts too in due course
  RGNil   :: RG n f O O
  RGUnit  :: Fact e f -> Block n e x -> RG n f e x
  RGMany  :: BodyWithFacts n f -> RG n f C C
  RGCatO  :: RG n f e O -> RG n f O x -> RG n f e x
  RGCatC  :: RG n f e C -> RG n f C x -> RG n f e x

type BodyWithFacts  n f     = (Body n, FactBase f)
type GraphWithFacts n f e x = (Graph n e x, FactBase f)
  -- A Graph together with the facts for that graph
  -- The domains of the two maps should be identical

normaliseBody :: Edges n => RG n f C C -> BodyWithFacts n f
normaliseBody rg = (body, fact_base)
  where
    (GMany _ body _, fact_base) = normCC rg

normOO :: Edges n => RG n f O O -> GraphWithFacts n f O O
normOO RGNil          = (GNil, noFacts)
normOO (RGUnit _ b)   = (GUnit b, noFacts)
normOO (RGCatO g1 g2) = normOO g1 `gwfCat` normOO g2
normOO (RGCatC g1 g2) = normOC g1 `gwfCat` normCO g2

normOC :: Edges n => RG n f O C -> GraphWithFacts n f O C
normOC (RGUnit _ b)   = (GMany (OpenLink b) BodyEmpty ClosedLink, noFacts)
normOC (RGCatO g1 g2) = normOO g1 `gwfCat` normOC g2
normOC (RGCatC g1 g2) = normOC g1 `gwfCat` normCC g2

normCO :: Edges n => RG n f C O -> GraphWithFacts n f C O
normCO (RGUnit f b) = (GMany ClosedLink BodyEmpty (OpenLink b), unitFact l f)
                    where
                      l = entryBlockId b
normCO (RGCatO g1 g2) = normCO g1 `gwfCat` normOO g2
normCO (RGCatC g1 g2) = normCC g1 `gwfCat` normCO g2

normCC :: Edges n => RG n f C C -> GraphWithFacts n f C C
normCC (RGUnit f b) = (GMany ClosedLink (BodyUnit b) ClosedLink, unitFact l f)
                    where
                      l = entryBlockId b
normCC (RGMany (body,facts)) = (GMany ClosedLink body ClosedLink, facts)
normCC (RGCatO g1 g2) = normCO g1 `gwfCat` normOC g2
normCC (RGCatC g1 g2) = normCC g1 `gwfCat` normCC g2

noBWF :: BodyWithFacts n f
noBWF = (BodyEmpty, noFacts)

gwfCat :: Edges n => GraphWithFacts n f e a
                  -> GraphWithFacts n f a x 
                  -> GraphWithFacts n f e x
gwfCat (g1, fb1) (g2, fb2) = (g1 `gCat` g2, fb1 `unionFactBase` fb2)

bwfUnion :: BodyWithFacts n f -> BodyWithFacts n f -> BodyWithFacts n f
bwfUnion (bg1, fb1) (bg2, fb2) = (bg1 `BodyCat` bg2, fb1 `unionFactBase` fb2)

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
  = forall e x. n e x -> Fact e f -> Fact x f 

type ForwardRewrite n f 
  = forall e x. n e x -> Fact e f -> Maybe (AGraph n e x)

type family   Fact x f :: *
type instance Fact C f = FactBase f
type instance Fact O f = f

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

         , tfb_blks  :: BodyWithFacts n f  -- Transformed blocks
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

fixpoint :: forall n f. Edges n
         =>  DataflowLattice f
         -> (FactBase f -> Block n C C
              -> FuelMonad (FactBase f, RG n f C C))
         -> FactBase f 
         -> [(BlockId, Block n C C)]
         -> FuelMonad (FactBase f, BodyWithFacts n f)
fixpoint lat do_block init_fbase blocks
  = do { fuel <- getFuel  
       ; tx_fb <- loop fuel init_fbase
       ; return (tfb_fbase tx_fb `deleteFromFactBase` blocks, tfb_blks tx_fb) }
	     -- The successors of the Graph are the the BlockIds for which
	     -- we have facts, that are *not* in the blocks of the graph
  where
    tx_blocks :: [(BlockId, Block n C C)] 
              -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    tx_blocks []             tx_fb = return tx_fb
    tx_blocks ((lbl,blk):bs) tx_fb = do { tx_fb1 <- tx_block lbl blk tx_fb
                                        ; tx_blocks bs tx_fb1 }

    tx_block :: BlockId -> Block n C C 
             -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    tx_block lbl blk (TxFB { tfb_fbase = fbase, tfb_bids = lbls
                           , tfb_blks = blks, tfb_cha = cha })
      = do { (out_facts, rg) <- do_block fbase blk
           ; let (cha',fbase') = foldr (updateFact lat lbls) (cha,fbase) 
                                       (factBaseList out_facts)
		-- tfb_blks will be discarded unless we have 
		-- reached a fixed point, so it doesn't matter
		-- whether we get f from fbase or fbase'
           ; return (TxFB { tfb_bids  = extendBlockSet lbls lbl
                          , tfb_blks  = normaliseBody rg `bwfUnion` blks
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

type ARF thing n f = forall e x. Fact e f -> thing e x -> FuelMonad (Fact x f, RG n f e x)

type ARF_Node  n f = ARF n         n f
type ARF_Block n f = ARF (Block n) n f
type ARF_Graph n f = ARF (Graph n) n f
-----------------------------------------------------------------------------

arfNodeNoRW :: forall n f. ForwardTransfer n f -> ARF_Node n f
 -- Lifts ForwardTransfer to ARF_Node; simple transfer only
arfNodeNoRW transfer_fn f node
  = return (transfer_fn node f, RGUnit f (BUnit node))

arfNode :: forall n f. Edges n
        => DataflowLattice f
        -> ForwardTransfer n f
        -> ForwardRewrite n f
        -> ARF_Node n f
        -> ARF_Node n f
-- Lifts (ForwardTransfer,ForwardRewrite) to ARF_Node; 
-- this time we do rewriting as well. 
-- The ARF_Graph parameters specifies what to do with the rewritten graph
arfNode lattice transfer_fn rewrite_fn arf_node f node
  = do { mb_g <- withFuel (rewrite_fn node f)
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

arfBody :: forall n f. Edges n
          => DataflowLattice f 
          -> ARF_Node n f -> FactBase f -> Body n 
          -> FuelMonad (FactBase f, BodyWithFacts n f)
		-- Outgoing factbase is restricted to BlockIds *not* in
		-- in the Body; the facts for BlockIds
		-- *in* the Body are in the BodyWithFacts
arfBody lattice arf_node init_fbase blocks
  = fixpoint lattice (arfBlock arf_node) init_fbase $
    forwardBlockList (factBaseBlockIds init_fbase) blocks

arfGraph :: forall n f. Edges n
         => DataflowLattice f -> ARF_Node n f -> ARF_Graph n f
-- Lift from blocks to graphs
arfGraph _       _        f GNil        = return (f, RGNil)
arfGraph _       arf_node f (GUnit blk) = arfBlock arf_node f blk
arfGraph lat arf_node f (GMany ClosedLink body ClosedLink)
  = do { (fb, body') <- arfBody lat arf_node f body
       ; return (fb, RGMany body') }
arfGraph lat arf_node f (GMany ClosedLink body (OpenLink exit))
  = do { (fb, body') <- arfBody lat arf_node f body
       ; (fx, exit') <- arfBlock arf_node fb exit
       ; return (fx, RGMany body' `RGCatC` exit') }
arfGraph lat arf_node f (GMany (OpenLink entry) body ClosedLink)
  = do { (fe, entry') <- arfBlock arf_node f entry
       ; (fb, body') <- arfBody lat arf_node fe body
       ; return (fb, entry' `RGCatC` RGMany body') }
arfGraph lat arf_node f (GMany (OpenLink entry) body (OpenLink exit))
  = do { (fe, entry') <- arfBlock arf_node f entry
       ; (fb, body') <- arfBody lat arf_node fe body
       ; (fx, exit') <- arfBlock arf_node fb exit
       ; return (fx, entry' `RGCatC` RGMany body' `RGCatC` exit') }

forwardBlockList :: Edges n => [BlockId] -> Body n -> [(BlockId,Block n C C)]
-- This produces a list of blocks in order suitable for forward analysis.
-- ToDo: Do a topological sort to improve convergence rate of fixpoint
--       This will require a (HavingSuccessors l) class constraint
forwardBlockList  _ blks = bodyList blks

----------------------------------------------------------------
--       The pièce de resistance: cunning transfer functions
----------------------------------------------------------------

pureAnalysis :: Edges n => DataflowLattice f -> ForwardTransfer n f -> ARF_Graph n f
pureAnalysis lattice f = arfGraph lattice (arfNodeNoRW f)

analyseAndRewriteFwd
   :: forall n f. Edges n
   => DataflowLattice f
   -> ForwardTransfer n f
   -> ForwardRewrite n f
   -> RewritingDepth
   -> FactBase f
   -> Body n
   -> FuelMonad (Body n, FactBase f)

data RewritingDepth = RewriteShallow | RewriteDeep
-- When a transformation proposes to rewrite a node, 
-- you can either ask the system to
--  * "shallow": accept the new graph, analyse it without further rewriting
--  * "deep": recursively analyse-and-rewrite the new graph

analyseAndRewriteFwd lattice transfers rewrites depth facts graph
  = do { (_, gwf) <- arfBody lattice arf_node facts graph
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
  = forall e x. n e x -> Fact x f -> Fact e f 
type BackwardRewrite n f 
  = forall e x. n e x -> Fact x f -> Maybe (AGraph n e x)

type ARB thing n f = forall e x. Fact x f -> thing e x
                              -> FuelMonad (Fact e f, RG n f e x)

type ARB_Node  n f = ARB n         n f
type ARB_Block n f = ARB (Block n) n f
type ARB_Graph n f = ARB (Graph n) n f

arbNodeNoRW :: forall n f . BackwardTransfer n f -> ARB_Node n f
-- Lifts BackwardTransfer to ARB_Node; simple transfer only
arbNodeNoRW transfer_fn f node
  = return (entry_f, RGUnit entry_f (BUnit node))
  where
    entry_f = transfer_fn node f

arbNode :: forall n f. Edges n
        => DataflowLattice f
        -> BackwardTransfer n f
        -> BackwardRewrite n f
        -> ARB_Node n f
        -> ARB_Node n f
-- Lifts (BackwardTransfer,BackwardRewrite) to ARB_Node; 
-- this time we do rewriting as well. 
-- The ARB_Graph parameters specifies what to do with the rewritten graph
arbNode lattice transfer_fn rewrite_fn arf_node f node
  = do { mb_g <- withFuel (rewrite_fn node f)
       ; case mb_g of
           Nothing -> arbNodeNoRW transfer_fn f node
      	   Just ag -> do { g <- graphOfAGraph ag
      		         ; arbGraph lattice arf_node f g } }

arbBlock :: forall n f. ARB_Node n f -> ARB_Block n f
-- Lift from nodes to blocks
arbBlock arb_node f (BUnit node) = arb_node f node
arbBlock arb_node f (BCat b1 b2) = do { (f2,g2) <- arbBlock arb_node f  b2
                                      ; (f1,g1) <- arbBlock arb_node f2 b1
	                              ; return (f1, g1 `RGCatO` g2) }

arbBody :: forall n f. Edges n
        => DataflowLattice f 
        -> ARB_Node n f -> FactBase f
        -> Body n -> FuelMonad (FactBase f, BodyWithFacts n f)
arbBody lattice arb_node init_fbase blocks
  = fixpoint lattice (arbBlock arb_node) init_fbase $
    backwardBlockList (factBaseBlockIds init_fbase) blocks 

arbGraph :: forall n f. Edges n => DataflowLattice f -> ARB_Node n f -> ARB_Graph n f
arbGraph _       _        f GNil        = return (f, RGNil)
arbGraph _       arb_node f (GUnit blk) = arbBlock arb_node f blk
arbGraph lat arb_node f (GMany ClosedLink body ClosedLink)
  = do { (fb, body') <- arbBody lat arb_node f body
       ; return (fb, RGMany body') }
arbGraph lat arb_node f (GMany ClosedLink body (OpenLink exit))
  = do { (fx, exit') <- arbBlock arb_node f exit
       ; (fb, body') <- arbBody lat arb_node fx body
       ; return (fb, RGMany body' `RGCatC` exit') }
arbGraph lat arb_node f (GMany (OpenLink entry) body ClosedLink)
  = do { (fb, body') <- arbBody lat arb_node f body
       ; (fe, entry') <- arbBlock arb_node fb entry
       ; return (fe, entry' `RGCatC` RGMany body') }
arbGraph lat arb_node f (GMany (OpenLink entry) body (OpenLink exit))
  = do { (fx, exit') <- arbBlock arb_node f exit
       ; (fb, body') <- arbBody lat arb_node fx body
       ; (fe, entry') <- arbBlock arb_node fb entry
       ; return (fe, entry' `RGCatC` RGMany body' `RGCatC` exit') }

backwardBlockList :: Edges n => [BlockId] -> Body n -> [(BlockId,Block n C C)]
-- This produces a list of blocks in order suitable for backward analysis.
backwardBlockList _ blks = bodyList blks

analyseAndRewriteBwd
   :: forall n f. Edges n
   => DataflowLattice f
   -> BackwardTransfer n f
   -> BackwardRewrite n f
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

----------------------
type FactBase a = M.IntMap a

noFacts :: FactBase f
noFacts = M.empty

mkFactBase :: [(BlockId, f)] -> FactBase f
mkFactBase prs = M.fromList prs

unitFact :: BlockId -> FactBase f -> FactBase f
-- Restrict a fact base to a single fact
unitFact l fb = case M.lookup l fb of
                  Just f  -> M.singleton l f
                  Nothing -> M.empty

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
