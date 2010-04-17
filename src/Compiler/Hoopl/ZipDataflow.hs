{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- bug in GHC

{- Notes about the genesis of Hoopl7
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Hoopl7 has the following major chages

a) GMany has symmetric entry and exit
b) GMany closed-entry does not record a BlockId
c) GMany open-exit does not record a BlockId
d) The body of a GMany is called Body
e) A Body is just a list of blocks, not a map. I've argued
   elsewhere that this is consistent with (c)

A consequence is that Graph is no longer an instance of Edges,
but nevertheless I managed to keep the ARF and ARB signatures
nice and uniform.

This was made possible by

* FwdTransfer looks like this:
    type FwdTransfer n f
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

* Note also that FwdTransfer *returns* a Fact too;
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

* I renamed BlockId to Label
-}

module Compiler.Hoopl.ZipDataflow 
  ( FwdPass(..),  FwdTransfer, FwdRewrite, FwdRes(..)
  , BwdPass(..), BwdTransfer, BwdRewrite, BwdRes(..)
  , analyzeAndRewriteFwd,  analyzeAndRewriteBwd
  , analyzeAndRewriteFwd', analyzeAndRewriteBwd'
  )
where

import Compiler.Hoopl.Dataflow 
           ( DataflowLattice(..), OldFact(..), NewFact(..)
           , ChangeFlag(..)
           , Fact
           )
import Compiler.Hoopl.Fuel
import Compiler.Hoopl.Graph
import qualified Compiler.Hoopl.GraphUtil as U
import Compiler.Hoopl.Label
import Compiler.Hoopl.Util
import Compiler.Hoopl.Zipper

type AGraph n e x = FuelMonad (ZGraph n e x)
graphOfAGraph :: AGraph n e x -> FuelMonad (ZGraph n e x)
graphOfAGraph = id

-----------------------------------------------------------------------------
--		Analyze and rewrite forward: the interface
-----------------------------------------------------------------------------

data FwdPass n f
  = FwdPass { fp_lattice  :: DataflowLattice f
            , fp_transfer :: FwdTransfer n f
            , fp_rewrite  :: FwdRewrite n f }

type FwdTransfer n f 
  = forall e x. n e x -> Fact e f -> Fact x f 

type FwdRewrite n f 
  = forall e x. n e x -> Fact e f -> Maybe (FwdRes n f e x)
data FwdRes n f e x = FwdRes (AGraph n e x) (FwdRewrite n f)
  -- result of a rewrite is a new graph and a (possibly) new rewrite function

analyzeAndRewriteFwd
   :: forall n f. Edges n
   => FwdPass n f
   -> ZBody n -> FactBase f
   -> FuelMonad (ZBody n, FactBase f)

analyzeAndRewriteFwd pass body facts
  = do { (rg, _) <- arfBody pass body facts
       ; return (normaliseBody rg) }

-- | if the graph being analyzed is open at the entry, there must
--   be no other entry point, or all goes horribly wrong...
analyzeAndRewriteFwd'
   :: forall n f e x. Edges n
   => FwdPass n f
   -> ZGraph n e x -> Fact e f
   -> FuelMonad (ZGraph n e x, FactBase f, MaybeO x f)
analyzeAndRewriteFwd' pass g f =
  do (rg, fout) <- arfGraph pass g f
     let (g', fb) = normalizeGraph g rg
     return (g', fb, distinguishedExitFact g' fout)

distinguishedExitFact :: forall n e x f . ZGraph n e x -> Fact x f -> MaybeO x f
distinguishedExitFact g f = maybe g
    where maybe :: ZGraph n e x -> MaybeO x f
          maybe GNil       = JustO f
          maybe (GUnit {}) = JustO f
          maybe (GMany _ _ x) = case x of NothingO -> NothingO
                                          JustO _  -> JustO f

normalizeGraph :: Edges n => ZGraph n e x -> RG n f e x -> GraphWithFacts n f e x
normalizeGraph GNil = normOO
normalizeGraph (GUnit {}) = normOO
normalizeGraph (GMany NothingO  _ NothingO)  = normCC
normalizeGraph (GMany (JustO _) _ NothingO)  = normOC
normalizeGraph (GMany NothingO  _ (JustO _)) = normCO
normalizeGraph (GMany (JustO _) _ (JustO _)) = normOO


----------------------------------------------------------------
--       Forward Implementation
----------------------------------------------------------------


type ARF' n f thing e x
  = FwdPass n f -> thing e x -> Fact e f -> FuelMonad (RG n f e x, Fact x f)

type ARF thing n = forall f e x . ARF' n f thing e x


arfNode :: Edges n
        => (n e x -> ZBlock n e x)
        -> ARF' n f n e x
arfNode bunit pass node f
  = do { mb_g <- withFuel (fp_rewrite pass node f)
       ; case mb_g of
           Nothing -> return (RGUnit f (bunit node),
                              fp_transfer pass node f)
      	   Just (FwdRes ag rw) -> do { g <- graphOfAGraph ag
                                     ; let pass' = pass { fp_rewrite = rw }
                                     ; arfGraph pass' g f } }

-- type demonstration
_arfBlock :: Edges n => ARF' n f (ZBlock n) e x
_arfBlock = arfBlock
_arfGraph :: Edges n => ARF' n f (ZGraph n) e x
_arfGraph = arfGraph


arfMiddle :: Edges n => ARF' n f n O O
arfMiddle = arfNode ZMiddle


arfBlock :: Edges n => ARF (ZBlock n) n
-- Lift from nodes to blocks
arfBlock pass (ZFirst  node)  = arfNode ZFirst  pass node
arfBlock pass (ZMiddle node)  = arfNode ZMiddle pass node
arfBlock pass (ZLast   node)  = arfNode ZLast   pass node
arfBlock pass (ZCat b1 b2)    = arfCat arfBlock  arfBlock  pass b1 b2
arfBlock pass (ZHead h n)     = arfCat arfBlock  arfMiddle pass h n
arfBlock pass (ZTail n t)     = arfCat arfMiddle arfBlock  pass n t
arfBlock pass (ZClosed h t)   = arfCat arfBlock  arfBlock  pass h t

arfCat :: Edges n => ARF' n f thing1 e O -> ARF' n f thing2 O x
       -> FwdPass n f -> thing1 e O -> thing2 O x
       -> Fact e f -> FuelMonad (RG n f e x, Fact x f)
arfCat arf1 arf2 pass thing1 thing2 f = do { (g1,f1) <- arf1 pass thing1 f
                                           ; (g2,f2) <- arf2 pass thing2 f1
                                           ; return (g1 `RGCatO` g2, f2) }
arfBody :: Edges n
                  
        => FwdPass n f -> ZBody n -> FactBase f
        -> FuelMonad (RG n f C C, FactBase f)
		-- Outgoing factbase is restricted to Labels *not* in
		-- in the Body; the facts for Labels *in*
                -- the Body are in the BodyWithFacts
arfBody pass blocks init_fbase
  = fixpoint True (fp_lattice pass) (arfBlock pass) init_fbase $
    forwardBlockList (factBaseLabels init_fbase) blocks

arfGraph :: Edges n => ARF (ZGraph n) n
-- Lift from blocks to graphs
arfGraph _    GNil        f = return (RGNil, f)
arfGraph pass (GUnit blk) f = arfBlock pass blk f
arfGraph pass (GMany NothingO body NothingO) f
  = do { (body', fb) <- arfBody pass body f
       ; return (body', fb) }
arfGraph pass (GMany NothingO body (JustO exit)) f
  = do { (body', fb) <- arfBody  pass body f
       ; (exit', fx) <- arfBlock pass exit fb
       ; return (body' `RGCatC` exit', fx) }
arfGraph pass (GMany (JustO entry) body NothingO) f
  = do { (entry', fe) <- arfBlock pass entry f
       ; (body', fb)  <- arfBody  pass body fe
       ; return (entry' `RGCatC` body', fb) }
arfGraph pass (GMany (JustO entry) body (JustO exit)) f
  = do { (entry', fe) <- arfBlock pass entry f
       ; (body', fb)  <- arfBody  pass body fe
       ; (exit', fx)  <- arfBlock pass exit fb
       ; return (entry' `RGCatC` body' `RGCatC` exit', fx) }

forwardBlockList :: (Edges n, LabelsPtr entry)
                 => entry -> ZBody n -> [ZBlock n C C]
-- This produces a list of blocks in order suitable for forward analysis,
-- along with the list of Labels it may depend on for facts.
forwardBlockList entries blks = postorder_dfs_from (bodyMap blks) entries

-----------------------------------------------------------------------------
--		Backward analysis and rewriting: the interface
-----------------------------------------------------------------------------

data BwdPass n f
  = BwdPass { bp_lattice  :: DataflowLattice f
            , bp_transfer :: BwdTransfer n f
            , bp_rewrite  :: BwdRewrite n f }

type BwdTransfer n f 
  = forall e x. n e x -> Fact x f -> Fact e f 
type BwdRewrite n f 
  = forall e x. n e x -> Fact x f -> Maybe (BwdRes n f e x)
data BwdRes n f e x = BwdRes (AGraph n e x) (BwdRewrite n f)

-----------------------------------------------------------------------------
--		Backward implementation
-----------------------------------------------------------------------------

type ARB' n f thing e x
  = BwdPass n f -> thing e x -> Fact x f -> FuelMonad (RG n f e x, Fact e f)

type ARB thing n = forall f e x. ARB' n f thing e x 

arbNode :: Edges n
        => (n e x -> ZBlock n e x)
        -> ARB' n f n e x
-- Lifts (BwdTransfer,BwdRewrite) to ARB_Node; 
-- this time we do rewriting as well. 
-- The ARB_Graph parameters specifies what to do with the rewritten graph
arbNode bunit pass node f
  = do { mb_g <- withFuel (bp_rewrite pass node f)
       ; case mb_g of
           Nothing -> return (RGUnit entry_f (bunit node), entry_f)
                    where
                      entry_f = bp_transfer pass node f
      	   Just (BwdRes ag rw) -> do { g <- graphOfAGraph ag
                                     ; let pass' = pass { bp_rewrite = rw }
                                     ; arbGraph pass' g f} }

arbMiddle :: Edges n => ARB' n f n O O
arbMiddle = arbNode ZMiddle

arbBlock :: Edges n => ARB (ZBlock n) n
-- Lift from nodes to blocks
arbBlock pass (ZFirst  node)  = arbNode ZFirst  pass node
arbBlock pass (ZMiddle node)  = arbNode ZMiddle pass node
arbBlock pass (ZLast   node)  = arbNode ZLast   pass node
arbBlock pass (ZCat b1 b2)    = arbCat arbBlock  arbBlock  pass b1 b2
arbBlock pass (ZHead h n)     = arbCat arbBlock  arbMiddle pass h n
arbBlock pass (ZTail n t)     = arbCat arbMiddle arbBlock  pass n t
arbBlock pass (ZClosed h t)   = arbCat arbBlock  arbBlock  pass h t

arbCat :: Edges n => ARB' n f thing1 e O -> ARB' n f thing2 O x
       -> BwdPass n f -> thing1 e O -> thing2 O x
       -> Fact x f -> FuelMonad (RG n f e x, Fact e f)
arbCat arb1 arb2 pass thing1 thing2 f = do { (g2,f2) <- arb2 pass thing2 f
                                           ; (g1,f1) <- arb1 pass thing1 f2
                                           ; return (g1 `RGCatO` g2, f1) }

arbBody :: Edges n
        => BwdPass n f -> ZBody n -> FactBase f
        -> FuelMonad (RG n f C C, FactBase f)
arbBody pass blocks init_fbase
  = fixpoint False (bp_lattice pass) (arbBlock pass) init_fbase $
    backwardBlockList blocks 

arbGraph :: Edges n => ARB (ZGraph n) n
arbGraph _    GNil        f = return (RGNil, f)
arbGraph pass (GUnit blk) f = arbBlock pass blk f
arbGraph pass (GMany NothingO body NothingO) f
  = do { (body', fb) <- arbBody pass body f
       ; return (body', fb) }
arbGraph pass (GMany NothingO body (JustO exit)) f
  = do { (exit', fx) <- arbBlock pass exit f
       ; (body', fb) <- arbBody  pass body fx
       ; return (body' `RGCatC` exit', fb) }
arbGraph pass (GMany (JustO entry) body NothingO) f
  = do { (body', fb)  <- arbBody  pass body f
       ; (entry', fe) <- arbBlock pass entry fb
       ; return (entry' `RGCatC` body', fe) }
arbGraph pass (GMany (JustO entry) body (JustO exit)) f
  = do { (exit', fx)  <- arbBlock pass exit f
       ; (body', fb)  <- arbBody  pass body fx
       ; (entry', fe) <- arbBlock pass entry fb
       ; return (entry' `RGCatC` body' `RGCatC` exit', fe) }

backwardBlockList :: Edges n => ZBody n -> [ZBlock n C C]
-- This produces a list of blocks in order suitable for backward analysis,
-- along with the list of Labels it may depend on for facts.
backwardBlockList body = reachable ++ missing
  where reachable = reverse $ forwardBlockList entries body
        entries = externalEntryLabels body
        all = bodyList body
        missingLabels =
            mkLabelSet (map fst all) `minusLabelSet`
            mkLabelSet (map entryLabel reachable)
        missing = map snd $ filter (flip elemLabelSet missingLabels . fst) all

{-

The forward and backward dataflow analyses now use postorder depth-first
order for faster convergence.

The forward and backward cases are not dual.  In the forward case, the
entry points are known, and one simply traverses the body blocks from
those points.  In the backward case, something is known about the exit
points, but this information is essentially useless, because we don't
actually have a dual graph (that is, one with edges reversed) to
compute with.  (Even if we did have a dual graph, it would not avail
us---a backward analysis must include reachable blocks that don't
reach the exit, as in a procedure that loops forever and has side
effects.)

Since in the general case, no information is available about entry
points, I have put in a horrible hack.  First, I assume that every
label defined but not used is an entry point.  Then, because an entry
point might also be a loop header, I add, in arbitrary order, all the
remaining "missing" blocks.  Needless to say, I am not pleased.  
I am not satisfied.  I am not Senator Morgan.

Wait! I believe that the Right Thing here is to require that anyone
wishing to analyze a graph closed at the entry provide a way of
determining the entry points, if any, of that graph.  This requirement
can apply equally to forward and backward analyses; I believe that
using the input FactBase to determine the entry points of a closed
graph is *also* a hack.

NR

-}


analyzeAndRewriteBwd
   :: forall n f. Edges n
   => BwdPass n f 
   -> ZBody n -> FactBase f 
   -> FuelMonad (ZBody n, FactBase f)

analyzeAndRewriteBwd pass body facts
  = do { (rg, _) <- arbBody pass body facts
       ; return (normaliseBody rg) }

-- | if the graph being analyzed is open at the exit, I don't
--   quite understand the implications of possible other exits
analyzeAndRewriteBwd'
   :: forall n f e x. Edges n
   => BwdPass n f
   -> ZGraph n e x -> Fact x f
   -> FuelMonad (ZGraph n e x, FactBase f, MaybeO e f)
analyzeAndRewriteBwd' pass g f =
  do (rg, fout) <- arbGraph pass g f
     let (g', fb) = normalizeGraph g rg
     return (g', fb, distinguishedEntryFact g' fout)

distinguishedEntryFact :: forall n e x f . ZGraph n e x -> Fact e f -> MaybeO e f
distinguishedEntryFact g f = maybe g
    where maybe :: ZGraph n e x -> MaybeO e f
          maybe GNil       = JustO f
          maybe (GUnit {}) = JustO f
          maybe (GMany e _ _) = case e of NothingO -> NothingO
                                          JustO _  -> JustO f

-----------------------------------------------------------------------------
--      fixpoint: finding fixed points
-----------------------------------------------------------------------------

data TxFactBase n f
  = TxFB { tfb_fbase :: FactBase f
         , tfb_rg  :: RG n f C C -- Transformed blocks
         , tfb_cha   :: ChangeFlag
         , tfb_lbls  :: LabelSet }
 -- Note [TxFactBase change flag]
 -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 -- Set the tfb_cha flag iff 
 --   (a) the fact in tfb_fbase for or a block L changes
 --   (b) L is in tfb_lbls.
 -- The tfb_lbls are all Labels of the *original* 
 -- (not transformed) blocks

updateFact :: DataflowLattice f -> LabelSet -> (Label, f)
           -> (ChangeFlag, FactBase f) 
           -> (ChangeFlag, FactBase f)
-- See Note [TxFactBase change flag]
updateFact lat lbls (lbl, new_fact) (cha, fbase)
  | NoChange <- cha2        = (cha,        fbase)
  | lbl `elemLabelSet` lbls = (SomeChange, new_fbase)
  | otherwise               = (cha,        new_fbase)
  where
    (cha2, res_fact) -- Note [Unreachable blocks]
       = case lookupFact fbase lbl of
           Nothing -> (SomeChange, snd $ join $ fact_bot lat)  -- Note [Unreachable blocks]
           Just old_fact -> join old_fact
         where join old_fact = fact_extend lat lbl (OldFact old_fact) (NewFact new_fact)
    new_fbase = extendFactBase fbase lbl res_fact

fixpoint :: forall block n f. Edges (block n)
         => Bool	-- Going forwards?
         -> DataflowLattice f
         -> (block n C C -> FactBase f
              -> FuelMonad (RG n f C C, FactBase f))
         -> FactBase f 
         -> [block n C C]
         -> FuelMonad (RG n f C C, FactBase f)
fixpoint is_fwd lat do_block init_fbase untagged_blocks
  = do { fuel <- getFuel  
       ; tx_fb <- loop fuel init_fbase
       ; return (tfb_rg tx_fb, 
                 tfb_fbase tx_fb `delFromFactBase` map fst blocks) }
	     -- The successors of the ZGraph are the the Labels for which
	     -- we have facts, that are *not* in the blocks of the graph
  where
    blocks = map tag untagged_blocks
     where tag b = ((entryLabel b, b), if is_fwd then [entryLabel b] else successors b)

    tx_blocks :: [((Label, block n C C), [Label])]   -- I do not understand this type
              -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    tx_blocks []              tx_fb = return tx_fb
    tx_blocks (((lbl,blk), deps):bs) tx_fb = tx_block lbl blk deps tx_fb >>= tx_blocks bs
     -- "deps" == Labels the block may _depend_ upon for facts

    tx_block :: Label -> block n C C -> [Label]
             -> TxFactBase n f -> FuelMonad (TxFactBase n f)
    tx_block lbl blk deps tx_fb@(TxFB { tfb_fbase = fbase, tfb_lbls = lbls
                                      , tfb_rg = blks, tfb_cha = cha })
      | is_fwd && not (lbl `elemFactBase` fbase)
      = return tx_fb {tfb_lbls = lbls `unionLabelSet` mkLabelSet deps}	-- Note [Unreachable blocks]
      | otherwise
      = do { (rg, out_facts) <- do_block blk fbase
           ; let (cha',fbase') 
                   = foldr (updateFact lat lbls) (cha,fbase) 
                           (factBaseList out_facts)
                 lbls' = lbls `unionLabelSet` mkLabelSet deps
           ; return (TxFB { tfb_lbls  = lbls'
                          , tfb_rg    = rg `RGCatC` blks
                          , tfb_fbase = fbase', tfb_cha = cha' }) }

    loop :: Fuel -> FactBase f -> FuelMonad (TxFactBase n f)
    loop fuel fbase 
      = do { let init_tx_fb = TxFB { tfb_fbase = fbase
                                   , tfb_cha   = NoChange
                                   , tfb_rg    = RGNil
                                   , tfb_lbls  = emptyLabelSet }
           ; tx_fb <- tx_blocks blocks init_tx_fb
           ; case tfb_cha tx_fb of
               NoChange   -> return tx_fb
               SomeChange -> do { setFuel fuel
                                ; loop fuel (tfb_fbase tx_fb) } }

{- Note [Unreachable blocks]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A block that is not in the domain of tfb_fbase is "currently unreachable".
A currently-unreachable block is not even analyzed.  Reason: consider 
constant prop and this graph, with entry point L1:
  L1: x:=3; goto L4
  L2: x:=4; goto L4
  L4: if x>3 goto L2 else goto L5
Here L2 is actually unreachable, but if we process it with bottom input fact,
we'll propagate (x=4) to L4, and nuke the otherwise-good rewriting of L4.

* If a currently-unreachable block is not analyzed, then its rewritten
  graph will not be accumulated in tfb_rg.  And that is good:
  unreachable blocks simply do not appear in the output.

* Note that clients must be careful to provide a fact (even if bottom)
  for each entry point. Otherwise useful blocks may be garbage collected.

* Note that updateFact must set the change-flag if a label goes from
  not-in-fbase to in-fbase, even if its fact is bottom.  In effect the
  real fact lattice is
       UNR
       bottom
       the points above bottom

* Even if the fact is going from UNR to bottom, we still call the
  client's fact_extend function because it might give the client
  some useful debugging information.

* All of this only applies for *forward* fixpoints.  For the backward
  case we must treat every block as reachable; it might finish with a
  'return', and therefore have no successors, for example.
-}

-----------------------------------------------------------------------------
--	RG: an internal data type for graphs under construction
--          TOTALLY internal to Hoopl
-----------------------------------------------------------------------------

-- this type exists because we have not yet found a way to write arfNode
-- to return a Graph; the invariants of ZGraph seem too strong

data RG' block n f e x where
  RGNil   :: RG' block n f a a
  RGUnit  :: Fact e f -> block n e x -> RG' block n f e x
  RGCatO  :: RG' block n f e O -> RG' block n f O x -> RG' block n f e x
  RGCatC  :: RG' block n f e C -> RG' block n f C x -> RG' block n f e x
type RG = RG' ZBlock

type BodyWithFacts  n f     = (ZBody n, FactBase f)
type GraphWithFacts n f e x = (ZGraph n e x, FactBase f)
  -- A ZGraph together with the facts for that graph
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
normOC (RGUnit _ b)   = (GMany (JustO b) BodyEmpty NothingO, noFacts)
normOC (RGCatO g1 g2) = normOO g1 `gwfCat` normOC g2
normOC (RGCatC g1 g2) = normOC g1 `gwfCat` normCC g2

normCO :: Edges n => RG n f C O -> GraphWithFacts n f C O
normCO (RGUnit f b) = (GMany NothingO BodyEmpty (JustO b), unitFact l f)
                    where
                      l = entryLabel b
normCO (RGCatO g1 g2) = normCO g1 `gwfCat` normOO g2
normCO (RGCatC g1 g2) = normCC g1 `gwfCat` normCO g2

normCC :: Edges n => RG n f C C -> GraphWithFacts n f C C
normCC RGNil        = (GMany NothingO BodyEmpty NothingO, noFacts)
normCC (RGUnit f b) = (GMany NothingO (BodyUnit b) NothingO, unitFact l f)
                    where
                      l = entryLabel b
normCC (RGCatO g1 g2) = normCO g1 `gwfCat` normOC g2
normCC (RGCatC g1 g2) = normCC g1 `gwfCat` normCC g2

gwfCat :: Edges n => GraphWithFacts n f e a
                  -> GraphWithFacts n f a x 
                  -> GraphWithFacts n f e x
gwfCat (g1, fb1) (g2, fb2) = (g1 `U.zSplice` g2, fb1 `unionFactBase` fb2)

{-
bwfUnion :: BodyWithFacts n f -> BodyWithFacts n f -> BodyWithFacts n f
bwfUnion (bg1, fb1) (bg2, fb2) = (bg1 `BodyCat` bg2, fb1 `unionFactBase` fb2)
-}
