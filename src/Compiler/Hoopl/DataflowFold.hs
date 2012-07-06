{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif

{- Notes about the genesis of Hoopl7
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Hoopl7 has the following major chages

a) GMany has symmetric entry and exit
b) GMany closed-entry does not record a BlockId
c) GMany open-exit does not record a BlockId
d) The body of a GMany is called Body
e) A Body is just a list of blocks, not a map. I've argued
   elsewhere that this is consistent with (c)

A consequence is that Graph is no longer an instance of NonLocal,
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
  both need (NonLocal n), and that goes everywhere.

* I renamed BlockId to Label
-}

module Compiler.Hoopl.DataflowFold
  ( DataflowLattice(..), JoinFun, OldFact(..), NewFact(..), Fact
  , ChangeFlag(..), changeIf
  , FwdPass(..), FwdTransfer, mkFTransfer, mkFTransfer', getFTransfers
  , FwdRes(..),  FwdRewrite,  mkFRewrite,  mkFRewrite',  getFRewrites
  , BwdPass(..), BwdTransfer, mkBTransfer, mkBTransfer', getBTransfers
  , BwdRes(..),  BwdRewrite,  mkBRewrite,  mkBRewrite',  getBRewrites
  , analyzeAndRewriteFwd,  analyzeAndRewriteBwd
  )
where

import Data.Maybe

import Compiler.Hoopl.Fuel
import Compiler.Hoopl.Graph
import Compiler.Hoopl.MkGraph
import Compiler.Hoopl.Label
import Compiler.Hoopl.Util

-----------------------------------------------------------------------------
--		DataflowLattice
-----------------------------------------------------------------------------

data DataflowLattice a = DataflowLattice  
 { fact_name       :: String          -- Documentation
 , fact_bot        :: a               -- Lattice bottom element
 , fact_join       :: JoinFun a       -- Lattice join plus change flag
                                      -- (changes iff result > old fact)
 }
-- ^ A transfer function might want to use the logging flag
-- to control debugging, as in for example, it updates just one element
-- in a big finite map.  We don't want Hoopl to show the whole fact,
-- and only the transfer function knows exactly what changed.

type JoinFun a = Label -> OldFact a -> NewFact a -> (ChangeFlag, a)
  -- the label argument is for debugging purposes only
newtype OldFact a = OldFact a
newtype NewFact a = NewFact a

data ChangeFlag = NoChange | SomeChange deriving (Eq, Ord)
changeIf :: Bool -> ChangeFlag
changeIf changed = if changed then SomeChange else NoChange


-----------------------------------------------------------------------------
--		Analyze and rewrite forward: the interface
-----------------------------------------------------------------------------

data FwdPass n f
  = FwdPass { fp_lattice  :: DataflowLattice f
            , fp_transfer :: FwdTransfer n f
            , fp_rewrite  :: FwdRewrite n f }

newtype FwdTransfer n f 
  = FwdTransfers { getFTransfers ::
                     ( n C O -> f -> f
                     , n O O -> f -> f
                     , n O C -> f -> FactBase f
                     ) }

newtype FwdRewrite n f 
  = FwdRewrites { getFRewrites ::
                    ( n C O -> f -> Maybe (FwdRes n f C O)
                    , n O O -> f -> Maybe (FwdRes n f O O)
                    , n O C -> f -> Maybe (FwdRes n f O C)
                    ) }
data FwdRes n f e x = FwdRes (AGraph n e x) (FwdRewrite n f)
  -- result of a rewrite is a new graph and a (possibly) new rewrite function

mkFTransfer :: (n C O -> f -> f)
            -> (n O O -> f -> f)
            -> (n O C -> f -> FactBase f)
            -> FwdTransfer n f
mkFTransfer f m l = FwdTransfers (f, m, l)

mkFTransfer' :: (forall e x . n e x -> f -> Fact x f) -> FwdTransfer n f
mkFTransfer' f = FwdTransfers (f, f, f)

mkFRewrite :: (n C O -> f -> Maybe (FwdRes n f C O))
           -> (n O O -> f -> Maybe (FwdRes n f O O))
           -> (n O C -> f -> Maybe (FwdRes n f O C))
           -> FwdRewrite n f
mkFRewrite f m l = FwdRewrites (f, m, l)

mkFRewrite' :: (forall e x . n e x -> f -> Maybe (FwdRes n f e x)) -> FwdRewrite n f
mkFRewrite' f = FwdRewrites (f, f, f)


type family   Fact x f :: *
type instance Fact C f = FactBase f
type instance Fact O f = f

-- | if the graph being analyzed is open at the entry, there must
--   be no other entry point, or all goes horribly wrong...
analyzeAndRewriteFwd
   :: forall n f e x entries. (NonLocal n, LabelsPtr entries)
   => FwdPass n f
   -> MaybeC e entries
   -> Graph n e x -> Fact e f
   -> FuelMonad (Graph n e x, FactBase f, MaybeO x f)
analyzeAndRewriteFwd pass entries g f =
  do (rg, fout) <- arfGraph pass (nilBefore g) (fmap targetLabels entries) g f
     let (g', fb) = normalizeGraph rg
     return (g', fb, distinguishedExitFact g' fout)
 where nilBefore (GMany NothingO _ _) = rgnilC
       nilBefore (GMany (JustO _) _ _) = rgnil
       nilBefore GNil = rgnil
       nilBefore (GUnit _) = rgnil
       nilBefore :: Graph n e x -> RG f n e e

distinguishedExitFact :: forall n e x f . Graph n e x -> Fact x f -> MaybeO x f
distinguishedExitFact g f = maybe g
    where maybe :: Graph n e x -> MaybeO x f
          maybe GNil       = JustO f
          maybe (GUnit {}) = JustO f
          maybe (GMany _ _ x) = case x of NothingO -> NothingO
                                          JustO _  -> JustO f

----------------------------------------------------------------
--       Forward Implementation
----------------------------------------------------------------


type FM = FuelMonad

type Entries e = MaybeC e [Label]

type RGPair f n e x = (RG f n e x, Fact x f)


arfGraph :: forall n f e a x .
            (NonLocal n)
         => FwdPass n f
         -> RG f n e a
         -> Entries a -> Graph n a x -> Fact a f -> FM (RG f n e x, Fact x f)
arfGraph pass head entries g f = graph g (head, f)
 where
   graph :: Graph n a x -> RGPair f n e a -> FM (RGPair f n e x)
   block :: forall e a x . Block n a x -> (RG f n e a, f) -> FM (RGPair f n e x)
   node  :: forall e a x . (ShapeLifter a x) 
                        => n a x -> (RG f n e a, f) -> FM (RGPair f n e x)
   body  :: forall e . [Label] -> Body n -> (RGPair f n e C) -> FM (RGPair f n e C) 
                   -- Outgoing factbase is restricted to Labels *not* in
                   -- in the Body; the facts for Labels *in*
                   -- the Body are in the 'RG f n C C'

   cat :: forall e a b x info info' info''.
          ((RG f n e a, info)  -> FuelMonad (RG f n e b, info'))
       -> ((RG f n e b, info') -> FuelMonad (RG f n e x, info''))
       -> ((RG f n e a, info)  -> FuelMonad (RG f n e x, info''))

   cat ft1 ft2 (g, f) = ft1 (g, f) >>= ft2

   graph GNil            = return
   graph (GUnit blk)     = block blk
   graph (GMany e bdy x) = eb e bdy `cat` exit x
    where
     eb   :: MaybeO a (Block n O C) -> Body n -> (RGPair f n e a) -> FM (RGPair f n e C)
     exit :: MaybeO x (Block n C O)           -> (RGPair f n e C) -> FM (RGPair f n e x)
     exit (JustO blk) = arfx block blk
     exit NothingO    = return
     eb entry bdy = c entries entry
      where c :: MaybeC a [Label] -> MaybeO a (Block n O C)
              -> (RGPair f n e a) -> FM (RGPair f n e C)
            c NothingC (JustO entry)   = block entry `cat` body (successors entry) bdy
            c (JustC entries) NothingO = body entries bdy

   -- Lift from nodes to blocks
   block (BFirst  n)  = node n
   block (BMiddle n)  = node n
   block (BLast   n)  = node n
   block (BCat b1 b2) = block b1 `cat` block b2
   block (BSnoc h n)  = block h  `cat` node n
   block (BCons n t)  = node  n  `cat` block t
   block (BClosed h t)= block h  `cat` block t

   node thenode (head, f)
     = do { mb_g <- withFuel (frewrite pass thenode f)
          ; case mb_g of
              Nothing -> return (spliceRgNode head f thenode,
                                 ftransfer pass thenode f)
              Just (FwdRes ag rw) ->
                  do { g <- graphOfAGraph ag
                     ; let pass' = pass { fp_rewrite = rw }
                     ; arfGraph pass' head (entry thenode) g (elift thenode f) } }

   -- | Compose fact transformers and concatenate the resulting
   -- rewritten graphs.
   {-# INLINE cat #-} 

   arfx :: forall thing e x .
           NonLocal thing
        => (thing C x -> (RG f n e C,        f) -> FM (RGPair f n e x))
        -> (thing C x -> (RG f n e C, Fact C f) -> FM (RGPair f n e x))
   arfx arf thing (h, fb) = 
     arf thing (h, fromJust $ lookupFact (joinInFacts lattice fb) $ entryLabel thing)
    where lattice = fp_lattice pass
    -- joinInFacts adds debugging information


                   -- Outgoing factbase is restricted to Labels *not* in
   		    -- in the Body; the facts for Labels *in*
                   -- the Body are in the 'RG f n C C'
   body entries blocks (h, init_fbase)
       = do { (body', fb) <- fix; return (h `rgCat` body', fb) }
     where
       fix = fixpoint True (fp_lattice pass) do_block init_fbase $
             forwardBlockList entries blocks
       do_block b f = do (g, fb) <- block b (rgnilC, lookupF pass (entryLabel b) f)
                         return (g, factBaseList fb)


-- Join all the incoming facts with bottom.
-- We know the results _shouldn't change_, but the transfer
-- functions might, for example, generate some debugging traces.
joinInFacts :: DataflowLattice f -> FactBase f -> FactBase f
joinInFacts (DataflowLattice {fact_bot = bot, fact_join = fj}) fb =
  mkFactBase $ map botJoin $ factBaseList fb
    where botJoin (l, f) = (l, snd $ fj l (OldFact bot) (NewFact f))


forwardBlockList :: (NonLocal n, LabelsPtr entry)
                 => entry -> Body n -> [Block n C C]
-- This produces a list of blocks in order suitable for forward analysis,
-- along with the list of Labels it may depend on for facts.
forwardBlockList entries (Body blks) = postorder_dfs_from blks entries

-----------------------------------------------------------------------------
--		Backward analysis and rewriting: the interface
-----------------------------------------------------------------------------

data BwdPass n f
  = BwdPass { bp_lattice  :: DataflowLattice f
            , bp_transfer :: BwdTransfer n f
            , bp_rewrite  :: BwdRewrite n f }

newtype BwdTransfer n f 
  = BwdTransfers { getBTransfers ::
                     ( n C O -> f          -> f
                     , n O O -> f          -> f
                     , n O C -> FactBase f -> f
                     ) }
newtype BwdRewrite n f 
  = BwdRewrites { getBRewrites ::
                    ( n C O -> f          -> Maybe (BwdRes n f C O)
                    , n O O -> f          -> Maybe (BwdRes n f O O)
                    , n O C -> FactBase f -> Maybe (BwdRes n f O C)
                    ) }
data BwdRes n f e x = BwdRes (AGraph n e x) (BwdRewrite n f)

mkBTransfer :: (n C O -> f -> f) -> (n O O -> f -> f) ->
               (n O C -> FactBase f -> f) -> BwdTransfer n f
mkBTransfer f m l = BwdTransfers (f, m, l)

mkBTransfer' :: (forall e x . n e x -> Fact x f -> f) -> BwdTransfer n f
mkBTransfer' f = BwdTransfers (f, f, f)

mkBRewrite :: (n C O -> f          -> Maybe (BwdRes n f C O))
           -> (n O O -> f          -> Maybe (BwdRes n f O O))
           -> (n O C -> FactBase f -> Maybe (BwdRes n f O C))
           -> BwdRewrite n f
mkBRewrite f m l = BwdRewrites (f, m, l)

mkBRewrite' :: (forall e x . n e x -> Fact x f -> Maybe (BwdRes n f e x)) -> BwdRewrite n f
mkBRewrite' f = BwdRewrites (f, f, f)


-----------------------------------------------------------------------------
--		Backward implementation
-----------------------------------------------------------------------------

type ARB' n f thing e x
  = BwdPass n f -> thing e x -> Fact x f -> FuelMonad (RG f n e x, f)

type ARB thing n = forall f e x. ARB' n f thing e x 

arbNode :: (NonLocal n, ShapeLifter e x) => ARB' n f n e x
-- Lifts (BwdTransfer,BwdRewrite) to ARB_Node; 
-- this time we do rewriting as well. 
-- The ARB_Graph parameters specifies what to do with the rewritten graph
arbNode pass node f
  = do { mb_g <- withFuel (brewrite pass node f)
       ; case mb_g of
           Nothing -> return (rgunit entry_f (unit node), entry_f)
                    where entry_f  = btransfer pass node f
      	   Just (BwdRes ag rw) -> do { g <- graphOfAGraph ag
                                     ; let pass' = pass { bp_rewrite = rw }
                                     ; (g, f) <- arbGraph pass' g f
                                     ; return (g, elower (bp_lattice pass) node f)} }

arbBlock :: NonLocal n => ARB (Block n) n
-- Lift from nodes to blocks
arbBlock pass (BFirst  node)  = arbNode pass node
arbBlock pass (BMiddle node)  = arbNode pass node
arbBlock pass (BLast   node)  = arbNode pass node
arbBlock pass (BCat b1 b2)    = arbCat arbBlock arbBlock pass b1 b2
arbBlock pass (BSnoc h n)     = arbCat arbBlock arbNode  pass h n
arbBlock pass (BCons n t)     = arbCat arbNode  arbBlock pass n t
arbBlock pass (BClosed h t)   = arbCat arbBlock arbBlock pass h t

arbCat :: NonLocal n => ARB' n f thing1 e O -> ARB' n f thing2 O x
       -> BwdPass n f -> thing1 e O -> thing2 O x
       -> Fact x f -> FuelMonad (RG f n e x, f)
arbCat arb1 arb2 pass thing1 thing2 f = do { (g2,f2) <- arb2 pass thing2 f
                                           ; (g1,f1) <- arb1 pass thing1 f2
                                           ; return (g1 `rgCat` g2, f1) }

arbBody :: NonLocal n
        => BwdPass n f -> Body n -> FactBase f
        -> FuelMonad (RG f n C C, FactBase f)
arbBody pass blocks init_fbase
  = fixpoint False (bp_lattice pass) do_block init_fbase $
    backwardBlockList blocks 
  where
    do_block b f = do (g, f) <- arbBlock pass b f
                      return (g, [(entryLabel b, f)])

arbGraph :: NonLocal n
         => BwdPass n f -> Graph n e x -> Fact x f
         -> FuelMonad (RG f n e x, Fact e f)
arbGraph _    GNil        f = return (rgnil, f)
arbGraph pass (GUnit blk) f = arbBlock pass blk f
arbGraph pass (GMany NothingO body NothingO) f
  = do { (body', fb) <- arbBody pass body f
       ; return (body', fb) }
arbGraph pass (GMany NothingO body (JustO exit)) f
  = do { (exit', fx) <- arbBlock pass exit f
       ; (body', fb) <- arbBody  pass body $
                          joinInFacts (bp_lattice pass) $ mkFactBase [(entryLabel exit, fx)]
       ; return (body' `rgCat` exit', fb) }
arbGraph pass (GMany (JustO entry) body NothingO) f
  = do { (body', fb)  <- arbBody  pass body f
       ; (entry', fe) <- arbBlock pass entry fb
       ; return (entry' `rgCat` body', fe) }
arbGraph pass (GMany (JustO entry) body (JustO exit)) f
  = do { (exit', fx)  <- arbBlock pass exit f
       ; (body', fb)  <- arbBody  pass body $
                           joinInFacts (bp_lattice pass) $ mkFactBase [(entryLabel exit, fx)]
       ; (entry', fe) <- arbBlock pass entry fb
       ; return (entry' `rgCat` body' `rgCat` exit', fe) }

backwardBlockList :: NonLocal n => Body n -> [Block n C C]
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


-- | if the graph being analyzed is open at the exit, I don't
--   quite understand the implications of possible other exits
analyzeAndRewriteBwd
   :: forall n f e x. NonLocal n
   => BwdPass n f
   -> Graph n e x -> Fact x f
   -> FuelMonad (Graph n e x, FactBase f, MaybeO e f)
analyzeAndRewriteBwd pass g f =
  do (rg, fout) <- arbGraph pass g f
     let (g', fb) = normalizeGraph rg
     return (g', fb, distinguishedEntryFact g' fout)

distinguishedEntryFact :: forall n e x f . Graph n e x -> Fact e f -> MaybeO e f
distinguishedEntryFact g f = maybe g
    where maybe :: Graph n e x -> MaybeO e f
          maybe GNil       = JustO f
          maybe (GUnit {}) = JustO f
          maybe (GMany e _ _) = case e of NothingO -> NothingO
                                          JustO _  -> JustO f

-----------------------------------------------------------------------------
--      fixpoint: finding fixed points
-----------------------------------------------------------------------------

data TxFactBase n f
  = TxFB { tfb_fbase :: FactBase f
         , tfb_rg  :: RG f n C C -- Transformed blocks
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
         where join old_fact = fact_join lat lbl (OldFact old_fact) (NewFact new_fact)
    new_fbase = extendFactBase fbase lbl res_fact

fixpoint :: forall block n f. (NonLocal n, NonLocal (block n))
         => Bool	-- Going forwards?
         -> DataflowLattice f
         -> (block n C C -> FactBase f
              -> FuelMonad (RG f n C C, [(Label, f)]))
         -> FactBase f 
         -> [block n C C]
         -> FuelMonad (RG f n C C, FactBase f)
fixpoint is_fwd lat do_block init_fbase untagged_blocks
  = do { fuel <- getFuel  
       ; tx_fb <- loop fuel init_fbase
       ; return (tfb_rg tx_fb, 
                 tfb_fbase tx_fb `delFromFactBase` map fst blocks) }
	     -- The successors of the Graph are the the Labels for which
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
                   = foldr (updateFact lat lbls) (cha,fbase) out_facts
                 lbls' = lbls `unionLabelSet` mkLabelSet deps
           ; return (TxFB { tfb_lbls  = lbls'
                          , tfb_rg    = rg `rgCat` blks
                          , tfb_fbase = fbase', tfb_cha = cha' }) }

    loop :: Fuel -> FactBase f -> FuelMonad (TxFactBase n f)
    loop fuel fbase 
      = do { let init_tx_fb = TxFB { tfb_fbase = fbase
                                   , tfb_cha   = NoChange
                                   , tfb_rg    = rgnilC
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
  client's fact_join function because it might give the client
  some useful debugging information.

* All of this only applies for *forward* fixpoints.  For the backward
  case we must treat every block as reachable; it might finish with a
  'return', and therefore have no successors, for example.
-}

-----------------------------------------------------------------------------
--	RG: an internal data type for graphs under construction
--          TOTALLY internal to Hoopl; each block carries its fact
-----------------------------------------------------------------------------

type RG      f n e x = Graph' (FBlock f) n e x
data FBlock f n e x = FBlock f (Block n e x)
instance NonLocal n => NonLocal (FBlock f n) where
  entryLabel (FBlock _ b) = entryLabel b
  successors (FBlock _ b) = successors b

--- constructors

rgnil  :: RG f n O O
rgnilC :: RG f n C C
rgunit :: NonLocal n => f -> Block n e x -> RG f n e x
rgCat  :: NonLocal n => RG f n e a -> RG f n a x -> RG f n e x

---- observers

type GraphWithFacts n f e x = (Graph n e x, FactBase f)
  -- A Graph together with the facts for that graph
  -- The domains of the two maps should be identical

normalizeGraph :: forall n f e x .
                  NonLocal n => RG f n e x -> GraphWithFacts n f e x

normalizeGraph g = (graphMapBlocks dropFact g, facts g)
    where dropFact (FBlock _ b) = b
          facts :: RG f n e x -> FactBase f
          facts GNil = noFacts
          facts (GUnit _) = noFacts
          facts (GMany _ body exit) = bodyFacts body `unionFactBase` exitFacts exit
          exitFacts :: MaybeO x (FBlock f n C O) -> FactBase f
          exitFacts NothingO = noFacts
          exitFacts (JustO (FBlock f b)) = mkFactBase [(entryLabel b, f)]
          bodyFacts :: Body (FBlock f) n -> FactBase f
          bodyFacts body = foldLabelMap f noFacts body
            where f (FBlock f b) fb = extendFactBase fb (entryLabel b) f

--- implementation of the constructors (boring)

rgnil  = GNil
rgnilC = GMany NothingO emptyMap NothingO

rgunit f b@(BFirst  {}) = gUnitCO (FBlock f b)
rgunit f b@(BMiddle {}) = gUnitOO (FBlock f b)
rgunit f b@(BLast   {}) = gUnitOC (FBlock f b)
rgunit f b@(BCat {})    = gUnitOO (FBlock f b)
rgunit f b@(BSnoc {})   = gUnitCO (FBlock f b)
rgunit f b@(BCons {})   = gUnitOC (FBlock f b)
rgunit f b@(BClosed {}) = gUnitCC (FBlock f b)

rgCat = U.splice fzCat
  where fzCat (FBlock f b1) (FBlock _ b2) = FBlock f (b1 `U.cat` b2)

----------------------------------------------------------------
--       Utilities
----------------------------------------------------------------

-- Lifting based on shape:
--  - from nodes to blocks
--  - from facts to fact-like things
-- Lowering back:
--  - from fact-like things to facts
-- Note that the latter two functions depend only on the entry shape.
class ShapeLifter e x where
  unit      :: n e x -> Block n e x
  elift     :: NonLocal n =>                      n e x -> f -> Fact e f
  elower    :: NonLocal n => DataflowLattice f -> n e x -> Fact e f -> f
  ftransfer :: FwdPass n f -> n e x -> f        -> Fact x f
  btransfer :: BwdPass n f -> n e x -> Fact x f -> f
  frewrite  :: FwdPass n f -> n e x -> f        -> Maybe (FwdRes n f e x)
  brewrite  :: BwdPass n f -> n e x -> Fact x f -> Maybe (BwdRes n f e x)
  spliceRgNode :: NonLocal n => RG f n a e -> f -> n e x -> RG f n a x
  entry     :: NonLocal n => n e x -> Entries e

instance ShapeLifter C O where
  unit            = BFirst
  elift      n f  = mkFactBase [(entryLabel n, f)]
  elower lat n fb = getFact lat (entryLabel n) fb
  ftransfer (FwdPass {fp_transfer = FwdTransfers (ft, _, _)}) n f = ft n f
  btransfer (BwdPass {bp_transfer = BwdTransfers (bt, _, _)}) n f = bt n f
  frewrite  (FwdPass {fp_rewrite  = FwdRewrites  (fr, _, _)}) n f = fr n f
  brewrite  (BwdPass {bp_rewrite  = BwdRewrites  (br, _, _)}) n f = br n f
  spliceRgNode (GMany e body NothingO) f n = GMany e body x
     where x = JustO $ FBlock f $ BFirst n
  entry n = JustC [entryLabel n]

instance ShapeLifter O O where
  unit         = BMiddle
  elift    _ f = f
  elower _ _ f = f
  ftransfer (FwdPass {fp_transfer = FwdTransfers (_, ft, _)}) n f = ft n f
  btransfer (BwdPass {bp_transfer = BwdTransfers (_, bt, _)}) n f = bt n f
  frewrite  (FwdPass {fp_rewrite  = FwdRewrites  (_, fr, _)}) n f = fr n f
  brewrite  (BwdPass {bp_rewrite  = BwdRewrites  (_, br, _)}) n f = br n f
  spliceRgNode (GMany e body (JustO (FBlock f x))) _ n = GMany e body (JustO x')
     where x' = FBlock f $ BSnoc x n
  spliceRgNode (GNil) f n = GUnit $ FBlock f $ BMiddle n
  spliceRgNode (GUnit (FBlock f b)) _ n = GUnit $ FBlock f $ b `BCat` BMiddle n
  entry _ = NothingC

instance ShapeLifter O C where
  unit         = BLast
  elift    _ f = f
  elower _ _ f = f
  ftransfer (FwdPass {fp_transfer = FwdTransfers (_, _, ft)}) n f = ft n f
  btransfer (BwdPass {bp_transfer = BwdTransfers (_, _, bt)}) n f = bt n f
  frewrite  (FwdPass {fp_rewrite  = FwdRewrites  (_, _, fr)}) n f = fr n f
  brewrite  (BwdPass {bp_rewrite  = BwdRewrites  (_, _, br)}) n f = br n f
  spliceRgNode (GMany e b1 (JustO (FBlock f x))) _ n = GMany e body' NothingO
     where body' = unionLabelMap b1 b2
           b2 = addBlock (FBlock f $ BClosed x $ BLast n) emptyMap
  spliceRgNode (GNil) f n = GMany e emptyMap NothingO
     where e = JustO $ FBlock f $ BLast n
  spliceRgNode (GUnit (FBlock f b)) _ n = GMany e emptyMap NothingO
     where e = JustO $ FBlock f (b `U.cat` BLast n)
  entry _ = NothingC

-- Fact lookup: the fact `orelse` bottom
lookupF :: FwdPass n f -> Label -> FactBase f -> f
lookupF = getFact . fp_lattice

getFact  :: DataflowLattice f -> Label -> FactBase f -> f
getFact lat l fb = case lookupFact fb l of Just  f -> f
                                           Nothing -> fact_bot lat
