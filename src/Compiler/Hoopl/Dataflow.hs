{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, MultiParamTypeClasses #-}

module Compiler.Hoopl.Dataflow
  ( DataflowLattice(..), JoinFun, OldFact(..), NewFact(..), Fact
  , ChangeFlag(..), changeIf
  , FwdPass(..), FwdTransfer, mkFTransfer, mkFTransfer3, getFTransfer3
  , FwdRew(..),  FwdRewrite,  mkFRewrite,  mkFRewrite3,  getFRewrite3
  , BwdPass(..), BwdTransfer, mkBTransfer, mkBTransfer3, getBTransfer3
  , BwdRew(..),  BwdRewrite,  mkBRewrite,  mkBRewrite3,  getBRewrite3
  , analyzeAndRewriteFwd,  analyzeAndRewriteBwd
  )
where

import Data.Maybe

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Fuel
import Compiler.Hoopl.Graph hiding (Graph) -- hiding so we can redefine
                                           -- and include definition in paper
import qualified Compiler.Hoopl.GraphUtil as U
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

data FwdPass m n f
  = FwdPass { fp_lattice  :: DataflowLattice f
            , fp_transfer :: FwdTransfer n f
            , fp_rewrite  :: FwdRewrite m n f }

newtype FwdTransfer n f 
  = FwdTransfer3 { getFTransfer3 ::
                     ( n C O -> f -> f
                     , n O O -> f -> f
                     , n O C -> f -> FactBase f
                     ) }

newtype FwdRewrite m n f 
  = FwdRewrite3 { getFRewrite3 ::
                    ( n C O -> f -> m (Maybe (FwdRew m n f C O))
                    , n O O -> f -> m (Maybe (FwdRew m n f O O))
                    , n O C -> f -> m (Maybe (FwdRew m n f O C))
                    ) }
data FwdRew m n f e x = FwdRew (Graph n e x) (FwdRewrite m n f)

  -- result of a rewrite is a new graph and a (possibly) new rewrite function

mkFTransfer3 :: (n C O -> f -> f)
             -> (n O O -> f -> f)
             -> (n O C -> f -> FactBase f)
             -> FwdTransfer n f
mkFTransfer3 f m l = FwdTransfer3 (f, m, l)

mkFTransfer :: (forall e x . n e x -> f -> Fact x f) -> FwdTransfer n f
mkFTransfer f = FwdTransfer3 (f, f, f)

mkFRewrite3 :: (n C O -> f -> m (Maybe (FwdRew m n f C O)))
            -> (n O O -> f -> m (Maybe (FwdRew m n f O O)))
            -> (n O C -> f -> m (Maybe (FwdRew m n f O C)))
            -> FwdRewrite m n f
mkFRewrite3 f m l = FwdRewrite3 (f, m, l)

mkFRewrite :: (forall e x . n e x -> f -> m (Maybe (FwdRew m n f e x)))
           -> FwdRewrite m n f
mkFRewrite f = FwdRewrite3 (f, f, f)


type family   Fact x f :: *
type instance Fact C f = FactBase f
type instance Fact O f = f

-- | if the graph being analyzed is open at the entry, there must
--   be no other entry point, or all goes horribly wrong...
analyzeAndRewriteFwd
   :: forall m n f e x entries. (FuelMonad m, NonLocal n, LabelsPtr entries)
   => FwdPass m n f
   -> MaybeC e entries
   -> Graph n e x -> Fact e f
   -> m (Graph n e x, FactBase f, MaybeO x f)
analyzeAndRewriteFwd pass entries g f =
  do (rg, fout) <- arfGraph pass (fmap targetLabels entries) g f
     let (g', fb) = normalizeGraph rg
     return (g', fb, distinguishedExitFact g' fout)

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

type Entries e = MaybeC e [Label]

arfGraph :: forall m n f e x .
            (NonLocal n, FuelMonad m) => FwdPass m n f -> 
            Entries e -> Graph n e x -> Fact e f -> m (DG f n e x, Fact x f)
arfGraph pass entries = graph
  where
    {- nested type synonyms would be so lovely here 
    type ARF  thing = forall e x . thing e x -> f        -> m (DG f n e x, Fact x f)
    type ARFX thing = forall e x . thing e x -> Fact e f -> m (DG f n e x, Fact x f)
    -}
    graph ::              Graph n e x -> Fact e f -> m (DG f n e x, Fact x f)
    block :: forall e x . Block n e x -> f        -> m (DG f n e x, Fact x f)
    node  :: forall e x . (ShapeLifter e x) 
                       => n e x       -> f        -> m (DG f n e x, Fact x f)
-- @ start bodyfun.tex
    body  :: [Label] -> LabelMap (Block n C C)
          -> Fact C f -> m (DG f n C C, Fact C f)
-- @ end bodyfun.tex
                    -- Outgoing factbase is restricted to Labels *not* in
                    -- in the Body; the facts for Labels *in*
                    -- the Body are in the 'DG f n C C'
    cat :: forall m e a x info info' info''. Monad m =>
           (info  -> m (DG f n e a, info'))
        -> (info' -> m (DG f n a x, info''))
        -> (info  -> m (DG f n e x, info''))

    graph GNil            = \f -> return (dgnil, f)
    graph (GUnit blk)     = block blk
    graph (GMany e bdy x) = (e `ebcat` bdy) `cat` exit x
     where
      ebcat :: MaybeO e (Block n O C) -> Body n -> Fact e f -> m (DG f n e C, Fact C f)
      exit  :: MaybeO x (Block n C O)           -> Fact C f -> m (DG f n C x, Fact x f)
      exit (JustO blk) = arfx block blk
      exit NothingO    = \fb -> return (dgnilC, fb)
      ebcat entry bdy = c entries entry
       where c :: MaybeC e [Label] -> MaybeO e (Block n O C)
                -> Fact e f -> m (DG f n e C, Fact C f)
             c NothingC (JustO entry)   = block entry `cat` body (successors entry) bdy
             c (JustC entries) NothingO = body entries bdy
             c _ _ = error "bogus GADT pattern match failure"

    -- Lift from nodes to blocks
    block (BFirst  n)  = node n
    block (BMiddle n)  = node n
    block (BLast   n)  = node n
    block (BCat b1 b2) = block b1 `cat` block b2
    block (BHead h n)  = block h  `cat` node n
    block (BTail n t)  = node  n  `cat` block t
    block (BClosed h t)= block h  `cat` block t

    node n f
      = do { fwdres <- frewrite pass n f >>= withFuel
           ; case fwdres of
               Nothing -> return (toDg f (toBlock n),
                                  ftransfer pass n f)
               Just (FwdRew g rw) ->
                   let pass' = pass { fp_rewrite = rw }
                   in  arfGraph pass' (maybeEntry n) g (fwdEntryFact n f) }

    -- | Compose fact transformers and concatenate the resulting
    -- rewritten graphs.
    {-# INLINE cat #-} 
    cat ft1 ft2 f = do { (g1,f1) <- ft1 f
                       ; (g2,f2) <- ft2 f1
                       ; return (g1 `dgCat` g2, f2) }

    arfx :: forall thing x .
            NonLocal thing
         => (thing C x ->        f -> m (DG f n C x, Fact x f))
         -> (thing C x -> Fact C f -> m (DG f n C x, Fact x f))
    arfx arf thing fb = 
      arf thing $ fromJust $ lookupFact (entryLabel thing) $ joinInFacts lattice fb
     where lattice = fp_lattice pass
     -- joinInFacts adds debugging information


                    -- Outgoing factbase is restricted to Labels *not* in
    		    -- in the Body; the facts for Labels *in*
                    -- the Body are in the 'DG f n C C'
-- @ start bodyfun.tex
    body entries blockmap init_fbase
      = fixpoint Fwd lattice do_block blocks init_fbase
      where
        blocks  = forwardBlockList entries blockmap
        lattice = fp_lattice pass
        do_block b fb = block b entryFact
          where entryFact = getFact lattice (entryLabel b) fb
-- @ end bodyfun.tex


-- Join all the incoming facts with bottom.
-- We know the results _shouldn't change_, but the transfer
-- functions might, for example, generate some debugging traces.
joinInFacts :: DataflowLattice f -> FactBase f -> FactBase f
joinInFacts (DataflowLattice {fact_bot = bot, fact_join = fj}) fb =
  mkFactBase $ map botJoin $ mapToList fb
    where botJoin (l, f) = (l, snd $ fj l (OldFact bot) (NewFact f))

forwardBlockList :: (NonLocal n, LabelsPtr entry)
                 => entry -> Body n -> [Block n C C]
-- This produces a list of blocks in order suitable for forward analysis,
-- along with the list of Labels it may depend on for facts.
forwardBlockList entries blks = postorder_dfs_from blks entries

-----------------------------------------------------------------------------
--		Backward analysis and rewriting: the interface
-----------------------------------------------------------------------------

data BwdPass m n f
  = BwdPass { bp_lattice  :: DataflowLattice f
            , bp_transfer :: BwdTransfer n f
            , bp_rewrite  :: BwdRewrite m n f }

newtype BwdTransfer n f 
  = BwdTransfer3 { getBTransfer3 ::
                     ( n C O -> f          -> f
                     , n O O -> f          -> f
                     , n O C -> FactBase f -> f
                     ) }
newtype BwdRewrite m n f 
  = BwdRewrite3 { getBRewrite3 ::
                    ( n C O -> f          -> m (Maybe (BwdRew m n f C O))
                    , n O O -> f          -> m (Maybe (BwdRew m n f O O))
                    , n O C -> FactBase f -> m (Maybe (BwdRew m n f O C))
                    ) }
data BwdRew m n f e x = BwdRew (Graph n e x) (BwdRewrite m n f)


mkBTransfer3 :: (n C O -> f -> f) -> (n O O -> f -> f) ->
                (n O C -> FactBase f -> f) -> BwdTransfer n f
mkBTransfer3 f m l = BwdTransfer3 (f, m, l)

mkBTransfer :: (forall e x . n e x -> Fact x f -> f) -> BwdTransfer n f
mkBTransfer f = BwdTransfer3 (f, f, f)

mkBRewrite3 :: (n C O -> f          -> m (Maybe (BwdRew m n f C O)))
            -> (n O O -> f          -> m (Maybe (BwdRew m n f O O)))
            -> (n O C -> FactBase f -> m (Maybe (BwdRew m n f O C)))
            -> BwdRewrite m n f
mkBRewrite3 f m l = BwdRewrite3 (f, m, l)

mkBRewrite :: (forall e x . n e x -> Fact x f -> m (Maybe (BwdRew m n f e x)))
           -> BwdRewrite m n f
mkBRewrite f = BwdRewrite3 (f, f, f)


-----------------------------------------------------------------------------
--		Backward implementation
-----------------------------------------------------------------------------

arbGraph :: forall m n f e x .
            (NonLocal n, FuelMonad m) => BwdPass m n f -> 
            Entries e -> Graph n e x -> Fact x f -> m (DG f n e x, Fact e f)
arbGraph pass entries = graph
  where
    {- nested type synonyms would be so lovely here 
    type ARB  thing = forall e x . thing e x -> Fact x f -> m (DG f n e x, f)
    type ARBX thing = forall e x . thing e x -> Fact x f -> m (DG f n e x, Fact e f)
    -}
    graph ::              Graph n e x -> Fact x f -> m (DG f n e x, Fact e f)
    block :: forall e x . Block n e x -> Fact x f -> m (DG f n e x, f)
    node  :: forall e x . (ShapeLifter e x) 
                       => n e x       -> Fact x f -> m (DG f n e x, f)
    body  :: [Label] -> Body n -> Fact C f -> m (DG f n C C, Fact C f)
    cat :: forall e a x info info' info''.
           (info' -> m (DG f n e a, info''))
        -> (info  -> m (DG f n a x, info'))
        -> (info  -> m (DG f n e x, info''))

    graph GNil            = \f -> return (dgnil, f)
    graph (GUnit blk)     = block blk
    graph (GMany e bdy x) = (e `ebcat` bdy) `cat` exit x
     where
      ebcat :: MaybeO e (Block n O C) -> Body n -> Fact C f -> m (DG f n e C, Fact e f)
      exit  :: MaybeO x (Block n C O)           -> Fact x f -> m (DG f n C x, Fact C f)
      exit (JustO blk) = arbx block blk
      exit NothingO    = \fb -> return (dgnilC, fb)
      ebcat entry bdy = c entries entry
       where c :: MaybeC e [Label] -> MaybeO e (Block n O C)
                -> Fact C f -> m (DG f n e C, Fact e f)
             c NothingC (JustO entry)   = block entry `cat` body (successors entry) bdy
             c (JustC entries) NothingO = body entries bdy
             c _ _ = error "bogus GADT pattern match failure"

    -- Lift from nodes to blocks
    block (BFirst  n)  = node n
    block (BMiddle n)  = node n
    block (BLast   n)  = node n
    block (BCat b1 b2) = block b1 `cat` block b2
    block (BHead h n)  = block h  `cat` node n
    block (BTail n t)  = node  n  `cat` block t
    block (BClosed h t)= block h  `cat` block t

    node n f
      = do { bwdres <- brewrite pass n f >>= withFuel
           ; case bwdres of
               Nothing -> return (toDg entry_f (toBlock n), entry_f)
                            where entry_f = btransfer pass n f
               Just (BwdRew g rw) ->
                          do { let pass' = pass { bp_rewrite = rw }
                             ; (g, f) <- arbGraph pass' (maybeEntry n) g f
                             ; return (g, bwdEntryFact (bp_lattice pass) n f)} }

    -- | Compose fact transformers and concatenate the resulting
    -- rewritten graphs.
    {-# INLINE cat #-} 
    cat ft1 ft2 f = do { (g2,f2) <- ft2 f
                       ; (g1,f1) <- ft1 f2
                       ; return (g1 `dgCat` g2, f1) }

    arbx :: forall thing x .
            NonLocal thing
         => (thing C x -> Fact x f -> m (DG f n C x, f))
         -> (thing C x -> Fact x f -> m (DG f n C x, Fact C f))

    arbx arb thing f = do { (rg, f) <- arb thing f
                          ; let fb = joinInFacts (bp_lattice pass) $
                                     mapSingleton (entryLabel thing) f
                          ; return (rg, fb) }
     -- joinInFacts adds debugging information

                    -- Outgoing factbase is restricted to Labels *not* in
    		    -- in the Body; the facts for Labels *in*
                    -- the Body are in the 'DG f n C C'
    body entries blockmap init_fbase
      = fixpoint Bwd (bp_lattice pass) do_block blocks init_fbase
      where
        blocks = backwardBlockList entries blockmap
        do_block b f = do (g, f) <- block b f
                          return (g, mapSingleton (entryLabel b) f)


backwardBlockList :: (LabelsPtr entries, NonLocal n) => entries -> Body n -> [Block n C C]
-- This produces a list of blocks in order suitable for backward analysis,
-- along with the list of Labels it may depend on for facts.
backwardBlockList entries body = reverse $ forwardBlockList entries body

{-

The forward and backward cases are not dual.  In the forward case, the
entry points are known, and one simply traverses the body blocks from
those points.  In the backward case, something is known about the exit
points, but this information is essentially useless, because we don't
actually have a dual graph (that is, one with edges reversed) to
compute with.  (Even if we did have a dual graph, it would not avail
us---a backward analysis must include reachable blocks that don't
reach the exit, as in a procedure that loops forever and has side
effects.)

-}


-- | if the graph being analyzed is open at the exit, I don't
--   quite understand the implications of possible other exits
analyzeAndRewriteBwd
   :: (FuelMonad m, NonLocal n, LabelsPtr entries)
   => BwdPass m n f
   -> MaybeC e entries -> Graph n e x -> Fact x f
   -> m (Graph n e x, FactBase f, MaybeO e f)
analyzeAndRewriteBwd pass entries g f =
  do (rg, fout) <- arbGraph pass (fmap targetLabels entries) g f
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
         , tfb_rg    :: DG f n C C -- Transformed blocks
         , tfb_cha   :: ChangeFlag
         , tfb_lbls  :: LabelSet }
     -- See Note [TxFactBase invariants]

updateFact :: DataflowLattice f -> LabelSet
           -> Label -> f -> (ChangeFlag, FactBase f)
           -> (ChangeFlag, FactBase f)
-- See Note [TxFactBase change flag]
updateFact lat lbls lbl new_fact (cha, fbase)
  | NoChange <- cha2     = (cha,        fbase)
  | lbl `setMember` lbls = (SomeChange, new_fbase)
  | otherwise            = (cha,        new_fbase)
  where
    (cha2, res_fact) -- Note [Unreachable blocks]
       = case lookupFact lbl fbase of
           Nothing -> (SomeChange, new_fact_debug)  -- Note [Unreachable blocks]
           Just old_fact -> join old_fact
         where join old_fact = 
                 fact_join lat lbl
                   (OldFact old_fact) (NewFact new_fact)
               (_, new_fact_debug) = join (fact_bot lat)
    new_fbase = mapInsert lbl res_fact fbase

{-  this type is too general for the paper :-( 
fixpoint :: forall m block n f. 
            (FuelMonad m, NonLocal n, NonLocal (block n))
         => Direction
         -> DataflowLattice f
         -> (block n C C -> FactBase f
             -> m (DG f n C C, [(Label, f)]))
         -> [block n C C]
         -> FactBase f 
         -> m (DG f n C C, FactBase f)
-}
-- @ start fptype.tex
data Direction = Fwd | Bwd
fixpoint :: forall m n f. (FuelMonad m, NonLocal n)
 => Direction
 -> DataflowLattice f
 -> (Block n C C -> Fact C f -> m (DG f n C C, Fact C f))
 -> [Block n C C]
 -> (Fact C f -> m (DG f n C C, Fact C f))
-- @ end fptype.tex
fixpoint direction lat do_block blocks init_fbase
  = do { fuel <- getFuel  
       ; tx_fb <- loop fuel init_fbase
       ; return (tfb_rg tx_fb, 
                 map (fst . fst) tagged_blocks 
                    `mapDeleteList` tfb_fbase tx_fb ) }
	     -- The successors of the Graph are the the Labels for which
	     -- we have facts, that are *not* in the blocks of the graph
  where
    tagged_blocks = map tag blocks
    is_fwd = case direction of { Fwd -> True; 
                                 Bwd -> False }
    tag b = ((entryLabel b, b), 
             if is_fwd then [entryLabel b] 
                        else successors b)
     -- 'tag' adds the in-labels of the block; 
     -- see Note [TxFactBase invairants]

    tx_blocks :: [((Label, Block n C C), [Label])]   -- I do not understand this type
              -> TxFactBase n f -> m (TxFactBase n f)
    tx_blocks []              tx_fb = return tx_fb
    tx_blocks (((lbl,blk), in_lbls):bs) tx_fb 
      = tx_block lbl blk in_lbls tx_fb >>= tx_blocks bs
     -- "in_lbls" == Labels the block may 
     --                 _depend_ upon for facts

    tx_block :: Label -> Block n C C -> [Label]
             -> TxFactBase n f -> m (TxFactBase n f)
    tx_block lbl blk in_lbls 
        tx_fb@(TxFB { tfb_fbase = fbase, tfb_lbls = lbls
                    , tfb_rg = blks, tfb_cha = cha })
      | is_fwd && not (lbl `mapMember` fbase)
      = return (tx_fb {tfb_lbls = lbls'})	-- Note [Unreachable blocks]
      | otherwise
      = do { (rg, out_facts) <- do_block blk fbase
           ; let (cha',fbase') 
                   = mapFoldWithKey (updateFact lat lbls) 
                          (cha,fbase) out_facts
           ; return (TxFB { tfb_lbls  = lbls'
                          , tfb_rg    = rg `dgCat` blks
                          , tfb_fbase = fbase'
                          , tfb_cha = cha' }) }
      where
        lbls' = lbls `setUnion` setFromList in_lbls
        

    loop :: Fuel -> FactBase f -> m (TxFactBase n f)
    loop fuel fbase 
      = do { let init_tx = TxFB { tfb_fbase = fbase
                                , tfb_cha   = NoChange
                                , tfb_rg    = dgnilC
                                , tfb_lbls  = setEmpty }
           ; tx_fb <- tx_blocks tagged_blocks init_tx
           ; case tfb_cha tx_fb of
               NoChange   -> return tx_fb
               SomeChange 
                 -> do { setFuel fuel
                       ; loop fuel (tfb_fbase tx_fb) } }

{-  Note [TxFactBase invariants]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The TxFactBase is used only during a fixpoint iteration (or "sweep"),
and accumulates facts (and the transformed code) during the fixpoint
iteration.

* tfb_fbase increases monotonically, across all sweeps

* At the beginning of each sweep
      tfb_cha  = NoChange
      tfb_lbls = {}

* During each sweep we process each block in turn.  Processing a block
  is done thus:
    1.  Read from tfb_fbase the facts for its entry label (forward)
        or successors labels (backward)
    2.  Transform those facts into new facts for its successors (forward)
        or entry label (backward)
    3.  Augment tfb_fbase with that info
  We call the labels read in step (1) the "in-labels" of the sweep

* The field tfb_lbls is the set of in-labels of all blocks that have
  been processed so far this sweep, including the block that is
  currently being processed.  tfb_lbls is initialised to {}.  It is a
  subset of the Labels of the *original* (not transformed) blocks.

* The tfb_cha field is set to SomeChange iff we decide we need to
  perform another iteration of the fixpoint loop. It is initialsed to NoChange.

  Specifically, we set tfb_cha to SomeChange in step (3) iff
    (a) The fact in tfb_fbase for a block L changes
    (b) L is in tfb_lbls
  Reason: until a label enters the in-labels its accumuated fact in tfb_fbase
  has not been read, hence cannot affect the outcome

Note [Unreachable blocks]
~~~~~~~~~~~~~~~~~~~~~~~~~
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
--	DG: an internal data type for 'decorated graphs'
--          TOTALLY internal to Hoopl; each block is decorated with a fact
-----------------------------------------------------------------------------

-- @ start dg.tex
type Graph = Graph' Block
type DG     f n e x = Graph'   (DBlock f) n e x
data DBlock f n e x = DBlock f (Block n e x) -- ^ block decorated with fact
toDg :: NonLocal n => f -> Block n e x -> DG f n e x
-- @ end dg.tex
instance NonLocal n => NonLocal (DBlock f n) where
  entryLabel (DBlock _ b) = entryLabel b
  successors (DBlock _ b) = successors b

--- constructors

dgnil  :: DG f n O O
dgnilC :: DG f n C C
dgCat  :: NonLocal n => DG f n e a -> DG f n a x -> DG f n e x

---- observers

type GraphWithFacts n f e x = (Graph n e x, FactBase f)
  -- A Graph together with the facts for that graph
  -- The domains of the two maps should be identical

normalizeGraph :: forall n f e x .
                  NonLocal n => DG f n e x -> GraphWithFacts n f e x

normalizeGraph g = (graphMapBlocks dropFact g, facts g)
    where dropFact (DBlock _ b) = b
          facts :: DG f n e x -> FactBase f
          facts GNil = noFacts
          facts (GUnit _) = noFacts
          facts (GMany _ body exit) = bodyFacts body `mapUnion` exitFacts exit
          exitFacts :: MaybeO x (DBlock f n C O) -> FactBase f
          exitFacts NothingO = noFacts
          exitFacts (JustO (DBlock f b)) = mapSingleton (entryLabel b) f
          bodyFacts :: LabelMap (DBlock f n C C) -> FactBase f
          bodyFacts body = mapFold f noFacts body
            where f (DBlock f b) fb = mapInsert (entryLabel b) f fb

--- implementation of the constructors (boring)

dgnil  = GNil
dgnilC = GMany NothingO emptyBody NothingO

toDg f b@(BFirst  {}) = gUnitCO (DBlock f b)
toDg f b@(BMiddle {}) = gUnitOO (DBlock f b)
toDg f b@(BLast   {}) = gUnitOC (DBlock f b)
toDg f b@(BCat {})    = gUnitOO (DBlock f b)
toDg f b@(BHead {})   = gUnitCO (DBlock f b)
toDg f b@(BTail {})   = gUnitOC (DBlock f b)
toDg f b@(BClosed {}) = gUnitCC (DBlock f b)

dgCat = U.splice fzCat
  where fzCat (DBlock f b1) (DBlock _ b2) = DBlock f (b1 `U.cat` b2)

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
  toBlock      :: n e x -> Block n e x
  fwdEntryFact :: NonLocal n =>                      n e x -> f -> Fact e f
  bwdEntryFact :: NonLocal n => DataflowLattice f -> n e x -> Fact e f -> f
  ftransfer    :: FwdPass m n f -> n e x -> f        -> Fact x f
  btransfer    :: BwdPass m n f -> n e x -> Fact x f -> f
  frewrite     :: FwdPass m n f -> n e x -> f        -> m (Maybe (FwdRew m n f e x))
  brewrite     :: BwdPass m n f -> n e x -> Fact x f -> m (Maybe (BwdRew m n f e x))
  maybeEntry   :: NonLocal n => n e x -> Entries e

instance ShapeLifter C O where
  toBlock         = BFirst
  fwdEntryFact     n f  = mkFactBase [(entryLabel n, f)]
  bwdEntryFact lat n fb = getFact lat (entryLabel n) fb
  ftransfer (FwdPass {fp_transfer = FwdTransfer3 (ft, _, _)}) n f = ft n f
  btransfer (BwdPass {bp_transfer = BwdTransfer3 (bt, _, _)}) n f = bt n f
  frewrite  (FwdPass {fp_rewrite  = FwdRewrite3  (fr, _, _)}) n f = fr n f
  brewrite  (BwdPass {bp_rewrite  = BwdRewrite3  (br, _, _)}) n f = br n f
  maybeEntry n = JustC [entryLabel n]

instance ShapeLifter O O where
  toBlock      = BMiddle
  fwdEntryFact   _ f = f
  bwdEntryFact _ _ f = f
  ftransfer (FwdPass {fp_transfer = FwdTransfer3 (_, ft, _)}) n f = ft n f
  btransfer (BwdPass {bp_transfer = BwdTransfer3 (_, bt, _)}) n f = bt n f
  frewrite  (FwdPass {fp_rewrite  = FwdRewrite3  (_, fr, _)}) n f = fr n f
  brewrite  (BwdPass {bp_rewrite  = BwdRewrite3  (_, br, _)}) n f = br n f
  maybeEntry _ = NothingC

instance ShapeLifter O C where
  toBlock      = BLast
  fwdEntryFact   _ f = f
  bwdEntryFact _ _ f = f
  ftransfer (FwdPass {fp_transfer = FwdTransfer3 (_, _, ft)}) n f = ft n f
  btransfer (BwdPass {bp_transfer = BwdTransfer3 (_, _, bt)}) n f = bt n f
  frewrite  (FwdPass {fp_rewrite  = FwdRewrite3  (_, _, fr)}) n f = fr n f
  brewrite  (BwdPass {bp_rewrite  = BwdRewrite3  (_, _, br)}) n f = br n f
  maybeEntry _ = NothingC

-- Fact lookup: the fact `orelse` bottom
getFact  :: DataflowLattice f -> Label -> FactBase f -> f
getFact lat l fb = case lookupFact l fb of Just  f -> f
                                           Nothing -> fact_bot lat
