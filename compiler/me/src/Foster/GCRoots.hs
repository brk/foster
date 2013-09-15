{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns, RankNTypes,
             ScopedTypeVariables, NoMonoLocalBinds #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.GCRoots(insertSmartGCRoots, fnty_of_procty) where

import Compiler.Hoopl

import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.Boxes as Boxes

import Foster.Base(TExpr, TypedId(TypedId), freeTypedIds, Ident, Occurrence,
                   tidType, tidIdent, typeOf, MayGC(GCUnknown), boolGC)
import Foster.CFG(runWithUniqAndFuel, M, rebuildGraphM)
import Foster.Config
import Foster.CloConv
import Foster.TypeLL
import Foster.Letable
import Foster.Avails

import Debug.Trace(trace)

import Data.Maybe(fromMaybe)
import Data.Map(Map)
import qualified Data.Set as Set
import qualified Data.Map as Map(lookup, empty, elems, findWithDefault, insert,
           keys, assocs, delete, fromList, keysSet)
import qualified Data.Text as T(pack)
import Control.Monad(when, liftM)
import Control.Monad.State(evalStateT, get, put, modify, StateT, lift, gets)

-- | Explicit insertion (and optimization) of GC roots.

-- Assumption: allocation has already been made explicit,
--             and we're being called as part of ILExpr.hs's
--             pre-codegen preparations.

showOptResults = False
gDoReuseRootSlots = True

--------------------------------------------------------------------

-- Every potentially-GCing operation could invalidate
-- every value stored in the root slots, so we must insert reloads
-- from slots between GC points and uses. The simplest strategy
-- is to insert reloads immediately after each GC point. But consider
-- the following example::
--      (gcpoint; if ... then () else f ss)
-- If we reload after the GC point, we'll reload ss even if the
-- conditional ends up being false and ss isn't needed. Thus,
-- we prefer to reload immediately before each use, unless a prior
-- reload is available that hasn't been invalidated by a gc point.
--
-- In addition to inserting reloads, we also want to generate memory
-- lifetime markers, which will help LLVM generate better code for
-- inlined functions. The most straightforward way of doing so would
-- be to run a liveness analysis and transformation that inserts
-- liveness markers after loads. Unfortunately that has two problems:
---First, it would require a backwards analysis combined with a
-- forward rewrite, which Hoopl does not support. To avoid this problem,
-- we'll first place "disabled" markers in a forward pass, then remove/enable
-- them in a separate backwards, liveness-based pass. Second, placing markers
-- after loads alone is insufficient to achieve precise GC root placement.
-- In particular, consider a CFG like this::
--
--      E: [gen a,b ; condbr T S]    << note: a, b both live here
--      T: [                         << note: b dead here!
--           use a  ;
--           br F]
--      S: [use b   ;     br F]
--      F: [ret]
--
-- If we only insert kills after uses, we will fail to kill b on the T path,
-- likewise a on the S path.
--
-- So we take a nine-stage (!!!) approach to inserting roots, detailed below.
--
-- An alternate design would annotate BB headers & terminators with their
-- live/dead sets, and then propagate that information forward, using the
-- differences to guide placement of GC root kills at BB headers. The main
-- reason we don't is that doing so would involve extending the definition of
-- BasicBlockGraph' and/or ILExpr, which would be a hassle.

type GCRootsForVariables = Map LLVar RootVar
type VariablesForGCRoots = Map RootVar LLVar

-- Precondition: allocations have been made explicit in the input graph.
-- Precondition: may-gc analysis has updated the annotations in the graph.
insertSmartGCRoots :: BasicBlockGraph' -> Map Ident MayGC -> Bool -> Compiled ( BasicBlockGraph' , [RootVar] )
insertSmartGCRoots bbgp0 mayGCmap dump = do
  --   1) Run a rewriting (non-dataflow) pass to insert root initializers
  --      at first uses, and insert disabled kill markers after each use.
  bbgp'1 <- insertDumbGCRoots bbgp0 dump

  --   2) Fold to compute the (root, initializing variable) relation/mapping.
  let gcr = computeGCRootsForVars bbgp'1

  --   3) Run a backwards liveness pass to compute:
  --        * What the set of live roots are, when a GC might occur.
  --      This pass also enables kills (after trimming out live roots).
  (bbgp'2 , rootsLiveAtGCPoints) <- runLiveAtGCPoint2 bbgp'1 mayGCmap

  --   4) Run a rewriting pass to remove actions referencing dead roots.
  bbgp'3  <- removeDeadGCRoots bbgp'2 (mapInverse gcr) rootsLiveAtGCPoints

  --   5) Run a rewriting (non-dataflow) pass to insert root kills for *every*
  --      root at *every* basic block.
  bbgp'4 <- insertDumbGCKills bbgp'3 dump (Map.elems gcr)

  --   6) Run a forwards pass to trim redundant kills.
  --      If we are configured to reuse root slots,
  --      this is where we do it.
  bbgp'5a <- runAvails bbgp'4 rootsLiveAtGCPoints mayGCmap gDoReuseRootSlots

  -- runAvails might have reused a root slot in a forwards pass, which might
  -- have invalidated liveness information (backwards pass). So we'll re-run the
  -- backwards pass, and finish with runAvails configured not to reuse slots.
  (bbgp'5b , rootsLiveAtGCPoints'5b) <- runLiveAtGCPoint2 bbgp'5a mayGCmap
  bbgp'5c  <- removeDeadGCRoots bbgp'5b (mapInverse gcr) rootsLiveAtGCPoints'5b
  bbgp'5d <- runAvails bbgp'5c rootsLiveAtGCPoints'5b mayGCmap False

  lift $ when (showOptResults || dump) $ do
              putStrLn "difference from runAvails:"
              Boxes.printBox $ catboxes2 (bbgpBody bbgp'4) (bbgpBody bbgp'5d )

  let bbgp_final = bbgp'5d
  return ( bbgp_final , computeUsedRoots bbgp_final )
  -- We need to return the set of live roots so LLVM codegen can create them
  -- in advance.
 where
    mapInverse m = let ks = Map.keysSet m in
                   let es = Set.fromList (Map.elems m) in
                   let swap (a,b) = (b,a) in
                   if Set.size ks == Set.size es
                     then Map.fromList (map swap $ Map.assocs m)
                     else error $ "mapInverse can't reverse a non-one-to-one map!"
                               ++ "\nkeys: " ++ show ks ++ "\nelems:" ++ show es

    computeUsedRoots bbgp = Set.toList . Set.fromList $
                             Map.elems (computeGCRootsForVars bbgp)

    computeGCRootsForVars bbgp = foldGraphNodes go (bbgpBody bbgp) Map.empty
      where
        go :: Insn' e x -> GCRootsForVariables -> GCRootsForVariables
        go (CCGCInit _ v root) s = -- assert v not in s
                                   Map.insert v root s
        -- don't recurse into functions: we don't want their roots!
        go _                   s = s

instance TExpr Closure TypeLL where freeTypedIds _ = []

-- A moving garbage collector can copy a pointer. Because LLVM does
-- not automatically spill GCable pointers to the stack (because it
-- doesn't distinguish different types of pointers in the backends)
-- the front-end is responsible for setting up and emitting reloads
-- from GC root stack slots.
--
-- Our rule for selective insertion of GC roots is based on liveness:
-- we assign a GC root for any GCable pointer whose live range
-- includes a potential GC point.

-- |||||||||||||||||||| Figure out which variables need roots |||{{{
type LiveGCRoots    = Set.Set LLVar
type RootLiveWhenGC = Set.Set LLVar
type ContinuationMayGC = Bool
type LiveAGC2 = (LiveGCRoots, RootLiveWhenGC, ContinuationMayGC)

-- When we see a load from a root, the root becomes live;
-- when we see a root init happen, the root becomes dead.
-- When we see an operation that may induce (copying) GC,
-- we'll add the current set of live roots to the set of
-- roots we keep.
liveAtGCPointXfer2 :: Map Ident MayGC -> BwdTransfer Insn' LiveAGC2
liveAtGCPointXfer2 mayGCmap = mkBTransfer go
  where
    go :: Insn' e x -> Fact x LiveAGC2 -> LiveAGC2
    go (CCLabel   {}        ) f = ifgc False            f
    go (CCGCLoad _v fromroot) f = markLive fromroot     f
    go (CCGCInit _ _v toroot) f = markDead   toroot     f
    go (CCGCKill {}         ) f = {- just ignore it  -} f
    go (CCLetVal  _ letable ) f = ifgc (boolGC maygc)   f where maygc = canGC mayGCmap letable
    go (CCLetFuns _ids _clos) f = ifgc True             f
    go (CCTupleStore   {}   ) f = ifgc False            f
    go (CCRebindId     {}   ) f = ifgc False            f
    go node@(CCLast    cclast) fdb =
          let f = combineLastFacts fdb node in
          ifgc (canCCLastGC mayGCmap cclast) f

    markLive root (s, g, c) = (Set.insert root s, g, c)
    markDead root (s, g, c) = (Set.delete root s, g, c)

    ifgc mayGC (s, g, c) = if mayGC then (s, g `Set.union` s, True)
                                    else (s, g              , c)

-- If we see a (disabled) GCKill marker when a root is still alive,
-- we'll remove the marker, but if the root is dead, we'll enable
-- the marker, since it is, by definition, (conservatively) correct.
-- Eliminating redundant kills is a job for a separate (forward) pass.
liveAtGCPointRewrite2 :: forall m. FuelMonad m => BwdRewrite m Insn' LiveAGC2
liveAtGCPointRewrite2 = mkBRewrite d
  where
    d :: Insn' e x -> Fact x LiveAGC2 -> m (Maybe (Graph Insn' e x))
    d (CCLabel      {}       )   _    = return Nothing
    d (CCLetVal     {}       )   _    = return Nothing
    d (CCLetFuns    {}       )   _    = return Nothing
    d (CCTupleStore {}       )   _    = return Nothing
    d (CCRebindId   {}       )   _    = return Nothing
    d (CCGCLoad     {}       )   _    = return Nothing
    d (CCGCInit     {}       )   _    = return Nothing
    d (CCGCKill (Enabled _) _)   _    = return Nothing -- leave as-is.
    d (CCGCKill Disabled    roots) (liveRoots,_,cgc) =
          return $ Just (mkMiddle (CCGCKill (Enabled cgc) deadRoots))
                   where deadRoots = Set.difference roots liveRoots
    d (CCLast {}              ) _fdb  = return Nothing

runLiveAtGCPoint2 :: BasicBlockGraph' -> Map Ident MayGC ->
                               Compiled (BasicBlockGraph' , RootLiveWhenGC)
runLiveAtGCPoint2 bbgp mayGCmap
                       = do uref <- gets ccUniqRef
                            lift $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M (BasicBlockGraph' ,RootLiveWhenGC)
    go bbgp = do
        let ((_,blab), _) = bbgpEntry bbgp
        (body' , fdb, _) <- analyzeAndRewriteBwd bwd (JustC [bbgpEntry bbgp])
                                                             (bbgpBody bbgp)
                         (mapSingleton blab (fact_bot liveAtGCPointLattice2))
        let (_, liveRoots, _) = fromMaybe (error "runLiveAtGCPoint failed") $
                                                             lookupFact blab fdb
        return (bbgp { bbgpBody = body' } , liveRoots)

    bwd = BwdPass { bp_lattice  = liveAtGCPointLattice2
                  , bp_transfer = liveAtGCPointXfer2 mayGCmap
                  , bp_rewrite  = liveAtGCPointRewrite2
                  }

liveAtGCPointLattice2 :: DataflowLattice LiveAGC2
liveAtGCPointLattice2 = DataflowLattice
  { fact_name = "Live GC roots"
  , fact_bot  = (Set.empty, Set.empty, False)
  , fact_join = add
  }
    where add _lab (OldFact (ol,og,oc)) (NewFact (nl,ng,nc)) = (ch, (jl, jg,jc))
            where
              jl = nl `Set.union` ol
              jg = ng `Set.union` og
              jc = nc     ||      oc
              ch = changeIf (Set.size jl > Set.size ol
                          || Set.size jg > Set.size og)

combineLastFacts :: FactBase LiveAGC2 -> Insn' O C -> LiveAGC2
combineLastFacts fdb node = union3s (map (fact fdb) (successors node))
  where
    union3s xycs = let (xs,ys,cs) = unzip3 xycs
                   in  (Set.unions xs, Set.unions ys, or cs)

    fact :: FactBase LiveAGC2 -> Label -> LiveAGC2
    fact f l = fromMaybe (fact_bot liveAtGCPointLattice2) $ lookupFact l f
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

makeSubstWith :: Ord a => [a] -> [a] -> (a -> a)
makeSubstWith from to = let m = Map.fromList $ zip from to in
                        let s v = Map.findWithDefault v v m in
                        s

catboxes2 bbg1 bbg2 = Boxes.hsep 1 Boxes.left $
                            [(boxify . measure . plain . pretty) bbg1
                            ,(boxify . measure .         pretty) bbg2]

measure :: Doc -> Boxes.Box
measure d = Boxes.vcat Boxes.left (map Boxes.text $ lines $ show d)

boxify :: Boxes.Box -> Boxes.Box
boxify b = v Boxes.<> (h Boxes.// b Boxes.// h) Boxes.<> v
             where v = Boxes.vcat Boxes.left (take (Boxes.rows b + 2) (repeat (Boxes.char '|')))
                   h = Boxes.text $          (take (Boxes.cols b    ) (repeat '-'))

-- Generate a GC root for each GCable variable in the body, and
-- en masse, rewrite each use of a GCable variable to generate and
-- use a load from the variable's associated root. Each use of a loaded variable
-- will also be followed by a kill marker, to ensure that we get the tightest
-- live range possible for the gc roots.
--
-- In a later flow-driven pass, we'll figure out which roots are really needed,
-- and remove redundant loads (TODO),
-- unneeded roots, and incorrectly-placed kill marks.
insertDumbGCRoots :: BasicBlockGraph' -> Bool -> Compiled BasicBlockGraph'
insertDumbGCRoots bbgp0 dump = do
   -- If we have        REPLACE o WITH v
   --                   CASE o OF ...
   -- we don't want to try to find a root for o!
   -- So we enforce the invariant that no active rebindings exist here.
   -- Running runRebinds will leave the rebinding nodes themselves,
   -- but they will be dead and we can safely ignore them.
   bbgp <- runRebinds bbgp0
   g'  <- evalStateT (rebuildGraphM (case bbgpEntry bbgp of (bid, _) -> bid)
                                    (bbgpBody bbgp) transform)
                             Map.empty

   lift $ when (showOptResults || dump) $ do Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'

   return bbgp { bbgpBody =  g' }

 where

  transform :: forall e x. Insn' e x -> RootMapped (Graph Insn' e x)
  transform insn = case insn of
    -- See the note above explaining why we generate all these GCKills...
    CCLabel (_bid, vs)            -> do inits <- mapM maybeRootInitializer vs
                                        return (mkFirst insn <*> catGraphs inits {- <*> mkMiddle
                                           (CCGCKill Disabled (Set.fromList $ Map.elems gcr' ) -} )
    CCGCLoad  {}                  -> do return $ mkMiddle $ insn
    CCGCInit  {}                  -> do return $ mkMiddle $ insn
    CCGCKill  {}                  -> do return $ mkMiddle $ insn
    CCTupleStore vs v r           -> do {- trace ("isGCable " ++ show v ++ " :" ++ show (isGCable v)) $ -}
                                         withGCLoads (v:vs) (\(v' : vs' ) ->
                                          mkMiddle $ CCTupleStore vs' v' r)
    CCLetVal id val               -> do ri <- maybeRootInitializer (TypedId (typeOf val) id)
                                        let vs = freeTypedIds val
                                        withGCLoads vs (\vs' ->
                                         let s = makeSubstWith vs vs' in
                                         (mkMiddle $ CCLetVal id (substVarsInLetable s val)) <*> ri)
    CCLetFuns [id] [clo]          -> do
                                        let concrete_fnty = fnty_of_procty (tidType (closureProcVar clo))
                                        ri <- maybeRootInitializer (TypedId concrete_fnty id)
                                        let vs = [closureEnvVar clo]
                                        withGCLoads vs (\vs' ->
                                          let s = makeSubstWith vs vs' in
                                          (mkMiddle $ CCLetFuns [id] [substVarsInClo s clo]) <*> ri)
    CCLetFuns ids _clos           -> do error $ "CCLetFuns should all become singletons!" ++ show ids
    CCRebindId _doc _v1 _v2       -> do return $ mkMiddle $ insn
    CCLast (CCCont b vs)          -> do withGCLoads vs (\vs'  ->
                                               (mkLast $ CCLast (CCCont b vs' )))
    CCLast (CCCall b t id v vs)  -> do withGCLoads (v:vs) (\(v' : vs' ) ->
                                               (mkLast $ CCLast (CCCall b t id v' vs' )))
    CCLast (CCCase v arms mb)    -> do withGCLoads [v] (\[v' ] ->
                                               (mkLast $ CCLast (CCCase v' arms mb)))

  fresh str = lift $ ccFreshId (T.pack str)

  substVarsInClo s (Closure proc env capts asrc) =
        Closure proc (s env) (map s capts) asrc

  maybeRootInitializer :: LLVar -> RootMapped (Graph Insn' O O)
  maybeRootInitializer v = do
    if not $ isGCable v
      then return emptyGraph
      else do junkid <- fresh (show (tidIdent v) ++ ".junk")
              let junk = TypedId (LLPtrType (LLStructType [])) junkid
              rootid <- fresh (show (tidIdent v) ++ ".root")
              let root = TypedId (tidType v) rootid
              modify (Map.insert v root)
              return $ --trace ("maybeRootInitializer: adding gcinit for root " ++ show (tidIdent root)) $
                       mkMiddle $ CCGCInit junk v root

  -- A helper function to assist in rewriting instructions to use loads from
  -- GC roots for variables which are subject to garbage collection.
  withGCLoads :: [LLVar] -> ([LLVar] -> Graph Insn' O x) -> RootMapped (Graph Insn' O x)
  withGCLoads vs mkG = do
    loadsAndVars <- mapM withGCLoad vs
    let (loads, vs' ) = unzip loadsAndVars
    return $ mkMiddles (concat loads) <*> mkG vs'
   where
      -- We'll rewrite something like ``call @foo (x,n)`` (where ``x`` is
      -- GCable and ``n`` isn't) with::
      --      x.load = load x.root
      --      kill x.root (disabled)
      ---     call @foo (x.load , n)
      -- We'll removed kills for live roots and enable the remainder.
      -- We'll insert root initializations in a separate pass.
      retLoaded root = do
          id <- fresh (show (tidIdent root) ++ ".load")
          let loadedvar = TypedId (tidType root) id
          return ([CCGCLoad loadedvar root
                  ,CCGCKill Disabled (Set.fromList [root])]
                 , loadedvar)

      withGCLoad_t :: LLVar -> RootMapped ([Insn' O O], LLVar)
      withGCLoad_t v = do rv <- withGCLoad (trace ("withGCLoad " ++ show v) v)
                          return $ trace ("withGCLoad " ++ show v ++ " ==> " ++ show (pretty rv)) rv

      withGCLoad :: LLVar -> RootMapped ([Insn' O O], LLVar)
      withGCLoad v = if not $ isGCable v then return ([], v)
       else do gcr <- get
               case Map.lookup v gcr of
                 Just root -> do retLoaded root
                 Nothing   -> do
                                 rootid <- fresh (show (tidIdent v) ++ ".ROOT")
                                 let root = TypedId (tidType v) rootid
                                 put (Map.insert v root gcr)
                                 retLoaded root

-- There's one unusual subtlety here: in addition to generating (disabled)
-- kill markers after each load from a root, we also generate markers at the
-- start of each basic block. The reason is due to code like this::
--      (... ; if use x then compute-without-x else reuse x end)
--
-- This will get translated to
--      ...                                    ...
--      x.load = gcload from x.root            x.load = gcload from x.root
--      tmp = call use x.load                  tmp = call use x.load
--      kill x.root (disabled)                 // removed; x.root is live!
--      cond tmp Lthen Lelse                   cond tmp Lthen Lelse
--    Lthen:                                 Lthen:
--      tmp3 = call compute-without-x ()       tmp3 = call compute-without-x ()
--      ret tmp3                               ret tmp3
--    Lelse:                                 Lelse:
--      x.load2 = gcload from x.root           x.load2 = gcload from x.root
--      kill x.root (disabled)                 kill x.root (enabled) // x.root dead
--      tmp2 = call reuse x.load2              tmp2 = call reuse x.load2
--      ret tmp2                               ret tmp2
--
-- The problem is that, in order to be safe-for-space, x.root should be
-- deallocatable while we're running compute-without-x, but as translated
-- above, we never kill the root slot!
--
-- So we must insert kills for dead root slots at the start of basic blocks.
insertDumbGCKills :: BasicBlockGraph' -> Bool -> [RootVar] -> Compiled BasicBlockGraph'
insertDumbGCKills bbgp dump allroots = do
   g'  <- rebuildGraphM (case bbgpEntry bbgp of (bid, _) -> bid)
                                    (bbgpBody bbgp) transform
   lift $ when (showOptResults || dump) $ do Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'
   return bbgp { bbgpBody =  g' }
 where
  transform :: forall e x. Insn' e x -> Compiled (Graph Insn' e x)
  transform insn = case insn of
    CCLabel       _ -> return $ mkFirst insn
                            <*> mkMiddle (CCGCKill Disabled (Set.fromList allroots))
    CCLast       {} -> return $ mkMiddle (CCGCKill Disabled (Set.fromList allroots))
                            <*> mkLast insn
    CCGCInit     {} -> return $ mkMiddle insn
    CCGCLoad     {} -> return $ mkMiddle insn
    CCGCKill     {} -> return $ mkMiddle insn
    CCLetVal     {} -> return $ mkMiddle insn
    CCTupleStore {} -> return $ mkMiddle insn
    CCLetFuns    {} -> return $ mkMiddle insn
    CCRebindId   {} -> return $ mkMiddle insn

type RootMapped = StateT GCRootsForVariables Compiled

-- Now we know the set of GC roots which are (and, implicitly, are not)
-- live when GC can occur. If a root is not live, we'll remove all the
-- loads, inits, and kills associated with it. We'll also replace uses
-- of gcloads with the corresponding variables. For example, we'll replace::
--    gc.root := x
--    x.load = gcload x.root
--    call foo (x.load)
-- with::
--    call foo (x)
removeDeadGCRoots :: BasicBlockGraph'
                  -> VariablesForGCRoots
                  -> RootLiveWhenGC
                  -> Compiled BasicBlockGraph'
removeDeadGCRoots bbgp varsForGCRoots liveRoots = do
   let mappedAction = rebuildGraphM (case bbgpEntry bbgp of (bid, _) -> bid)
                                    (bbgpBody bbgp) transform
   g' <- evalStateT mappedAction Map.empty

   lift $ when showOptResults $ Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'

   return bbgp { bbgpBody =  g' }
 where
  isLive root = Set.member root liveRoots
  iflive root g = if isLive root then return g else return emptyGraph

  transform :: forall e x. Insn' e x -> RootMapped (Graph Insn' e x)
  transform insn = case insn of
    CCLabel {}                    -> do return $ mkFirst $ insn
    CCGCLoad  v     root          -> do m <- get
                                        put (Map.insert v root m)
                                        iflive root $ mkMiddle $ insn
    CCGCInit  _ _   root          -> do iflive root $ mkMiddle $ insn
    CCGCKill  Disabled    _root   -> do error "transform saw disabled gckill?"
    CCGCKill  enabled     roots   -> do return $ mkMiddle (CCGCKill enabled (Set.intersection roots liveRoots))
    CCTupleStore vs v r           -> do undoDeadGCLoads (v:vs) (\(v' : vs' ) ->
                                         mkMiddle $ CCTupleStore vs' v' r)
    CCLetVal id val               -> do let vs = freeTypedIds val
                                        undoDeadGCLoads vs (\vs' ->
                                         let s = makeSubstWith vs vs' in
                                         mkMiddle $ CCLetVal id (substVarsInLetable s val))
    CCLetFuns {}                  -> do return $ mkMiddle $ insn
    CCLast (CCCont b vs)          -> do undoDeadGCLoads vs (\vs'  ->
                                               (mkLast $ CCLast (CCCont b vs' )))
    CCLast (CCCall b t id v vs)   -> do undoDeadGCLoads (v:vs) (\(v' : vs' ) ->
                                               (mkLast $ CCLast (CCCall b t id v' vs' )))
    CCLast (CCCase v arms mb)     -> do undoDeadGCLoads [v] (\[v' ] ->
                                               (mkLast $ CCLast (CCCase v' arms mb)))
    CCRebindId     {}             -> do return $ mkMiddle $ insn

  varForRoot_t root = let rv = varForRoot (trace ("varForRoot " ++ show root) root) in
                      trace ("varForRoot " ++ show root ++ " ==> " ++ show (pretty rv)) rv

  varForRoot root = case Map.lookup root varsForGCRoots of
                       Nothing -> error $ "GCRoots.hs: Unable to find source variable for root "
                                        ++ show root ++ "\nmap keys are "
                                        ++ show (pretty $ map tidIdent $ Map.keys varsForGCRoots)
                       Just var -> var

  undoDeadGCLoads vs k = liftM k (mapM undo vs)

  undo v = do gcRootsForVars <- get
              return $ case Map.lookup v gcRootsForVars of
                           Nothing   -> v
                           Just root -> if isLive root
                                          then v
                                          else varForRoot root

fnty_of_procty pt@(LLProcType (env:_args) _rets _cc) =
      LLPtrType (LLStructType [pt, env])
fnty_of_procty other = error $ "GCRoots.hs: fnty_of_procty undefined for " ++ show other

-- Filter out non-pointer-typed variables from live set.
isGCable v = case tidType v of
               LLPrimInt _            -> False
               LLPrimFloat64          -> False
               LLStructType _         -> False
               LLProcType _ _ _       -> False
               LLPtrType _            -> True -- could have further annotations on ptr types
               LLTyConApp   {}        -> True
               LLCoroType _ _         -> True
               LLArrayType _          -> True
               LLPtrTypeUnknown       -> True

-- |||||||||||||||||||| Redundancy elimination ||||||||||||||||||{{{

-- We want to track which roots have been killed, so that when we see
-- a kill of an already-killed (on all paths) root, we can drop the redundant
-- kill. The straightforward thing to do is to directly track a set of killed
-- roots, which starts out empty (for bottom), and grows when we xfer
-- past a kill. Because we want an all-paths  property, join is intersection:
-- a root is only killed if it is killed on all incoming paths.
--
-- The problem is that doing so does not form a valid lattice: as defined,
-- we would have ``_|_ \/ e = _|_`` by definition of bottom=empty-set and
-- join=intersection. What we instead need is ``_|_ \/ e = e`` (to be a
-- proper lattice).
-- Rather than tracking *killed* roots, we track *unkilled* roots, which thus
-- allows us to form a proper lattice that tracks what roots don't need kills.
-- Then the bottom element is all variables, and  we shrink when we xfer past
-- a kill.
--
-- Things are a bit trickier still for eliminating redundant reloads. We want
-- to track the set of available bindings corresponding to each (unkilled) root.
-- Since availability is an all-paths property, we need to use set intersection
-- as our join, which in turn implies that the bottom element must be
-- (UniverseMinus empty). But, unusually, this is *not* the element we want to
-- assign for our entry node! Rather, we need to use (Avail empty), i.e. top.
-- Consider this graph:
--      entry:
--              x.load  = load from x.root
--              do something with x.load
--      other:
--              x.load2 = load from x.root
--              jmp entry
-- When jmp'ing back to entry, x.load2 is available to replace a load from root.
-- If the beginning fact is (UniverseMinus empty), then we'll try to replace
-- x.load with x.load2---bad! Using top instead of bottom at the start fact
-- for the set of loaded roots prevents this from occurring.
--
--
-- (note: this pass runs after removeDeadGCRoots.)

eraseLoads roots (AvailMap a m) =
                 (AvailMap a (Set.fold Map.delete m roots))

type UnkilledRoots    = AvailSet LLRootVar
type InitializedRoots = AvailSet LLRootVar
data Avails = Avails { unkilledRoots :: UnkilledRoots
                     , rootLoads     :: AvailMap LLRootVar LLVar
                     , initedRoots   :: InitializedRoots
                     , availSubst    :: AvailMap LLRootVar LLVar
                     , availOccs     :: AvailMap (LLVar, Occurrence TypeLL) LLVar
                     }  -- note: AvailMap works here because LLVar == LLRootVar...
                     deriving Show

--instance Show Avails where show a = show (pretty a)
--instance Pretty Avails where
--  pretty (Avails uk lr fr) = text "(Avails unkilledRoots=" <> text (show uk)
--                         <+> text "loadedRoots="   <> text (show uk)
--                         <+> text "loadsForRoots=" <> text (show $ Map.map (Set.map tidIdent) fr) <> text ")"

availsXfer :: Map Ident MayGC -> FwdTransfer Insn' Avails
availsXfer mayGCmap = mkFTransfer3 go go (distributeXfer availsLattice go)
  where
    go :: Insn' e x -> Avails -> Avails
    go (CCLabel      {}    ) f = f
    go (CCGCLoad   var root) f = makeLoadAvail var root f
    go (CCGCInit _ _   root) f =        f `unkill` root
    go (CCGCKill (Enabled _) roots) f = f `killin` roots
    go (CCGCKill     {}    ) f = f
    go (CCLetVal id letable) f = ifgc (boolGC maygc)  xf where maygc = canGC mayGCmap letable
                                                               xf = considerLet f id letable
    go (CCLetFuns    {}    ) f = ifgc True             f
    go (CCTupleStore {}    ) f = f
    go (CCRebindId _ v1 v2 ) f = f { availSubst = insertAvailMap v1 v2 (availSubst f) }
    go (CCLast       cclast) f = ifgc (canCCLastGC mayGCmap cclast) f

    ifgc mayGC f = if mayGC then f { rootLoads = emptyAvailMap }
                            else f -- when a GC might occur, all root loads
                                   -- become invalidated...

    makeLoadAvail var root f = f { rootLoads = insertAvailMap root var (rootLoads f) }

    -- Killing a root implies removing it from the unkilled set, and vice versa.
    killin f roots = f { rootLoads     = eraseLoads roots (rootLoads f)
                       , unkilledRoots = unkilledRoots f `delAvails` roots
                       }
    unkill f root  = f { unkilledRoots = unkilledRoots f `addAvail`  root
                       , initedRoots   = initedRoots f   `addAvail`  root }

    considerLet avails id (ILOccurrence ty v occ) = avails { availOccs = insertAvailMap (v, occ) (TypedId ty id) (availOccs avails) }
    considerLet avails _ _ = avails

availsRewrite :: forall m. FuelMonad m => RootLiveWhenGC -> Bool -> FwdRewrite m Insn' Avails
availsRewrite allRoots doReuseRootSlots = mkFRewrite d
  where
    d :: Insn' e x -> Avails -> m (Maybe (Graph Insn' e x))
    d (CCLabel      {}       )   _    = return Nothing
    d (CCLetVal id (ILOccurrence ty v occ)) a =
        case lookupAvailMap (v, occ) (availOccs a) of
              [] -> return Nothing
              xs@(v' : _) -> return $ Just (mkMiddle $ CCRebindId (text "occ-reuse") (TypedId ty id) v' )

    d (CCLetVal     {}       )   _    = return Nothing
    d (CCLetFuns    {}       )   _    = return Nothing
    d (CCTupleStore {}       )   _    = return Nothing
    d (CCRebindId   {}       )   _    = return Nothing
    -- When we see a load from a root and a prior load of that root is
    -- in scope that hasn't been killed by a potential GC, replace the
    -- new load with the value of the old one.
    -- That is, replace::
    --          let var  = load root in
    --          let var' = load root in
    --          ... var ... var' ...
    -- with::
    --          let var  = load root in
    --          REPLACE var' WITH var in
    --          ... var ... var' ...
    d (CCGCLoad     var' root0)   a =
        let root = s a root0 in
        let replacement = if root == root0 then Nothing
                           else Just $ mkMiddle $ CCGCLoad var' root in
        case lookupAvailMap root (rootLoads a) of
              [var] -> return $ Just $ mkMiddle (CCRebindId (text "gcload") var' var)
              _     -> return replacement

    d (CCGCInit j v root0) a =
      let root = s a root0 in
      if (not doReuseRootSlots) || root /= root0
       then -- If we don't want to reuse root slots,
            -- don't rewrite gc init nodes.
            return Nothing
       else
        -- Note: we remove the root eligible for replacement from consideration.
        -- Also, if a root is killed in the body of a loop, it will be marked
        -- as such at the head of the loop, so we restrict ourselves to roots
        -- which have been both initialized and killed (on all paths), not just
        -- killed.
        let killedRoots = Set.toList $ (Set.delete root allRoots
                                                `lessAvail` unkilledRoots a)
                                                  `availFrom` initedRoots a in
        let killedRootsOfRightType = filter (varTypesEq v) killedRoots in
        let unkill f root  = f { unkilledRoots = unkilledRoots f `addAvail`  root
                               , initedRoots   = initedRoots f   `addAvail`  root } in
        case killedRootsOfRightType of
          [] -> return Nothing
          (r:_) -> let a1 = unkill a r in
                   let a2 = unkill a root in
                   let rv = Just $ mkMiddle (CCRebindId (text $ "gcinit" ++ if root /= root0 then "; root0 = " ++ show (tidIdent root0) else "; kr: " ++ show (killedRootsOfRightType)) root r)
                               <*> mkMiddle (CCGCInit j v r) in
                   if True
                    then return rv
                    else return $
                     trace ("\navailsRewrite: adding gcinit for root " ++ show (tidIdent root)
                                  ++ ";\n\tunkilled: " ++ show (unkilledRoots a)
                                  ++ ";\n\tinited: "   ++ show (initedRoots a)
                                  ++ ";\n\t    pretending to unkill " ++ show r
                                  ++ ";\n\tunkilled(1): " ++ show (unkilledRoots a1)
                                  ++ ";\n\tinited(1): "   ++ show (initedRoots a1)
                                  ++ ";\n\t    pretending to unkill " ++ show root
                                  ++ ";\n\tunkilled(2): " ++ show (unkilledRoots a2)
                                  ++ ";\n\tinited(2): "   ++ show (initedRoots a2)
                                  ++ ";\n\tallroots "  ++ show (allRoots)
                                  ) rv

    d (CCGCKill Disabled    _)   _    = return Nothing
    d (CCGCKill enabled roots)   a =
      let unkilled = (Set.map (s a) roots `availFrom` unkilledRoots a)
                                          `availFrom` initedRoots   a  in
      return $ Just $
        if Set.null unkilled
          then emptyGraph -- Remove kills of killed roots == keep unkilled ones.
          else mkMiddle (CCGCKill enabled unkilled)
    d (CCLast {}             )   _    = return Nothing

    varTypesEq v1 v2 = tidType v1 == tidType v2

    s a v = case lookupAvailMap v (availSubst a) of
              [    ] -> v
              [ v' ] -> v'
              [ _v1, _v2 ] -> trace ("GCRoots.hs: OOPS, " ++ show v ++ " mapped to two vars! choosing neither") v
              s -> error $ "GCRoots.hs: Expected avail. subst to map " ++ show v
                           ++ " to zero or one variables, but had " ++ show s

runAvails :: BasicBlockGraph' -> RootLiveWhenGC -> Map Ident MayGC -> Bool
                                                -> Compiled BasicBlockGraph'
runAvails bbgp rootsLiveAtGCPoints mayGCmap doReuseRootSlots = do
         uref <- gets ccUniqRef
         lift $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M BasicBlockGraph'
    go bbgp = do
        let ((_,blab), _) = bbgpEntry bbgp
        -- NOTE! The bottom element for the loaded & initialized roots is
        --       (UnivMinus empty), which is what we use for joins, but we use
        --       (Avail empty), i.e. top, for the entry block. Thus if/when we
        --       go back to the entry, we'll discard loads/inits from the body.
        --       See the commentary on AvailSet and AvailMap.
        let init = Avails (UniverseMinus Set.empty) emptyAvailMap (Avail Set.empty) emptyAvailMap emptyAvailMap
        (body' , _, _) <- analyzeAndRewriteFwd fwd (JustC [bbgpEntry bbgp])
                                                           (bbgpBody bbgp)
                           (mapSingleton blab init)
        return bbgp { bbgpBody = body' }

    --__fwd = debugFwdTransfers trace showing (\_ _ -> True) fwd
    _fwd = debugFwdJoins trace (\_ -> True) fwd
    fwd = FwdPass { fp_lattice  = availsLattice
                  , fp_transfer = availsXfer mayGCmap
                  , fp_rewrite  = availsRewrite rootsLiveAtGCPoints doReuseRootSlots
                  }

--showing :: Insn' e x -> String
--showing insn = show (pretty insn)

availsLattice :: DataflowLattice Avails
availsLattice = DataflowLattice
  { fact_name = "Availables"
  , fact_bot  = Avails (UniverseMinus Set.empty) botAvailMap
                       (UniverseMinus Set.empty) botAvailMap botAvailMap
  , fact_join = add
  }
    where add _lab (OldFact (Avails ok oa oi os ox)) (NewFact (Avails nk na ni ns nx))
                 = let r = (ch, Avails jk ja ji js jx)
                       --fp (v, occ) = (tidIdent v, map fst occ)
                       --sm = Set.map tidIdent
                           in
                       r   {-
                   case c3 of
                     False -> r
                     _ -> trace ("changed@" ++ show _lab ++ ";\nox=" ++ show (concretizeAvailMap fp sm ox)
                                                         ++ ";\nnx=" ++ show (concretizeAvailMap fp sm nx)
                                                         ++ ";\njx=" ++ show (concretizeAvailMap fp sm jx)) r
                                                         -}
            where
              jk = nk `intersectAvails` ok
              ji = ni `intersectAvails` oi
              (js, c1) = os `intersectAvailMap` ns
              (ja, c2) = oa `intersectAvailMap` na
              (jx, c3) = ox `intersectAvailMap` nx
              ch = changeIf (availSmaller jk ok || availSmaller ji oi
                                                || c1 || c2 || c3)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


-- |||||||||||||||||||||||| Rebind elimination ||||||||||||||||||{{{

data Rebinds = Rebinds { rebindSubst :: AvailMap LLRootVar LLVar }
               deriving Show

rebindXfer :: FwdTransfer Insn' Rebinds
rebindXfer = mkFTransfer3 go go (distributeXfer rebindLattice go)
  where
    go :: Insn' e x -> Rebinds -> Rebinds
    go (CCRebindId _ v1 v2 ) f = f { rebindSubst = insertAvailMap v1 v2 (rebindSubst f) }
    go _ f = f

rebindRewrite :: forall m. FuelMonad m => FwdRewrite m Insn' Rebinds
rebindRewrite = mkFRewrite d
  where
    d :: Insn' e x -> Rebinds -> m (Maybe (Graph Insn' e x))
    d (CCLabel      {}       )   _    = return Nothing
    d (CCLetVal id letable) a =
        let letable' = substVarsInLetable (s a) letable in
        if  letable' == letable
          then return Nothing
          else return $ Just (mkMiddle $ CCLetVal id letable' )
    d (CCLetFuns ids clos    )   a    =
      let clos' = map (\(Closure p e capts asrc) ->
                         Closure p (s a e) (map (s a) capts) asrc) clos in
      if clos' == clos
        then return Nothing
        else return $ Just (mkMiddle $ CCLetFuns ids clos' )
    d (CCTupleStore vs v amr )   a    =
      let vs' = map (s a) vs in
      if vs' == vs
        then return Nothing
        else return $ Just (mkMiddle $ CCTupleStore vs' v amr )
    d (CCRebindId doc v1 v2) a =
      let vs'@(v1' , v2' ) = (s a v1, s a v2) in
      if vs' == (v1, v2)
        then return Nothing
        else return $ Just (mkMiddle $ CCRebindId doc v1' v2' )
    d (CCGCLoad  v1 v2) a =
      let vs'@(v1' , v2' ) = (s a v1, s a v2) in
      if vs' == (v1, v2)
        then return Nothing
        else return $ Just (mkMiddle $ CCGCLoad v1' v2' )
    d (CCGCInit j v root0)       a =
      let vs'@(v' , r' ) = (s a v, s a root0) in
      if vs' == (v, root0)
        then return Nothing
        else return $ Just (mkMiddle $ CCGCInit j v' r' )
    d (CCGCKill disen roots)     a =
        let roots' = Set.map (s a) roots in
        if roots' == roots
          then return Nothing
          else return $ Just (mkMiddle $ CCGCKill disen roots' )
    d (CCLast (CCCont bid vs)) a =
      let vs' = map (s a) vs in
      if vs' == vs
        then return Nothing
        else return $ Just (mkLast $ CCLast (CCCont bid vs' ))
    d (CCLast (CCCall bid ty id v vs)) a =
      let (v', vs' ) = (s a v, map (s a) vs) in
      if (v', vs' ) == (v, vs)
        then return Nothing
        else return $ Just (mkLast $ CCLast (CCCall bid ty id v' vs' ))
    d (CCLast (CCCase v cases def)) a =
      let v' = s a v in
      if v' == v
        then return Nothing
        else return $ Just (mkLast $ CCLast (CCCase v' cases def))

    s a v = case lookupAvailMap v (rebindSubst a) of
              [    ] -> v
              [ v' ] -> v'
              [ _v1, _v2 ] -> trace ("GCRoots.hs: OOPS, " ++ show v ++ " rebound to two vars! choosing neither") v
              s -> error $ "GCRoots.hs: Expected rebinds. subst to map " ++ show v
                           ++ " to zero or one variables, but had " ++ show s

runRebinds :: BasicBlockGraph' -> Compiled BasicBlockGraph'
runRebinds bbgp = do
         uref <- gets ccUniqRef
         lift $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M BasicBlockGraph'
    go bbgp = do
        let ((_,blab), _) = bbgpEntry bbgp
        let init = Rebinds emptyAvailMap
        (body' , _, _) <- analyzeAndRewriteFwd fwd (JustC [bbgpEntry bbgp])
                                                           (bbgpBody bbgp)
                           (mapSingleton blab init)
        return bbgp { bbgpBody = body' }

    --__fwd = debugFwdTransfers trace showing (\_ _ -> True) fwd
    --_fwd = debugFwdJoins trace (\_ -> True) fwd
    fwd = FwdPass { fp_lattice  = rebindLattice
                  , fp_transfer = rebindXfer
                  , fp_rewrite  = rebindRewrite
                  }

rebindLattice :: DataflowLattice Rebinds
rebindLattice = DataflowLattice
  { fact_name = "Rebindings"
  , fact_bot  = Rebinds botAvailMap
  , fact_join = add
  }
    where add _lab (OldFact (Rebinds ro)) (NewFact (Rebinds rn))
                 = (ch, Rebinds rj)
            where
              (rj, c) = ro `intersectAvailMap` rn
              ch = changeIf c
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

canCCLastGC mayGCmap (CCCall _ _ _ v _) =
  boolGC $ Map.findWithDefault (GCUnknown "") (tidIdent v) mayGCmap
canCCLastGC _        (CCCont {}) = False
canCCLastGC _        (CCCase {}) = False

