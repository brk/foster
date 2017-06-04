{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns, RankNTypes,
             ScopedTypeVariables, NoMonoLocalBinds #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.GCRoots(insertSmartGCRoots, insertDumbGCRoots',
                      stripKills, fnty_of_procty) where

import Prelude hiding ((<*>))

import Compiler.Hoopl
import Foster.HooplDominatorPass

import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.Boxes as Boxes

import Foster.Base(TExpr, TypedId(TypedId), freeTypedIds, Ident(..), Occurrence,
                   tidType, tidIdent, typeOf, MayGC(), boolGC)
import Foster.CFG(runWithUniqAndFuel, M, rebuildGraphM, mapGraphNodesM_, rebuildGraphAccM, BlockId)
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
           keys, assocs, delete, fromList, keysSet, alter)
import qualified Data.Text as T(pack)
import Control.Monad(when, liftM)
import Control.Monad.IO.Class(liftIO)
import Control.Monad.State(evalStateT, get, put, modify, StateT, lift, gets,
                           execState, State)

-- | Explicit insertion (and optimization) of GC roots.

-- Assumption: allocation has already been made explicit,
--             and we're being called as part of ILExpr.hs's
--             pre-codegen preparations.

showOptResults = False
gDoReuseRootSlots = False -- True -- TODO measure effect of disabling this optimization.

--------------------------------------------------------------------

-- Every operation that might potentially trigger copying GC could invalidate
-- the values stored in the root slots, so we must insert reloads
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

insertDumbGCRoots' :: BasicBlockGraph' -> Bool -> Compiled ( BasicBlockGraph' , [RootVar] )
insertDumbGCRoots' bbgp0 dump = do
  bbgp' <- insertDumbGCRoots bbgp0 dump
  return (bbgp' , computeUsedRoots bbgp')
 where

    computeUsedRoots bbgp = Set.toList . Set.fromList $
                             Map.elems (computeGCRootsForVars bbgp)

    computeGCRootsForVars bbgp = foldGraphNodes go (bbgpBody bbgp) Map.empty
      where
        go :: Insn' e x -> GCRootsForVariables -> GCRootsForVariables
        go (CCGCInit _ v root) s = -- assert v not in s
                                   Map.insert v root s
        -- don't recurse into functions: we don't want their roots!
        go _                   s = s

-- Precondition: allocations have been made explicit in the input graph.
-- Precondition: may-gc analysis has updated the annotations in the graph.
insertSmartGCRoots :: Ident -> BasicBlockGraph' -> Map Ident MayGC -> Bool -> Compiled ( BasicBlockGraph' , [RootVar] )
insertSmartGCRoots procid bbgp0 mayGCmap dump = do
  runRootConsistencyChecker "bbgp0" bbgp0

  --   1) Run a rewriting (non-dataflow) pass to insert root initializers
  --      at first uses, and insert disabled kill markers after each use.
  bbgp'1 <- insertDumbGCRoots bbgp0 dump

  runRootConsistencyChecker ("bbgp'1 for " ++ show procid) bbgp'1

  --   2) Fold to compute the (root, initializing variable) relation/mapping.
  let gcr = computeGCRootsForVars bbgp'1

  --   3) Run a backwards liveness pass to compute:
  --        * What the set of live roots are, when a GC might occur.
  --      This pass also enables kills (after trimming out live roots).
  (bbgp'2 , rootsLiveAtGCPoints) <- runLiveAtGCPoint2 bbgp'1 mayGCmap

  runRootConsistencyChecker "bbgp'2" bbgp'2

  --   4) Run a rewriting pass to remove actions referencing dead roots.
  bbgp'3  <- removeDeadGCRoots bbgp'2 (mapInverse gcr) rootsLiveAtGCPoints

  runRootConsistencyChecker "bbgp'3" bbgp'3

  --   5) Run a rewriting (non-dataflow) pass to insert root kills for *every*
  --      root at *every* basic block.
  bbgp'4 <- insertDumbGCKills bbgp'3 dump (Map.elems gcr)

  runRootConsistencyChecker "bbgp'4" bbgp'4

  --   6) Run a forwards pass to trim redundant kills.
  --      If we are configured to reuse root slots,
  --      this is where we do it.
  bbgp'4b  <- relabelEntryExitBlocks bbgp'4
  bbgp'5a0 <- runAvails bbgp'4b rootsLiveAtGCPoints mayGCmap gDoReuseRootSlots
  bbgp'5a  <- runRebinds bbgp'5a0

  -- runAvails might have reused a root slot in a forwards pass, which might
  -- have invalidated liveness information (backwards pass). So we'll re-run the
  -- backwards pass, and finish with runAvails configured not to reuse slots.
  (bbgp'5b , rootsLiveAtGCPoints'5b) <- runLiveAtGCPoint2 bbgp'5a mayGCmap
  bbgp'5c  <- removeDeadGCRoots bbgp'5b (mapInverse gcr) rootsLiveAtGCPoints'5b
  bbgp'5d <- runAvails bbgp'5c rootsLiveAtGCPoints'5b mayGCmap False

  liftIO $ when (showOptResults || dump) $ do
              putStrLn "difference from runAvails:"
              Boxes.printBox $ catboxes2 (bbgpBody bbgp'4) (bbgpBody bbgp'5d )
              putStrLn "variant 4:"
              Boxes.printBox $ makebox (bbgpBody bbgp'4)
              putStrLn "variant 5a0:"
              Boxes.printBox $ makebox (bbgpBody bbgp'5a0)
              putStrLn "variant 5a:"
              Boxes.printBox $ makebox (bbgpBody bbgp'5a)

  runRootConsistencyChecker "bbgp'5d" bbgp'5d

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

-- Because LLVM does not automatically spill GCable pointers to the stack
-- (as it doesn't distinguish different types of pointers in the backends)
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

-- When we see a load from a root, the root becomes live in prior nodes;
-- when we see a root init happen, the root becomes dead in prior nodes.
-- When we see an operation that may induce (copying) GC,
-- we'll add the current set of live roots to the set of
-- roots we keep.
liveAtGCPointXfer2 :: Map Ident MayGC -> BwdTransfer Insn' LiveAGC2
liveAtGCPointXfer2 mayGCmap = mkBTransfer go
  where
    go :: Insn' e x -> Fact x LiveAGC2 -> LiveAGC2
    go (CCLabel   {}        ) f = ifgc False            f
    go (CCGCLoad _v fromrt _) f = markLive   fromrt     f
    go (CCGCInit _ _v toroot) f = markDead   toroot     f
    go (CCGCKill {}         ) f = {- just ignore it  -} f
    go (CCLetVal  _ letable ) f = ifgc (boolGC maygc)   f where maygc = canGC mayGCmap letable
    go (CCLetFuns _ids _clos) f = ifgc True             f
    go (CCTupleStore   {}   ) f = ifgc False            f
    go (CCRebindId     {}   ) _ =
        error $ "GCRoots.hs: Backwards rewrite(liveAtGCPointXfer2) saw a rebind-id node,\n"
             ++ "which has probably invalidated the computed results. Fix this by using\n"
             ++ "a forwards rewriting pass to resolve & remove RebindId nodes before\n"
             ++ "running a backwards analysis."
    go node@(CCLast {}) fdb =
          let f = combineLastFacts fdb node in
          ifgc False f

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
                            liftIO $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
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

makebox bbg = boxify $ measure $ pretty bbg

catboxes2 bbg1 bbg2 = Boxes.hsep 1 Boxes.left $
                            [(boxify . measure . plain . pretty) bbg1
                            ,(boxify . measure .         pretty) bbg2]

measure :: Doc -> Boxes.Box
measure d = Boxes.vcat Boxes.left (map Boxes.text $ lines $ show d)

boxify :: Boxes.Box -> Boxes.Box
boxify b = v Boxes.<> (h Boxes.// b Boxes.// h) Boxes.<> v
             where v = Boxes.vcat Boxes.left (take (Boxes.rows b + 2) (repeat (Boxes.char '|')))
                   h = Boxes.text $          (take (Boxes.cols b    ) (repeat '-'))


-- |||||||||||||||||||| Dumb GC root insertion ||||||||||||||||||{{{

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
   bbgp <- runRebinds bbgp0
   {--- Root insertion breaks if we process the graph in a different order than
     -- DFS-from-entry-node...
   g'bad  <- evalStateT (rebuildGraphM Nothing (bbgpBody bbgp) transform)
                             Map.empty
                             -}
   g'  <- evalStateT (rebuildGraphM (case bbgpEntry bbgp of (bid, _) -> Just bid)
                                    (bbgpBody bbgp) transform)
                             Map.empty

   liftIO $ when (showOptResults || dump) $ do Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'

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
    CCTupleStore vs v r           -> do withGCLoads (v:vs) (\(v' : vs' ) ->
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
    CCRebindId _doc _v1 _v2       -> do error $ "GCRoots.hs: insertDumbGCRoots saw unexpected CCRebindId: " ++ show (pretty insn)
    CCLast l (CCCont b vs)        -> do withGCLoads vs (\vs'  ->
                                               (mkLast $ CCLast l (CCCont b vs' )))
    CCLast l (CCCase v arms mb)   -> do withGCLoads [v] (\[v' ] ->
                                               (mkLast $ CCLast l (CCCase v' arms mb)))

  fresh str = lift $ ccFreshId (T.pack str)

  substVarsInClo s (Closure proc env capts asrc) =
        Closure proc (s env) (map s capts) asrc

  -- Return an empty graph if v doesn't need a GC root;
  -- otherwise, return a singleton GC root initializer node,
  -- and extend the substitution.
  maybeRootInitializer :: LLVar -> RootMapped (Graph Insn' O O)
  maybeRootInitializer v = do
    if not $ isGCableVar v
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
    -- TODO call maybeRootInitializers here?
    loadsAndVars <- mapM withGCLoad vs
    let (loads, vs' ) = unzip loadsAndVars
    return $ mkMiddles (concat loads) <*> mkG vs'
   where
      -- We'll rewrite something like ``call @foo (x,n)`` (where ``x`` is
      -- GCable and ``n`` isn't) with::
      --      x.load = load x.root
      --      kill x.root (disabled)
      ---     call @foo (x.load , n)
      -- We'll remove kills for live roots and enable the remainder.
      -- We'll insert root initializations in a separate pass.
      retLoaded root v = do
          id <- fresh (show (tidIdent root) ++ ".load")
          let loadedvar = TypedId (tidType root) id
          return ([CCGCLoad loadedvar root v
                  ,CCGCKill Disabled (Set.fromList [root])]
                 , loadedvar)

      _withGCLoad_t :: LLVar -> RootMapped ([Insn' O O], LLVar)
      _withGCLoad_t v = do rv <- withGCLoad (trace ("withGCLoad " ++ show v) v)
                           return $ trace ("withGCLoad " ++ show v ++ " ==> " ++ show (pretty rv)) rv

      withGCLoad :: LLVar -> RootMapped ([Insn' O O], LLVar)
      withGCLoad v =
       if not $ isGCableVar v
         then return ([], v)
         else do
               gcr <- get
               case Map.lookup v gcr of
                 Just root -> do retLoaded root v
                 Nothing   -> do
                                 rootid <- fresh (show (tidIdent v) ++ ".ROOT")
                                 let root = TypedId (tidType v) rootid
                                 put (Map.insert v root gcr)
                                 retLoaded root v

  isGlobalFunc (GlobalSymbol _) = True
  isGlobalFunc (Ident _ _) = False

  isGCableVar v = not (isGlobalFunc (tidIdent v)) && isGCable (tidType v)

  -- Filter out non-pointer-typed variables from live set.
  isGCable ty = case ty of
                 LLPrimInt _            -> False
                 LLNamedType "Float64"  -> False
                 LLStructType tys       -> any isGCable tys
                 LLProcType _ _ _       -> False
                 LLPtrType (LLStructType []) -> False
                 LLPtrType _            -> True -- could have further annotations on ptr types
                 LLNamedType _          -> True -- TODO maybe not?
                 LLCoroType _ _         -> True
                 LLArrayType _          -> True
                 LLPtrTypeUnknown       -> True

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
   g'  <- rebuildGraphM Nothing (bbgpBody bbgp) transform
   liftIO $ when (showOptResults || dump) $ do Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'
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
   g' <- evalStateT (rebuildGraphM (case bbgpEntry bbgp of (bid, _) -> Just bid)
                                   (bbgpBody bbgp) transform)
                    Map.empty

   liftIO $ when showOptResults $ Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'

   return bbgp { bbgpBody =  g' }
 where
  isLive root = Set.member root liveRoots
  iflive root g = if isLive root then return g else return emptyGraph

  transform :: forall e x. Insn' e x -> RootMapped (Graph Insn' e x)
  transform insn = case insn of
    CCLabel {}                    -> do return $ mkFirst $ insn
    CCGCLoad  v     root  _orig   -> do m <- get
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
    CCLast l (CCCont b vs)        -> do undoDeadGCLoads vs (\vs'  ->
                                               (mkLast $ CCLast l (CCCont b vs' )))
    CCLast l (CCCase v arms mb)   -> do undoDeadGCLoads [v] (\[v' ] ->
                                               (mkLast $ CCLast l (CCCase v' arms mb)))
    CCRebindId     {}             -> do return $ mkMiddle $ insn

  _varForRoot_t root = let rv = varForRoot (trace ("varForRoot " ++ show root) root) in
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

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

fnty_of_procty pt@(LLProcType (env:_args) _rets _cc) =
      LLPtrType (LLStructType [pt, env])
fnty_of_procty other = error $ "GCRoots.hs: fnty_of_procty undefined for " ++ show other

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

{-
instance Show Avails where show a = show (pretty a)
instance Pretty Avails where
  pretty (Avails uk lr fr) = text "(Avails unkilledRoots=" <> text (show uk)
                         <+> text "loadedRoots="   <> text (show uk)
                         <+> text "loadsForRoots=" <> text (show $ Map.map (Set.map tidIdent) fr) <> text ")"
                         <+> text "availSubst=" <> ( <> text ")"
                         <+> text "loadsForRoots=" <> text (show $ Map.map (Set.map tidIdent) fr) <> text ")"
                         -}

dominatedBy domInfo label = lookupFact (snd label) domInfo

computeDomInfo factbase =
  mapFromListWith (++) [(d, [l]) | (l,d) <- mapToList $ immediateDominators factbase]

availsXfer :: Map Ident MayGC -> LabelMap [Label] -> FwdTransfer Insn' Avails
availsXfer mayGCmap domInfo = mkFTransfer3 go go
                                dominanceXfer
                                --(distributeXfer availsLattice go)
  where
    go :: Insn' e x -> Avails -> Avails
    go (CCLabel      {}    ) f = f
    go (CCGCLoad var root _) f = makeLoadAvail var root f
    go (CCGCInit _ _   root) f =        f `unkill` root
    go (CCGCKill (Enabled _) roots) f = f `killin` roots
    go (CCGCKill     {}    ) f = f
    go (CCLetVal id letable) f = ifgc (boolGC maygc)  xf where maygc = canGC mayGCmap letable
                                                               xf = considerLet f id letable
    go (CCLetFuns    {}    ) f = ifgc True             f
    go (CCTupleStore {}    ) f = f
    go (CCRebindId _ v1 v2 ) f = f { availSubst = insertAvailMap v1 v2 (availSubst f) }
    go (CCLast       {}    ) f = ifgc False            f

    ifgc mayGC f = if mayGC then f { rootLoads = emptyAvailMap }
                            else f -- when a GC might occur, all root loads
                                   -- become invalidated...

    -- The simple seeming thing to do would be to use a transfer function driven by a
    -- dominance analysis, but the issue is that we need the label from the entry node
    -- in CCLast in order to get the proper list of dominance-successors.
    -- Stepping back, avails rewriting isn't a dataflow property, just a closure property.
    dominanceXfer :: Insn' O C -> Avails -> FactBase Avails
    dominanceXfer lastNode@(CCLast label _) avails =
      case dominatedBy domInfo label of
        Just labels -> let list = [ (l, go lastNode avails) | l <- labels ] in
                        --trace ("domXFER: domSucc for " ++ show label ++ "\nis " ++ show labels ++ "\nvs regular " ++ show (successors lastNode)) $
                          mkFactBase availsLattice list
        Nothing -> --trace ("domXFER: no entry for " ++ show label ++ " in " ++ show domInfo)
                    noFacts

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
              (v' : _) -> return $ Just (mkMiddle $ CCRebindId (text "occ-reuse") (TypedId ty id) v' )

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
    d (CCGCLoad     var' root0 orig)   a =
        let root = s a root0 in
        let replacement = if root == root0 then Nothing
                           else Just $ mkMiddle $ CCGCLoad var' root orig in
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
                   if True -- (head $ show (tidIdent root)) /= '.'
                    then return rv
                    else return $
                     trace ("\n\navailsRewrite: adding gcinit for root " ++ show (tidIdent root)
                                  ++ ";\n\tunkilled: " ++ show (mapAvailSet tidIdent $ unkilledRoots a)
                                  ++ ";\n\tinited: "   ++ show (mapAvailSet tidIdent $ initedRoots a)
                                  ++ ";\n\t    pretending to unkill " ++ show r
                                  ++ ";\n\tunkilled(1): " ++ show (mapAvailSet tidIdent $ unkilledRoots a1)
                                  ++ ";\n\tinited(1): "   ++ show (mapAvailSet tidIdent $ initedRoots a1)
                                  ++ ";\n\t    pretending to unkill " ++ show root
                                  ++ ";\n\tunkilled(2): " ++ show (mapAvailSet tidIdent $ unkilledRoots a2)
                                  ++ ";\n\tinited(2): "   ++ show (mapAvailSet tidIdent $ initedRoots a2)
                                  ++ ";\n\tallroots "  ++ show (allRoots)
                                  ++ ";\n\tkRoRT: " ++ show (map tidIdent $ killedRootsOfRightType)
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
         liftIO $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M BasicBlockGraph'
    go bbgp = do
        let ((_,blab), _) = bbgpEntry bbgp

        (_ , domfacts, _) <- analyzeAndRewriteFwd
                                --(debugFwdTransfers trace showing (\_ _ -> True) (debugFwdJoins trace (\_ -> True) domPass))
                                domPass
                                (JustC [bbgpEntry bbgp]) (bbgpBody bbgp) (mapSingleton blab domEntry)

        -- NOTE! The bottom element for the loaded & initialized roots is
        --       (UnivMinus empty), which is what we use for joins, but we use
        --       (Avail empty), i.e. top, for the entry block. Thus if/when we
        --       go back to the entry, we'll discard loads/inits from the body.
        --       See the commentary on AvailSet and AvailMap.
        let init = Avails (UniverseMinus Set.empty) emptyAvailMap (Avail Set.empty) emptyAvailMap emptyAvailMap
        (body' , _, _) <- analyzeAndRewriteFwd (fwd (domfacts)) (JustC [bbgpEntry bbgp])
                                                              (bbgpBody bbgp)
                           (mapSingleton blab init)
        return bbgp { bbgpBody = body' }

    --tracedomfacts domfacts = trace ("domfacts: " ++ show domfacts ++ "\nwith domInfo: "
    --                                    ++ show (computeDomInfo domfacts :: LabelMap [Label])
    --                                    ++ "\n for\n" ++ show (pretty bbgp)) domfacts

    --__fwd = debugFwdTransfers trace showing (\_ _ -> True) fwd
    -- _fwd = debugFwdJoins trace (\_ -> True) fwd
    fwd domfacts = FwdPass {
                    fp_lattice  = availsLattice
                  , fp_transfer = availsXfer mayGCmap (computeDomInfo domfacts)
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

-- We need to make sure that the "entry" labels on CCLast nodes are up-to-date
-- so that the dominator-successors computation is accurate.
relabelEntryExitBlocks :: BasicBlockGraph' -> Compiled BasicBlockGraph'
relabelEntryExitBlocks bbgp = do
   (g', _) <- case bbgpEntry bbgp of (bid, _) -> rebuildGraphAccM Nothing (bbgpBody bbgp) bid transform
   return BasicBlockGraph' {
                 bbgpEntry = bbgpEntry bbgp,
                 bbgpRetK  = bbgpRetK  bbgp,
                 bbgpBody  = g'
          }
  where
      transform :: BlockId -> Insn' e x -> Compiled (Graph Insn' e x, BlockId)
      transform ent insn = case insn of
        CCLabel l               -> return (mkFirst  insn, fst l)

        CCLetVal     {}         -> return (mkMiddle insn, ent)
        CCLetFuns    {}         -> return (mkMiddle insn, ent)
        CCGCLoad     {}         -> return (mkMiddle insn, ent)
        CCGCInit     {}         -> return (mkMiddle insn, ent)
        CCGCKill     {}         -> return (mkMiddle insn, ent)
        CCTupleStore {}         -> return (mkMiddle insn, ent)
        CCRebindId   {}         -> return (mkMiddle insn, ent)

        CCLast _ cclast         -> do return (mkLast (CCLast ent cclast), ent)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


-- ||||||||||||||| GC Root Kill Consistency Checker |||||||||||||{{{

type LiveRoots = AvailSet LLRootVar

-- When we see a root get initialized, it is removed from the set of
-- dead roots (going forwards). When we see a root get killed, it is
-- added to the set of dead roots.
liveRootsXfer :: String -> FwdTransfer Insn' LiveRoots
liveRootsXfer msg = mkFTransfer3 go go (distributeXfer liveRootsLattice go)
  where
    go :: Insn' e x -> LiveRoots -> LiveRoots
    go (CCGCLoad var root _orig) lives =
         if root `availIn` lives
            then lives
            else error $ "GCRoots.hs: runRootConsistencyChecker @ " ++ msg
                      ++ "\nDetected load from dead root: " ++ show root
                      ++ "\nBound to variable: " ++ show var
                      ++ "\nLive roots are: " ++ show lives
                      ++ "\nOrig is: " ++ show _orig
    go (CCGCInit _ _   root)        lives = lives `addAvail`  root
    go (CCGCKill (Enabled _) roots) lives = lives `delAvails` roots
    go _ lives = lives

liveRootsRewrite :: forall m. FuelMonad m => FwdRewrite m Insn' LiveRoots
liveRootsRewrite = mkFRewrite d
  where
    d :: Insn' e x -> LiveRoots -> m (Maybe (Graph Insn' e x))
    d _ _ = return Nothing

runRootConsistencyChecker :: String -> BasicBlockGraph' -> Compiled ()
runRootConsistencyChecker msg bbgp = do
         uref <- gets ccUniqRef
         liftIO $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M ()
    go bbgp = do
        let ((_,blab), _) = bbgpEntry bbgp
        (_body , _, _) <- analyzeAndRewriteFwd fwd (JustC [bbgpEntry bbgp])
                                                           (bbgpBody bbgp)
                           (mapSingleton blab $ Avail Set.empty) -- no live @ start
        return ()

    fwd = FwdPass { fp_lattice  = liveRootsLattice
                  , fp_transfer = liveRootsXfer msg
                  , fp_rewrite  = liveRootsRewrite
                  }

-- If we're tracking live roots, then we should use intersection
--      (must be live in all branches); the initial condition is
--      the empty set, representing that no roots are live initially;
--      bottom is the universl set.

liveRootsLattice :: DataflowLattice LiveRoots
liveRootsLattice = DataflowLattice
  { fact_name = "Root kill consistency checker"
  , fact_bot  = (UniverseMinus Set.empty) -- bottom w/r/t intersection
  , fact_join = add
  }
    where add _lab (OldFact (dra)) (NewFact (drb))
                 = (ch, drr)
            where
              drr = dra `intersectAvails` drb
              ch  = changeIf (availSmaller drr dra)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||| Rebind elimination ||||||||||||||||||{{{

-- Rebind elimination, *with removal*, is in some sense
-- a forwards analysis and a backwards rewrite!

runRebinds :: BasicBlockGraph' -> Compiled BasicBlockGraph'
runRebinds bbgp = do
  let (bid, _) = bbgpEntry bbgp
  let m = execState (mapGraphNodesM_ am bid (bbgpBody bbgp)) Map.empty
  g <- rebuildGraphM Nothing (bbgpBody bbgp) (d m)
  return bbgp { bbgpBody = g }
 where
    am :: forall e x. Insn' e x -> State (Map LLVar [LLVar]) ()
    am (CCRebindId _ v1 v2) = do modify $ Map.alter (ins v2) v1
    am _ = return ()

    ins v Nothing   = Just [v]
    ins v (Just vs) = Just (v:vs)

    d :: Monad m => Map LLRootVar [LLVar] -> Insn' e x -> m (Graph Insn' e x)
    d _ insn@(CCLabel {})     = return (mkFirst insn)
    d a (CCLetVal id letable) =
        let letable' = substVarsInLetable (s a) letable in
        return (mkMiddle $ CCLetVal id letable' )
    d a (CCLetFuns ids clos    ) =
      let clos' = map (\(Closure p e capts asrc) ->
                         Closure p (s a e) (map (s a) capts) asrc) clos in
      return (mkMiddle $ CCLetFuns ids clos' )
    d a (CCTupleStore vs v amr ) =
      return (mkMiddle $ CCTupleStore (map (s a) vs) (s a v) amr )
    d _ (CCRebindId {}) = return emptyGraph
    d a (CCGCLoad  v1 v2 orig) =
      return (mkMiddle $ CCGCLoad (s a v1) (s a v2) (s a orig))
    d a (CCGCInit j v root0)     =
      return (mkMiddle $ CCGCInit j (s a v) (s a root0))
    d a (CCGCKill disen roots)   =
        return (mkMiddle $ CCGCKill disen (Set.map (s a) roots))
    d a (CCLast l (CCCont bid vs)) =
      return (mkLast $ CCLast l (CCCont bid (map (s a) vs) ))
    d a (CCLast l (CCCase v cases def)) =
      return (mkLast $ CCLast l (CCCase (s a v) cases def))

    s a v = case Map.lookup v a of
              Nothing -> v
              Just [ v' ] -> v'
              Just [ _v1, _v2 ] -> trace ("GCRoots.hs: OOPS, " ++ show v ++ " rebound to two vars! choosing neither") v
              s -> error $ "GCRoots.hs: Expected rebinds. subst to map " ++ show v
                           ++ " to zero or one variables, but had " ++ show s

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


-- ||||||||||||||||||||||| Root kill elimination ||||||||||||||||{{{

stripKills :: BasicBlockGraph' -> Compiled BasicBlockGraph'
stripKills bbgp = do
  g <- rebuildGraphM Nothing (bbgpBody bbgp) d
  return bbgp { bbgpBody = g }
 where
    d :: Monad m => Insn' e x -> m (Graph Insn' e x)
    d insn@(CCLabel {})     = return (mkFirst insn)
    d insn@(CCLast  {})     = return (mkLast  insn)

    d (CCGCKill {})   = return emptyGraph

    d insn@(CCRebindId {})   = return $ mkMiddle insn
    d insn@(CCLetVal {})     = return $ mkMiddle insn
    d insn@(CCLetFuns {})    = return $ mkMiddle insn
    d insn@(CCTupleStore {}) = return $ mkMiddle insn
    d insn@(CCGCLoad {})     = return $ mkMiddle insn
    d insn@(CCGCInit {})     = return $ mkMiddle insn

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
