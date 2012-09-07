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

import Foster.Base(Uniq, TExpr, TypedId(TypedId), Ident(..), freeTypedIds,
                   tidType, tidIdent, mapFoldM' , typeOf)
import Foster.CFG(runWithUniqAndFuel, M, rebuildGraphAccM, rebuildGraphM)
import Foster.CloConv
import Foster.TypeLL
import Foster.Letable

import Data.Maybe(fromMaybe)
import Data.IORef(IORef, modifyIORef, readIORef)
import Data.Map(Map)
import qualified Data.Set as Set
import qualified Data.Map as Map(lookup, empty, fromList, elems, keysSet,
                                                        insert, findWithDefault)
import qualified Data.Text as T(pack)
import Control.Monad.State(evalStateT, get, put, StateT)

-- | Explicit insertion (and optimization) of GC roots.
-- | Assumption: allocation has already been made explicit.

--------------------------------------------------------------------

-- Every potentially-GCing operation can potentially invalidate
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
-- liveness markers after loads, but unfortunately that would require
-- a backwards analysis combined with a forward rewrite, which Hoopl
-- does not support.

type GCRootsForVariables = Map LLVar RootVar
type VariablesForGCRoots = Map RootVar LLVar

-- Precondition: allocations have been made explicit in the input graph.
insertSmartGCRoots :: IORef Uniq -> BasicBlockGraph' -> IO ( BasicBlockGraph' , [RootVar] )
insertSmartGCRoots uref bbgp0 = do
  (bbgp' , gcr) <- insertDumbGCRoots uref bbgp0
  (bbgp'' , rootsLiveAtGCPoints) <- runLiveAtGCPoint2 uref bbgp'
  bbgp''' <- removeDeadGCRoots bbgp'' (mapInverse gcr) rootsLiveAtGCPoints
  putStrLn $ "these roots were live at GC points: " ++ show rootsLiveAtGCPoints
  return ( bbgp''' , Set.toList rootsLiveAtGCPoints)
 where
    mapInverse m = let ks = Map.keysSet m in
                   let es = Set.fromList (Map.elems m) in
                   if Set.size ks == Set.size es
                     then Map.fromList (zip (Set.toList es) (Set.toList ks))
                     else error $ "mapInverse can't reverse a non-one-to-one map!"
                               ++ "\nkeys: " ++ show ks ++ "\nelems:" ++ show es

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
liveAtGCPointXfer2 :: BwdTransfer Insn' LiveAGC2
liveAtGCPointXfer2 = mkBTransfer go
  where
    go :: Insn' e x -> Fact x LiveAGC2 -> LiveAGC2
    go (CCLabel   {}        ) f = ifgc False            f
    go (CCGCLoad _v fromroot) f = markLive fromroot     f
    go (CCGCInit _ _v toroot) f = markDead   toroot     f
    go (CCGCKill {}         ) f = {- just ignore it  -} f
    go (CCLetVal  _id  l    ) f = ifgc (canGCLetable l) f
    go (CCLetFuns _ids _clos) f = ifgc True             f
    go (CCTupleStore   {}   ) f = ifgc False            f
    go node@(CCLast    cclast) fdb =
          let f = combineLastFacts fdb node in
          case cclast of
            (CCCont {}       ) -> ifgc False f
            (CCCall _ _ _ v _) -> ifgc (canGCCalled v) f
            (CCCase {}       ) -> ifgc False f

    markLive root (s, g, c) = (Set.insert root s, g, c)
    markDead root (s, g, c) = (Set.delete root s, g, c)

    ifgc mayGC (s, g, c) = if mayGC then (s, g `Set.union` s, True)
                                    else (s, g              , c)

-- If we see a (disabled) GCKill marker when a root is still alive,
-- we'll remove the marker, but if the root is dead, we'll enable
-- the marker, since it is, by definition, (conservatively) correct.
liveAtGCPointRewrite2 :: forall m. FuelMonad m => BwdRewrite m Insn' LiveAGC2
liveAtGCPointRewrite2 = mkBRewrite d
  where
    d :: Insn' e x -> Fact x LiveAGC2 -> m (Maybe (Graph Insn' e x))
    d (CCLabel      {}      )    _    = return Nothing
    d (CCLetVal     {}      )    _    = return Nothing
    d (CCLetFuns    {}      )    _    = return Nothing
    d (CCTupleStore {}      )    _    = return Nothing
    d (CCGCLoad     {}      )    _    = return Nothing
    d (CCGCInit     {}      )    _    = return Nothing
    d (CCGCKill (Enabled _) _root)    _    = return Nothing -- leave as-is.
    d (CCGCKill Disabled     root) (s,_,c) = -- s is the set of live roots
          if {-trace ("agc @ GCKILL " ++ show root ++ " : live? " ++ show (Set.member root s) ++ show s) $-}
             Set.member root s
            then return $ Just emptyGraph
             -- If a root is live, remove its fake kill node.
             -- Otherwise, toggle the node from disabled to enabled.
            else return $ Just (mkMiddle (CCGCKill (Enabled c) root))
    d _node@(CCLast {}      ) _fdb  = return Nothing

runLiveAtGCPoint2 :: IORef Uniq -> BasicBlockGraph' -> IO (BasicBlockGraph'
                                                          ,RootLiveWhenGC)
runLiveAtGCPoint2 uref bbgp = runWithUniqAndFuel uref infiniteFuel (go bbgp)
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
                  , bp_transfer = liveAtGCPointXfer2
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
--
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
-- To avoid having redundant kills, we'll only keep the kills which have a
-- potential-GC point in their continuation.
insertDumbGCRoots :: IORef Uniq -> BasicBlockGraph' -> IO (BasicBlockGraph'
                                                          ,GCRootsForVariables)
insertDumbGCRoots uref bbgp = do
   (g' , fini) <- rebuildGraphAccM (case bbgpEntry bbgp of (bid, _) -> bid)
                                       (bbgpBody bbgp) Map.empty transform

   if False then return () else do Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'

   return (bbgp { bbgpBody =  g' }, fini)

 where

  transform :: forall e x. GCRootsForVariables -> Insn' e x -> IO (Graph Insn' e x, GCRootsForVariables)
  transform gcr insn = case insn of
    -- See the note above explaining why we generate all these GCKills...
    CCLabel (_bid, vs)            -> do (inits, gcr' ) <- mapFoldM' vs gcr maybeRootInitializer
                                        return (mkFirst insn <*> catGraphs inits <*> mkMiddles [
                                                CCGCKill Disabled root | root <- Map.elems gcr' ]
                                                                                      , gcr' )
    CCGCLoad  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCGCInit  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCGCKill  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCTupleStore vs v r           -> do {- trace ("isGCable " ++ show v ++ " :" ++ show (isGCable v)) $ -}
                                         withGCLoads gcr (v:vs) (\(v' : vs' ) ->
                                          mkMiddle $ CCTupleStore vs' v' r)
    CCLetVal id val               -> do (ri, gcr' ) <- maybeRootInitializer (TypedId (typeOf val) id) gcr
                                        let vs = freeTypedIds val
                                        withGCLoads gcr' vs (\vs' ->
                                         let s = makeSubstWith vs vs' in
                                         (mkMiddle $ CCLetVal id (substVarsInLetable s val)) <*> ri)
    CCLetFuns [id] [clo]          -> do
                                        let concrete_fnty = fnty_of_procty (tidType (closureProcVar clo))
                                        (ri, gcr' ) <- maybeRootInitializer (TypedId concrete_fnty id) gcr
                                        let vs = [closureEnvVar clo]
                                        withGCLoads gcr' vs (\vs' ->
                                          let s = makeSubstWith vs vs' in
                                          (mkMiddle $ CCLetFuns [id] [substVarsInClo s clo]) <*> ri)
    CCLetFuns ids _clos           -> do error $ "CCLetFuns should all become singletons!" ++ show ids
    CCLast (CCCont b vs)          -> do withGCLoads gcr vs (\vs'  ->
                                               (mkLast $ CCLast (CCCont b vs' )))
    CCLast (CCCall b t id v vs)   -> do withGCLoads gcr (v:vs) (\(v' : vs' ) ->
                                               (mkLast $ CCLast (CCCall b t id v' vs' )))
    CCLast (CCCase v arms mb occ) -> do withGCLoads gcr [v] (\[v' ] ->
                                               (mkLast $ CCLast (CCCase v' arms mb occ)))

  fresh str = do u <- modifyIORef uref (+1) >> readIORef uref
                 return (Ident (T.pack str) u)

  substVarsInClo s (Closure proc env capts asrc) =
        Closure proc (s env) (map s capts) asrc

  maybeRootInitializer v gcr = do
    if not $ isGCable v
      then return (emptyGraph, gcr)
      else
        do junkid <- fresh (show (tidIdent v) ++ ".junk")
           let junk = TypedId (LLPtrType (LLStructType [])) junkid
           case Map.lookup v gcr of
             Just root -> do error $ "Wasn't expecting to see existing root when initializing! " ++ show v ++ "; " ++ show root
             Nothing   -> do rootid <- fresh (show (tidIdent v) ++ ".root")
                             let root = TypedId (tidType v) rootid
                             let gcr' = Map.insert v root gcr
                             return (mkMiddle $ CCGCInit junk v root, gcr' )

  -- A helper function to assist in rewriting instructions to use loads from
  -- GC roots for variables which are subject to garbage collection.
  withGCLoads :: GCRootsForVariables -> [LLVar]
                                     -> ([LLVar] -> Graph Insn' O x)
                                     -> IO (Graph Insn' O x, GCRootsForVariables)
  withGCLoads gcr vs mkG = do
    (loadsAndVars , gcr' ) <- mapFoldM' vs gcr withGCLoad
    let (loads, vs' ) = unzip loadsAndVars
    return (mkMiddles (concat loads) <*> mkG vs' , gcr' )
   where
      -- We'll rewrite something like ``call @foo (x,n)`` (where ``x`` is
      -- GCable and ``n`` isn't) with::
      --      x.load = load x.root
      --      kill x.root (disabled)
      ---     call @foo (x.load , n)
      -- We'll removed kills for live roots and enable the remainder.
      -- We'll insert root initializations in a separate pass.
      retLoaded root gcr oos = do
          id <- fresh (show (tidIdent root) ++ ".load")
          let loadedvar = TypedId (tidType root) id
          return ((oos ++ [CCGCLoad loadedvar root
                          ,CCGCKill Disabled  root], loadedvar), gcr)

      withGCLoad :: LLVar -> GCRootsForVariables
                          -> IO (([Insn' O O], LLVar), GCRootsForVariables)
      withGCLoad v gcr = do
        if not $ isGCable v
          then return (([], v), gcr)
          else case Map.lookup v gcr of
                 Just root -> do retLoaded root gcr []
                 Nothing   -> do
                                 rootid <- fresh (show (tidIdent v) ++ ".ROOT")
                                 let root = TypedId (tidType v) rootid
                                 let gcr' = Map.insert v root gcr
                                 retLoaded root gcr' []

type RootMapped = StateT GCRootsForVariables IO

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
                  -> IO BasicBlockGraph'
removeDeadGCRoots bbgp varsForGCRoots liveRoots = do
   let mappedAction = rebuildGraphM (case bbgpEntry bbgp of (bid, _) -> bid)
                                                       (bbgpBody bbgp) transform
   g' <- evalStateT mappedAction Map.empty

   if False then return () else Boxes.printBox $ catboxes2 (bbgpBody bbgp) g'

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
    CCGCKill  (Enabled _)  root   -> do if isLive root
                                         then return $ mkMiddle insn
                                         else return emptyGraph
    CCGCKill  Disabled    _root   -> do error "transform saw disabled gckill?"
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
    CCLast (CCCase v arms mb occ) -> do undoDeadGCLoads [v] (\[v' ] ->
                                               (mkLast $ CCLast (CCCase v' arms mb occ)))

  varForRoot root = case Map.lookup root varsForGCRoots of
                      Nothing -> error $ "Unable to find source variable for root " ++ show root
                      Just var -> var

  undoDeadGCLoads vs k = do
    vs' <- mapM undo vs
    return $ k vs'

  undo v = do gcRootsForVars <- get
              return $ case Map.lookup v gcRootsForVars of
                           Nothing   -> v
                           Just root -> if isLive root
                                          then v
                                          else varForRoot root

fnty_of_procty pt@(LLProcType (env:_args) _rets _cc) =
      LLPtrType (LLStructType [pt, env])

canGCLetable l = let rv = canGC  l in if rv then {- trace ("canGCL: " ++ show l) -} rv else rv
canGCCalled  v = let rv = canGCF v in if rv then {- trace ("canGCF: " ++ show v) -} rv else rv

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
{-

// * If a function body cannot trigger GC, then the in-params
//   need not be stored in gcroot slots. Reason: the params
//   are never live after a GC point, because there are no GC points.

fn-no-gc = { n : i32 => r : ref i32 =>
  let d = r^; in
    expect_i32 d;
    print_i32  n;
  end
}


// * If there are no GC points after a call returns a gc-ed pointer,
//   then the returned pointer need not be stored in a gcroot slot.
//   Reason: there are no further GC points
//           across which the pointer must be stored.

may-trigger-gc = {
  let x = (ref 0);
      d = x ^  ;
  in  d  end
}


no-gc-after-new = fn (to i32) {
  may-trigger-gc ! ;
  let n = (ref 0); in
    0
  end
}

// * If a pointer is dead before a GC can be triggered,
//   then it need not exist in a gcroot slot.
//
no-root-for-dead-ptrs = fn () {
  expect_i32(42)
  print_i32(deref(new 42))
  may-trigger-gc()
}

no-root-for-dead-ptrs = {
  expect_i32     42;
  let r = (ref 42);
      d = r ^     ;
  in
    print_i32 d;
    may-trigger-gc !;
  end
}



main = fn () {
  fn-no-gc(30, new 30)
  //no-gc-after-new()
  no-root-for-dead-ptrs()
}
-}

