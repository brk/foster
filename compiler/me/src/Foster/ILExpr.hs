{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns, RankNTypes,
             ScopedTypeVariables, NoMonoLocalBinds #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Compiler.Hoopl

import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.Boxes as Boxes

import Debug.Trace(trace)

import Foster.Base
import Foster.CFG
import Foster.CloConv
import Foster.TypeLL
import Foster.Letable

import Data.Maybe(fromMaybe)
import Data.IORef
import Data.Map(Map)
import Data.List(zipWith4, unzip3, or)
import qualified Data.Set as Set
import qualified Data.Map as Map(singleton, insertWith, lookup, empty, fromList,
                                 elems, keysSet, insert, union, findWithDefault)
import qualified Data.Text as T(pack, unpack)
import Control.Monad.State(evalStateT, get, put, StateT)

--------------------------------------------------------------------

-- | This pass does three things in prepration for handing of to LLVM:
-- |   #. Makes explicit all allocation and initialization of memory.
-- |   #. Inserts GC roots and live ranges using flow-based analysis.
-- |   #. Transforms from Hoopl's CFG representation to a block list.
-- |
-- | Unlike most of the previous passes, the invariants established
-- | by this portion of the compiler are left implicit.
-- |
-- |  * CCLetFuns are eliminated.
-- |  * ILTuples are eliminated, except for unit values.
-- |  * FnType _ _ _ FT_Func should have been eliminated
-- |    in favor of LLPtrType (LLStructType (FnType _ _ _ FT_Proc:_)).

-- ||||||||||||||||||||||||| Datatypes ||||||||||||||||||||||||||{{{
-- A program consists of top-level data types and mutually-recursive procedures.
data ILProgram = ILProgram [ILProcDef]
                           [LLExternDecl]
                           [DataType TypeLL]
                           SourceLines

data ILExternDecl = ILDecl String TypeLL
data ILProcDef = ILProcDef (Proc [ILBlock]) NumPredsMap [RootVar]
type NumPredsMap = Map BlockId Int

-- The standard definition of a basic block and its parts.
-- This is equivalent to MinCaml's make_closure ...
data ILBlock  = Block BlockEntryL [ILMiddle] ILLast
data ILMiddle = ILLetVal      Ident   (Letable TypeLL)
              | ILGCRootKill  LLVar    Bool -- continuation may GC
              | ILGCRootInit  LLVar    RootVar
              | ILTupleStore  [LLVar]  LLVar    AllocMemRegion
              deriving Show

-- Drop call-as-a-terminator and implicitly re-allow it as a letable value,
-- which better matches LLVM's IR. (If/when we support exception handling,
-- note that a possibly-exception-raising call remains a block terminator!)
data ILLast = ILRetVoid
            | ILRet      LLVar
            | ILBr       BlockId [LLVar]
            | ILCase     LLVar [(CtorId, BlockId)] (Maybe BlockId) (Occurrence TypeLL)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

prepForCodegen :: ModuleIL CCBody TypeLL -> IORef Uniq -> IO ILProgram
prepForCodegen m uref = do
    let decls = map (\(s,t) -> LLExternDecl s t) (moduleILdecls m)
    let dts = moduleILprimTypes m ++ moduleILdataTypes m
    procs <- mapM (deHooplize uref) (flatten $ moduleILbody m)
    return $ ILProgram procs decls dts (moduleILsourceLines m)
  where
   flatten :: CCBody -> [CCProc]
   flatten (CCB_Procs procs _) = procs

   deHooplize :: IORef Uniq -> Proc BasicBlockGraph' -> IO ILProcDef
   deHooplize uref p = do
     g' <- makeAllocationsExplicit (simplifyCFG $ procBlocks p) uref
     (g, liveRoots) <- insertSmartGCRoots uref g'
     let (cfgBlocks , numPreds) = flattenGraph g
     return $ ILProcDef (p { procBlocks = cfgBlocks }) numPreds liveRoots


makeAllocationsExplicit :: BasicBlockGraph' -> IORef Uniq -> IO BasicBlockGraph'
makeAllocationsExplicit bbgp uref = do
     let (bid,_) = bbgpEntry bbgp
     bb' <- rebuildGraphM bid (bbgpBody bbgp) explicate
     return $ bbgp { bbgpBody = bb' }
 where
  fresh str = do u <- modifyIORef uref (+1) >> readIORef uref
                 return (Ident (T.pack str) u)

  explicate :: forall e x. Insn' e x -> IO (Graph Insn' e x)
  explicate insn = case insn of
    (CCLabel   {}        ) -> return $ mkFirst $ insn
    (CCGCLoad _v fromroot) -> return $ mkMiddle $ insn
    (CCGCInit _ _v toroot) -> return $ mkMiddle $ insn
    (CCGCKill {}         ) -> return $ mkMiddle $ insn
    (CCLetVal id (ILAlloc v memregion)) -> do
            id' <- fresh "ref-alloc"
            let t = tidType v
            let info = AllocInfo t memregion "ref" Nothing Nothing "ref-allocator" NoZeroInit
            return $
              (mkMiddle $ CCLetVal id  (ILAllocate info)) <*>
              (mkMiddle $ CCLetVal id' (ILStore v (TypedId (LLPtrType t) id)))
    (CCLetVal id (ILTuple [] allocsrc)) -> return $ mkMiddle $ insn
    (CCLetVal id (ILTuple vs allocsrc)) -> do
            id' <- fresh "tup-alloc"
            let t = LLStructType (map tidType vs)
            let memregion = MemRegionGlobalHeap
            let info = AllocInfo t memregion "tup" Nothing Nothing "tup-allocator" NoZeroInit
            return $
              (mkMiddle $ CCLetVal id (ILAllocate info)) <*>
              (mkMiddle $ CCTupleStore vs (TypedId (LLPtrType t) id) memregion)
    (CCLetVal id (ILAppCtor t (CtorInfo cid _) vs)) -> do
            id' <- fresh "ctor-alloc"
            let tynm = ctorTypeName cid ++ "." ++ ctorCtorName cid
            let tag  = ctorSmallInt cid
            let t = LLStructType (map tidType vs)
            let obj = (TypedId (LLPtrType t) id' )
            let genty = LLPtrTypeUnknown
            let memregion = MemRegionGlobalHeap
            let info = AllocInfo t memregion tynm (Just tag) Nothing "ctor-allocator" NoZeroInit
            return $
              (mkMiddle $ CCLetVal id' (ILAllocate info)) <*>
              (mkMiddle $ CCTupleStore vs obj memregion)  <*>
              (mkMiddle $ CCLetVal id  (ILBitcast genty obj))
    (CCTupleStore   {}   ) -> return $ mkMiddle insn
    (CCLetVal  _id  _l   ) -> return $ mkMiddle insn
    (CCLetFuns ids clos)   -> makeClosureAllocationExplicit fresh ids clos
    (CCLast    cclast)     ->
          case cclast of
            (CCCont {}       ) -> return $ mkLast insn
            (CCCall _ _ _ _ _) -> return $ mkLast insn
            (CCCase {}       ) -> return $ mkLast insn

    -- Closures and their environments are mutually recursive; we'll tie
    -- the knot using mutation, as usual. For example, we'll translate::
    --          REC     c1 = Closure env=e1 proc=p1 captures=[c1]
    --                  c2 = Closure env=e2 proc=p2 captures=[c1,e1]
    -- to::
    --          LET e1     = ALLOC [typeOf c1]
    --          LET e2     = ALLOC [typeOf c1, typeOf e1.gen]
    --          LET c1     = ALLOC [procTy p1, typeOf e1.gen]
    --          LET c2     = ALLOC [procTy p2, typeOf e2.gen]
    --          LET e1.gen = BITCAST e1 to i8* // wait until all allocations are
    --          LET e2.gen = BITCAST e2 to i8* // done so bitcasts aren't stale.
    --          TUPLESTORE [p1, e1.gen] to c1
    --          TUPLESTORE [p2, e2.gen] to c2
    --          TUPLESTORE [c1]         to e1
    --          TUPLESTORE [c1, e1.gen] to e2
    -- Actually, we also need to genericize the environments for the proc types.
    --
    -- We split apart the allocation and initialization of closure environments
    -- on the off chance that one of the environments closes over one of its
    -- fellow closure values or environments.
    -- As a result, we must manually initialize env. storage to prevent the
    -- GC from seeing garbage if a GC is triggered before we fill in the envs.
    --
    -- In the common case, however, where the environments do *not* close
    -- over each other, we can make closure allocation slightly more efficient
    -- by directly initializing the environments. (TODO: how much more efficicient?)
    --
    -- Similarly, for the closures themselves, we can trade off between
    -- redundant loads and stores.
makeClosureAllocationExplicit fresh ids clos = do
  let generic_env_ptr_ty = LLPtrType (LLPrimInt I8)
  let generic_procty (LLProcType (_conc_env_ptr_type:rest) rt cc) =
                      LLProcType (generic_env_ptr_ty:rest) rt cc
  --let generic_fnty ty =
  --          let (FnType (_conc_env_ptr_type:rest) rt cc pf) = ty in
  --              (FnType (generic_env_ptr_ty:rest) rt cc pf)

  gen_proc_vars <- mapM (\procvar -> do
                          gen_proc_id <- fresh ".gen.proc"
                          return (TypedId (generic_procty $ tidType procvar)
                                           gen_proc_id)
                        ) (map closureProcVar clos)

  let gen id = TypedId generic_env_ptr_ty id
  let envids = map (tidIdent . closureEnvVar) clos
  env_gens <- mapM (\envid -> do fresh (T.unpack $ prependedTo ".gen"
                                                    (identPrefix envid))) envids
  let env_gen_map = Map.fromList $ zip envids env_gens
  let substGenEnv v = case Map.lookup (tidIdent v) env_gen_map of
                           Nothing -> v
                           Just id -> gen id
  -- TODO allocation source of clo?
  let envAllocsAndStores envid clo =
           let memregion = MemRegionGlobalHeap in
           let vs = map substGenEnv $ closureCaptures clo in
           let t = LLStructType (map tidType vs) in
           let envvar = TypedId (LLPtrType t) envid in
           let ealloc = ILAllocate (AllocInfo t memregion "env" Nothing Nothing
                                                "env-allocator" DoZeroInit) in
           (CCLetVal envid ealloc, CCTupleStore vs envvar memregion, envvar)
  let cloAllocsAndStores cloid gen_proc_var clo env_gen_id =
           let bitcast = ILBitcast (tidType gen_proc_var) (closureProcVar clo) in
           let memregion = MemRegionGlobalHeap in
           let vs = [gen_proc_var, gen env_gen_id] in
           let t  = LLStructType (map tidType vs) in
           let t' = fnty_of_procty (generic_procty (tidType (closureProcVar clo))) in
           let clovar = TypedId t' cloid in
           let calloc = ILAllocate (AllocInfo t memregion "clo" Nothing Nothing
                                                "clo-allocator" DoZeroInit) in
           (CCLetVal cloid calloc, [CCLetVal (tidIdent gen_proc_var) bitcast
                                   ,CCTupleStore vs clovar memregion])
  let (envallocs, env_tuplestores, envvars) = unzip3 $ zipWith  envAllocsAndStores envids clos
  let (cloallocs, clo_tuplestores         ) = unzip  $ zipWith4 cloAllocsAndStores ids gen_proc_vars clos env_gens
  let bitcasts = [CCLetVal envgen (ILBitcast generic_env_ptr_ty envvv)
                 | (envvv, envgen) <- zip envvars env_gens]
  return $ mkMiddles $ envallocs ++ cloallocs ++ bitcasts
                    ++ concat clo_tuplestores ++ env_tuplestores


--------------------------------------------------------------------

computeNumPredecessors elab blocks =
  foldr (\b m -> incrPredecessorsDueTo (lastNode b) m)
        startingMap blocks
 where
    -- The entry (i.e. postalloca) label will get an incoming edge in LLVM.
    startingMap = Map.singleton (blockId elab) 1

    incrPredecessorsDueTo :: Insn' O C -> NumPredsMap -> NumPredsMap
    incrPredecessorsDueTo insn' m =
        foldr (\tgt mm -> Map.insertWith (+) tgt 1 mm) m (block'TargetsOf insn')

--------------------------------------------------------------------

withGraphBlocks :: BasicBlockGraph' -> ( [ Block' ] -> a ) -> a
withGraphBlocks bbgp f =
   let jumpTo bg = case bbgpEntry bg of (bid, _) -> CCLast $ CCCont bid [] in
   f $ preorder_dfs $ mkLast (jumpTo bbgp) |*><*| bbgpBody bbgp

flattenGraph :: BasicBlockGraph' -> ( [ILBlock] , NumPredsMap )
flattenGraph bbgp =
   withGraphBlocks bbgp (\blocks ->
     ( map (deHooplizeBlock (bbgpRetK bbgp)) blocks
     , computeNumPredecessors (bbgpEntry bbgp) blocks ))
 where
  deHooplizeBlock :: BlockId -> Block Insn' C C -> ILBlock
  deHooplizeBlock retk b =
         let (f, ms, l) = blockSplit b in
         let (lastmids, last) = fin l in
         Block (frs f) (concatMap midmany (blockToList ms) ++ lastmids) last
   where
     midmany :: Insn' O O -> [ILMiddle]
     midmany insn = [mid insn]

     mid :: Insn' O O -> ILMiddle
     mid (CCLetVal id letable)    = ILLetVal   id  letable
     mid (CCGCLoad v   fromroot)  = ILLetVal (tidIdent v) (ILDeref (tidType v) fromroot)
     mid (CCGCInit _ src toroot)  = ILGCRootInit src toroot
     mid (CCGCKill (Enabled cgc) root) = ILGCRootKill root cgc
     mid (CCGCKill Disabled     _root) = error $ "Invariant violated: saw disabled root kill pseudo-insn!"
     mid (CCTupleStore vs tid r)  = ILTupleStore vs tid r
     mid (CCLetFuns ids closures) = error $ "Invariant violated: CCLetFuns should have been eliminated!"

     frs :: Insn' C O -> BlockEntryL
     frs (CCLabel be) = be

     fin :: Insn' O C -> ([ILMiddle], ILLast)
     fin (CCLast (CCCont k vs)       ) = ([], cont k vs)
     fin (CCLast (CCCase v bs mb occ)) = ([], ILCase v bs mb occ)
     -- [[f k vs]] ==> let x = f vs in [[k x]]
     fin (CCLast (CCCall k t id v vs)) = ([ILLetVal id (ILCall t v vs)]
                                         , cont k [TypedId t id] )
     -- Translate continuation application to br or ret, as appropriate.
     cont k vs =
        case (k == retk, vs) of
             (True,  [] ) -> ILRetVoid
             (True,  [v]) -> ILRet   v
             (True,   _ ) -> error $ "ILExpr.hs:No support for multiple return values yet\n" ++ show vs
             (False,  _ ) -> ILBr k vs

-- ||||||||||||||||||||||||| CFG Simplification  ||||||||||||||||{{{
simplifyCFG :: BasicBlockGraph' -> BasicBlockGraph'
simplifyCFG bbgp =
   -- Because we do a depth-first search, "renaming" blocks are guaranteed
   -- to be adjacent to each other in the list.
   withGraphBlocks bbgp (\blocks ->
       bbgp { bbgpBody = graphOfClosedBlocks $ mergeCallNamingBlocks blocks $
                             computeNumPredecessors (bbgpEntry bbgp) blocks } )

-- This little bit of unpleasantness is needed to ensure that we
-- don't need to create gcroot slots for the phi nodes corresponding
-- to blocks inserted from using CPS-like calls.
mergeCallNamingBlocks :: [Block' ] -> NumPredsMap -> [ Block' ]
mergeCallNamingBlocks blocks numpreds = go Map.empty [] blocks
  where
     go !subst !acc !blocks =
       case blocks of
         [] -> finalize acc subst
         [b] -> go subst (b:acc) []
         (x:y:zs) ->
            case mergeAdjacent subst (blockSplitTail x)
                                     (blockSplitHead y) of
              Just (m,s) -> go s        acc  (m:zs)
              Nothing    -> go subst (x:acc) (y:zs)

     mergeAdjacent :: Map LLVar LLVar -> (Block Insn' C O, Insn' O C)
                                      -> (Insn' C O, Block Insn' O C)
                                      -> Maybe (Block Insn' C C, Map LLVar LLVar)
     mergeAdjacent subst (xem, xl) (CCLabel (yb,yargs), yml) =
       case (yargs, xl) of
         ([yarg], CCLast (CCCall cb t _id v vs)) | cb == yb ->
             if Map.lookup yb numpreds == Just 1
                 then Just ((xem `blockSnoc`
                              (CCLetVal (tidIdent yarg) (ILCall t v vs)))
                                 `blockAppend` yml, subst)
                 else Nothing
         (_, CCLast (CCCont cb   avs))          | cb == yb ->
             if Map.lookup yb numpreds == Just 1
                 then case (length yargs == length avs, yb) of
                        (True, _) ->
                          let subst' = Map.union subst (Map.fromList $ zip yargs avs) in
                          Just ((xem `blockAppend` yml), subst' )
                        (False, ("postalloca",_)) ->
                          Nothing
                        (False, _) ->
                          error $ "Continuation application not passing same # of arguments "
                               ++ "as expected by the continuation!\n"
                               ++ show avs ++ "\n" ++ show yargs
                               ++ "\n" ++ show cb ++ " // " ++ show yb
                 else Nothing
         _ -> Nothing

     finalize revblocks subst =
         let s v = Map.findWithDefault v v subst in
         map (mapBlock' $ substIn s) (reverse revblocks)

     substIn :: VarSubstFor (Insn' e x)
     substIn s insn  = case insn of
          (CCLabel   {}        ) -> insn
          (CCGCLoad  v fromroot) -> CCGCLoad        (s v) (s fromroot)
          (CCGCInit vr v toroot) -> CCGCInit (s vr) (s v) (s   toroot)
          (CCGCKill enabld root) -> CCGCKill enabld (s root)
          (CCTupleStore vs  v r) -> CCTupleStore (map s vs) (s v) r
          (CCLetVal  id letable) -> CCLetVal id $ substVarsInLetable s letable
          (CCLetFuns ids fns   ) -> CCLetFuns ids $ map (substForInClo s) fns
          (CCLast    cclast    ) -> case cclast of
              (CCCont b vs)        -> CCLast (CCCont b (map s vs))
              (CCCall b t id v vs) -> CCLast (CCCall b t id (s v) (map s vs))
              (CCCase v cs mb occ) -> CCLast (CCCase (s v) cs mb occ)

     substForInClo :: VarSubstFor Closure
     substForInClo s clo =
       clo { closureCaptures = (map s (closureCaptures clo)) }

type VarSubstFor a = (LLVar -> LLVar) -> a -> a
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| GC Root Insertion |||||||||||||||||||||||{{{

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
--

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

type GCRootsForVariables = Map LLVar RootVar
type VariablesForGCRoots = Map RootVar LLVar

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
    CCLabel (bid, vs)             -> do (inits, gcr' ) <- mapFoldM' vs gcr maybeRootInitializer
                                        return (mkFirst insn <*> catGraphs inits <*> mkMiddles [
                                                CCGCKill Disabled root | root <- Map.elems gcr' ]
                                                                                      , gcr' )
    CCGCLoad  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCGCInit  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCGCKill  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCTupleStore vs v r           -> do trace ("isGCable " ++ show v ++ " :" ++ show (isGCable v)) $
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
    CCGCKill  (Enabled _)  root   -> do iflive root $ mkMiddle $ insn
    CCGCKill  Disabled    _root   -> do return emptyGraph -- TODO remove this
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

fnty_of_procty pt@(LLProcType (env:args) rets cc) =
      LLPtrType (LLStructType [pt, env])

canGCLetable l = let rv = canGC  l in if rv then {- trace ("canGCL: " ++ show l) -} rv else rv
canGCCalled  v = let rv = canGCF v in if rv then {- trace ("canGCF: " ++ show v) -} rv else rv

-- Filter out non-pointer-typed variables from live set.
gcable vs = Set.fromList $ filter isGCable vs
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
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{
showILProgramStructure :: ILProgram -> Doc
showILProgramStructure (ILProgram procdefs _decls _dtypes _lines) =
    vcat $ map showProcStructure procdefs
  where
    showProcStructure (ILProcDef proc _ roots) =
        text (show $ procIdent proc) <+> (text "//")
            <+> (text $ show $ map procVarDesc (procVars proc))
            <+> (text "==>") <+> (text $ show $ procReturnType proc)
          <$> text (unlines (map show roots))
          <$> vcat (map showBlock $ procBlocks proc)
          <$> text "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"

    procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

    showBlock (Block blockid mids last) =
            text (show blockid)
        <$> text (concatMap (\m -> "\t" ++ show m ++ "\n") mids)
        <$> text (show last ++ "\n\n")

instance Show ILLast where
  show (ILRetVoid     ) = "ret void"
  show (ILRet v       ) = "ret " ++ show v
  show (ILBr  bid args) = "br " ++ show bid ++ " , " ++ show args
  show (ILCase v _arms _def _occ) = "case(" ++ show v ++ ")"
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

