{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns, RankNTypes,
             ScopedTypeVariables, NoMonoLocalBinds, Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Prelude hiding ((<$>), (<*>))

import Compiler.Hoopl

import Text.PrettyPrint.ANSI.Leijen

import Foster.Base
import Foster.Kind
import Foster.Config
import Foster.CFG
import Foster.CloConv
import Foster.TypeLL
import Foster.Letable
import Foster.GCRoots
import Foster.Avails
import Foster.Output(putDocLn)
import Foster.MainOpts (getNonMovingGC, getNoGcAtAll,
                        getStripGCKills, getNoPreAllocOpt)
import Data.Map(Map)
import Data.List(zipWith4, foldl' )
import Data.Maybe(maybeToList, fromMaybe)
import Control.Monad.State(evalState, execState, State, get, gets, modify)
import Control.Monad.IO.Class(liftIO)
import qualified Data.Set as Set(toList, map, union, unions, difference,
                                 member, Set, empty, size, fromList, insert)
import qualified Data.Map as Map(singleton, insertWith, lookup, empty, fromList,
                                 adjust, insert, findWithDefault, toList)
import qualified Data.Text as T(pack, unpack, isInfixOf)
import qualified Data.Graph as Graph(stronglyConnComp)
import Data.Graph(SCC(..))

--import qualified Criterion.Measurement as Criterion(secs)

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
                           [ToplevelBinding TypeLL]
                           [LLExternDecl]
                           [DataType TypeLL]
                           SourceLines

data ILExternDecl = ILDecl String TypeLL
data ILProcDef = ILProcDef (Proc [ILBlock]) NumPredsMap [RootVar]
type NumPredsMap = Map BlockId Int

-- The standard definition of a basic block and its parts.
-- This is equivalent to MinCaml's make_closure ...
data ILBlock  = Block BlockEntryL [ILMiddle] ILLast
data ILMiddle = ILLetVal      Ident   (Letable TypeLL) MayGC
              | ILGCRootKill  LLVar    Bool -- continuation may GC
              | ILGCRootInit  LLVar    RootVar
              | ILTupleStore  [LLVar]  LLVar    AllocMemRegion
              | ILRebindId    Ident    LLVar
              deriving Show

-- Drop call-as-a-terminator and implicitly re-allow it as a letable value,
-- which better matches LLVM's IR. (If/when we support exception handling,
-- note that a possibly-exception-raising call remains a block terminator!)
data ILLast = ILRetVoid
            | ILRet      LLVar
            | ILBr       BlockId [LLVar]
            | ILCase     LLVar [((CtorId, CtorRepr), BlockId)] (Maybe BlockId)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- TODO last-stand optimizations
--        * reuse avails infrastructure for inlining occ bindings
--        * do liveness to eliminate dead bindings
--          * should be done before allocations are made explicit,
--            since otherwise we have to account for tuple stores not being "real" uses.
--          * but maybe after cfg simplification...

instance Pretty (Set.Set Ident) where pretty s = text "{" <> list (map pretty (Set.toList s)) <> text "}"

prepForCodegen :: ModuleIL CCBody TypeLL -> MayGCConstraints -> Compiled (ILProgram, [Proc BasicBlockGraph' ])
prepForCodegen m mayGCconstraints0 = do
    let decls = map (\(s,t, isForeign) -> LLExternDecl s t isForeign) (moduleILdecls m)
    let dts = moduleILprimTypes m ++ moduleILdataTypes m
    let CCBody hprocs valbinds = moduleILbody m
    (_ep_time, combined) <- ioTime $ mapM explicateProc hprocs
    let (aprocs, preallocprocs) = unzip combined

    let mayGCmap = resolveMayGC mayGCconstraints0 aprocs

    whenDumpIR "maygc" $ do
      putDocLn $ text "resolved maygc:" <$>
         indent 4 ( pretty (Map.toList $ mapAllFromList
                                   [(mgc,f) | (f,mgc) <- Map.toList mayGCmap]) )

    (_dh_time, procs) <- ioTime $ mapM (deHooplize mayGCmap) aprocs

    --liftIO $ putDocLn $ text "explicateProcs time: " <> text (Criterion.secs ep_time)
    --liftIO $ putDocLn $ text "deHooplize/gcr time: " <> text (Criterion.secs dh_time)

    return $ (ILProgram procs valbinds decls dts (moduleILsourceLines m),
              preallocprocs)
  where
   explicateProc p = do
     let failIfUsesGC = T.isInfixOf (T.pack "mustnotalloc_") (identPrefix $ procIdent p)

     flagVals <- gets ccFlagVals
     (_pa_time, g0) <- ioTime $ if getNoPreAllocOpt flagVals
                                  then return $ simplifyCFG $ procBlocks p
                                  else runPreAllocationOptimizations (simplifyCFG $ procBlocks p)
     (_ae_time, g') <- ioTime $ makeAllocationsExplicit g0 failIfUsesGC (procIdent p)
     --liftIO $ putDocLn $ text "  makeAllocExplicit time: " <> text (Criterion.secs ae_time)

     return (p { procBlocks = g' }, p { procBlocks = g0 })

   deHooplize :: Map Ident MayGC -> Proc BasicBlockGraph' -> Compiled ILProcDef
   deHooplize mayGCmap p = do

     flagVals <- gets ccFlagVals

     (g , liveRoots) <- if getNoGcAtAll flagVals
        then do
          return (procBlocks p, [])
        else do
          wantedFns <- gets ccDumpFns
          (g', liveRoots) <- insertSmartGCRoots (procIdent p) (procBlocks p) mayGCmap (want p wantedFns)
          --(g', liveRoots) <- insertDumbGCRoots' (procBlocks p) (want p wantedFns)
          g <- if getStripGCKills flagVals
                then stripKills g'
                else return     g'
          return (g, liveRoots)

     let (cfgBlocks , numPreds) = flattenGraph g mayGCmap (getNonMovingGC flagVals)
     return $ ILProcDef (p { procBlocks = cfgBlocks }) numPreds liveRoots

   want p wantedFns = T.unpack (identPrefix (procIdent p)) `elem` wantedFns

-- ||||||||||||||||||||||||| Allocation Explication  ||||||||||||{{{
makeAllocationsExplicit :: BasicBlockGraph' -> Bool -> Ident -> Compiled BasicBlockGraph'
makeAllocationsExplicit bbgp prohibitAllocations procId = do
     bb' <- rebuildGraphM Nothing (bbgpBody bbgp) explicate
     return $ bbgp { bbgpBody = bb' }
 where
  explicate :: forall e x. Insn' e x -> Compiled (Graph Insn' e x)
  explicate insn = case insn of
    (CCLabel   {}        ) -> return $ mkFirst $ insn
    (CCGCLoad  {}        ) -> return $ mkMiddle $ insn
    (CCGCInit  {}        ) -> return $ mkMiddle $ insn
    (CCGCKill  {}        ) -> return $ mkMiddle $ insn
    (CCLetVal id (ILAlloc v memregion sr)) ->
      if prohibitAllocations
        then compiledThrowE [text "Unable to eliminate allocations from " <> pretty procId]
        else do
            id' <- ccFreshId (T.pack "ref-alloc")
            let t = tidType v
            let info = AllocInfo t memregion "ref" Nothing Nothing ("ref-allocator:"++show t) NoZeroInit
            return $
              (mkMiddle $ CCLetVal id  (ILAllocate info sr)) <*>
              (mkMiddle $ CCLetVal id' (ILStore v (TypedId (LLPtrType t) id)))
    (CCLetVal _id (ILTuple _kind [] _allocsrc)) -> return $ mkMiddle $ insn
    (CCLetVal _id (ILTuple KindAnySizeType _vs _allocsrc)) -> do
            return $ mkMiddle $ insn
    (CCLetVal  id (ILTuple KindPointerSized vs allocsrc)) ->
      if prohibitAllocations
        then compiledThrowE [text "Unable to eliminate allocations from " <> pretty procId]
        else do
            let t = LLStructType (map tidType vs)
            let memregion = MemRegionGlobalHeap
            let info = AllocInfo t memregion "tup" Nothing Nothing ("tup-allocator:"++show vs) NoZeroInit
            return $
              (mkMiddle $ CCLetVal id (ILAllocate info (rangeOf allocsrc))) <*>
              (mkMiddle $ CCTupleStore vs (TypedId (LLPtrType t) id) memregion)
    (CCLetVal id (ILAppCtor genty (_cid, CR_Transparent) [v] _sr)) -> do
            return $
              (mkMiddle $ CCLetVal id  (ILBitcast genty v))
    (CCLetVal id (ILAppCtor _genty (_cid, CR_TransparentU) [v] _sr)) -> do
            return $
              (mkMiddle $ CCRebindId (text "TransparentU") (TypedId (tidType v) id) v)
    (CCLetVal id (ILAppCtor genty (cid, repr) vs sr)) -> do
      if prohibitAllocations
        then compiledThrowE [text "Unable to eliminate allocations from " <> pretty procId]
        else do
            id' <- ccFreshId (T.pack "ctor-alloc")
            let tynm = ctorTypeName cid ++ "." ++ ctorCtorName cid
            let t = LLStructType (map tidType vs)
            let obj = (TypedId (LLPtrType t) id' )
            let memregion = MemRegionGlobalHeap
            let info = AllocInfo t memregion tynm (Just repr) Nothing ("ctor-allocator:"++show cid) NoZeroInit
            return $
              (mkMiddle $ CCLetVal id' (ILAllocate info sr)) <*>
              (mkMiddle $ CCTupleStore vs obj memregion)  <*>
              (mkMiddle $ CCLetVal id  (ILBitcast genty obj))
    (CCTupleStore   {}   ) -> return $ mkMiddle insn
    (CCLetVal  _id  _l   ) -> return $ mkMiddle insn
    (CCLetFuns ids clos)   ->
      if prohibitAllocations
        then compiledThrowE [text "Unable to eliminate allocations from " <> pretty procId]
        else makeClosureAllocationExplicit ids clos
    (CCRebindId     {}   ) -> return $ mkMiddle insn
    (CCLast         {}   ) -> return $ mkLast insn

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
    -- by directly initializing the environments. (TODO: how much more efficient?)
    --
    -- Similarly, for the closures themselves, we can trade off between
    -- redundant loads and stores.
makeClosureAllocationExplicit ids clos = do
  let generic_env_ptr_ty = LLPtrType (LLPrimInt I8)
  let generic_procty (LLProcType (_conc_env_ptr_type:rest) rt cc) =
                      LLProcType (generic_env_ptr_ty:rest) rt cc
      generic_procty othertype = error $ "ILExpr.hs: generic_procty called for " ++ show othertype

  gen_proc_vars <- mapM (\procvar -> do
                          gen_proc_id <- ccFreshId (T.pack ".gen.proc")
                          return (TypedId (generic_procty $ tidType procvar)
                                           gen_proc_id)
                        ) (map closureProcVar clos)

  let gen id = TypedId generic_env_ptr_ty id
  let envids = map (tidIdent . closureEnvVar) clos
  env_gens <- mapM (\envid -> do ccFreshId (prependedTo ".gen"
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
                          ("env-allocator:"++show (tidIdent (closureProcVar clo))) DoZeroInit)
                          (MissingSourceRange "env-allocator") in
           (CCLetVal envid ealloc , CCTupleStore vs envvar memregion, envvar)
  let cloAllocsAndStores cloid gen_proc_var clo env_gen_id =
           let bitcast = ILBitcast (tidType gen_proc_var) (closureProcVar clo) in
           let memregion = MemRegionGlobalHeap in
           let vs = [gen_proc_var, gen env_gen_id] in
           let t  = LLStructType (map tidType vs) in
           let t' = fnty_of_procty (generic_procty (tidType (closureProcVar clo))) in
           let clovar = TypedId t' cloid in
           let calloc = ILAllocate (AllocInfo t memregion "clo" Nothing Nothing
                         ("clo-allocator:"++show (tidIdent (closureProcVar clo))) DoZeroInit)
                         (MissingSourceRange "clo-allocator") in
           (CCLetVal cloid calloc
           , [CCLetVal (tidIdent gen_proc_var) bitcast
             ,CCTupleStore vs clovar memregion])
  let (envallocs, env_tuplestores, envvars) = unzip3 $ zipWith  envAllocsAndStores envids clos
  let (cloallocs, clo_tuplestores         ) = unzip  $ zipWith4 cloAllocsAndStores ids gen_proc_vars clos env_gens
  let bitcasts = [CCLetVal envgen (ILBitcast generic_env_ptr_ty envvv)
                 | (envvv, envgen) <- zip envvars env_gens]
  return $ mkMiddles $ envallocs ++ cloallocs ++ bitcasts
                    ++ concat clo_tuplestores ++ env_tuplestores
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- MayGCConstraints is essentially two disjoint maps, merged into one.
-- There are functions which are definitely MayGC, and functions which
-- are of unknown GC-status, along with the functions they call.
-- Resolving the constraints means propagating the known-MayGC values
-- up through the call graph. Any function which does not get thusly
-- tainted can be assumed to not GC.

resolveMayGC :: MayGCConstraints -> [ Proc BasicBlockGraph' ] -> MayGCMap
resolveMayGC constraints procs =
  -- Compute the strongly-connected components of the MayGC constraint graph;
  -- nodes are (proc, maygc) pairs, and edges are from the MayGCConstraints map.
  let scc = Graph.stronglyConnComp [ ((p,m), procIdent p, Set.toList s)
                | p <- procs, (m,s) <- maybeToList $
                                            Map.lookup (procIdent p) constraints
            ] in
  -- Traverse the SCCs, bottom up, propagating constraints.
  foldl' go Map.empty scc
    where go :: (MayGCMap -> SCC (Proc BasicBlockGraph' , MayGC) -> MayGCMap)
          go m (AcyclicSCC (p,mgc)) = let m' = collectMayGCConstraints_Proc p $
                                                (Map.insert (procIdent p) mgc m)
                                      in Map.adjust unknownMeansNoGC (procIdent p) m'
          go m (CyclicSCC [(p,mgc)])= let m' = collectMayGCConstraints_Proc p $
                                                (Map.insert (procIdent p) mgc m)
                                      in Map.adjust unknownMeansNoGC (procIdent p) m'
          go m (CyclicSCC pms) =
            let (ps,mgcs) = unzip pms in
            -- Start with a conservative estimate for the whole SCC's behavior.
            let mgc = joinMayGCs mgcs in
            let m'0 = foldl' (\m p -> Map.insert (procIdent p) mgc m)    m    ps in
            let m's = foldl' (\m p -> collectMayGCConstraints_Proc p  m) m'0  ps in
            foldl' (\m p -> Map.adjust unknownMeansNoGC (procIdent p) m) m's  ps

          joinMayGCs mgcs = foldl1 joinMayGC mgcs

          joinMayGC MayGC _ = MayGC
          joinMayGC _ MayGC = MayGC
          joinMayGC WillNotGC WillNotGC = WillNotGC
          joinMayGC WillNotGC     (GCUnknown a)  = GCUnknown a
          joinMayGC (GCUnknown a) WillNotGC      = GCUnknown a
          joinMayGC (GCUnknown a) (GCUnknown b)  = GCUnknown (a ++ "+" ++ b)

-- At this point, all allocation has been made explicit;
-- if a known function has no constraints that imply it will GC,
-- then we can conclude that it will not GC.
unknownMeansNoGC (GCUnknown _) = WillNotGC
unknownMeansNoGC other         = other

-- Individual calls should be pessimistically assumed to GC.
unknownMeansMayGC (GCUnknown _) = MayGC
unknownMeansMayGC other         = other

type MayGCMap = Map Ident MayGC

collectMayGCConstraints_Proc :: Proc BasicBlockGraph' -> MayGCMap -> MayGCMap
collectMayGCConstraints_Proc proc m = foldGraphNodes go (bbgpBody $ procBlocks proc) m
  where
        go :: forall e x. Insn' e x -> MayGCMap -> MayGCMap
        go (CCLabel        {}   ) m = m
        go (CCGCLoad       {}   ) m = m
        go (CCGCInit       {}   ) m = m
        go (CCGCKill       {}   ) m = m
        go (CCTupleStore   {}   ) m = m
        go (CCRebindId     {}   ) m = m
        go (CCLast _ (CCCont {} ) ) m = m
        go (CCLast _ (CCCase {} ) ) m = m

        go (CCLetFuns  _ _clos) _ = error $ "collecMayGCConstraints saw CCLetClosures!"

        go (CCLetVal x (ILBitcast t v)) m = case Map.lookup (tidIdent v) m of
                                               Nothing  -> withGC m $ unknownMeansMayGC (canGC m (ILBitcast t v))
                                               Just mgc -> Map.insert x mgc m
        go (CCLetVal _  letable)        m = withGC m $ unknownMeansMayGC (canGC m letable)

        withGC m WillNotGC     = m
        withGC m MayGC         = Map.adjust (\_ -> MayGC) (procIdent proc) m
        withGC m (GCUnknown _) = m
--------------------------------------------------------------------

computeNumPredecessors elab blocks =
  foldr (\b m -> incrPredecessorsDueTo (lastNode b) m)
        startingMap blocks
 where
    -- The entry (i.e. postalloca) label will get an incoming edge in LLVM.
    startingMap = Map.singleton (fst elab) 1

    incrPredecessorsDueTo :: Insn' O C -> NumPredsMap -> NumPredsMap
    incrPredecessorsDueTo insn' m =
        foldr (\tgt mm -> Map.insertWith (+) tgt 1 mm) m (block'TargetsOf insn')

--------------------------------------------------------------------

withGraphBlocks :: BasicBlockGraph' -> ( [ Block' ] -> a ) -> a
withGraphBlocks bbgp f =
   let jumpTo bg = case bbgpEntry bg of (bid, _) -> CCLast bid $ CCCont bid [] in
   f $ preorder_dfs $ mkLast (jumpTo bbgp) |*><*| bbgpBody bbgp

flattenGraph :: BasicBlockGraph' -> MayGCMap -> Bool -> ( [ILBlock] , NumPredsMap )
flattenGraph bbgp mayGCmap assumeNonMovingGC = -- clean up any rebindings from gc root optz.
   withGraphBlocks (simplifyCFG bbgp) (\blocks ->
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
     --midmany (CCGCKill Disabled     _root) = error $ "Invariant violated: saw disabled root kill pseudo-insn!"
     midmany (CCGCKill Disabled     _root) = []
     midmany (CCGCKill (Enabled cgc) roots) = [ILGCRootKill root cgc | root <- Set.toList roots]
     midmany insn = [mid insn]

     mid :: Insn' O O -> ILMiddle
     mid (CCLetVal id letable   ) = ILLetVal id letable (canGC mayGCmap letable)
     mid (CCGCLoad v root orig  ) =
        if assumeNonMovingGC
          then ILRebindId (tidIdent v) orig
          else ILLetVal   (tidIdent v) (ILDeref (tidType v) root) WillNotGC
     mid (CCGCInit _ src toroot)  = ILGCRootInit src toroot
     mid (CCTupleStore vs tid r)  = ILTupleStore vs tid r
     mid (CCRebindId {}         ) = error $ "Invariant violated: CCRebindId not eliminated!"
     mid (CCLetFuns {}          ) = error $ "Invariant violated: CCLetFuns should have been eliminated!"
     mid (CCGCKill  {}          ) = error $ "Invariant violated: GCKill should have been handled by `midmany`..."

     frs :: Insn' C O -> BlockEntryL
     frs (CCLabel be) = be

     fin :: Insn' O C -> ([ILMiddle], ILLast)
     fin (CCLast _ (CCCont k vs)   ) = ([], cont k vs)
     fin (CCLast _ (CCCase v bs mb)) = ([], ILCase v bs mb)

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
   withGraphBlocks bbgp (\blocks ->
       bbgp { bbgpBody = graphOfClosedBlocks $ eliminateRebindings blocks } )

    where
     eliminateRebindings blocks =
         let elimRebindingsInBlock block = mapBlockM substIn' block in
         evalState (mapM elimRebindingsInBlock blocks) Map.empty

     -- | Monadic version of the strict mapBlock3' from Hoopl.
     mapBlockM :: Monad m => (forall e x. i e x -> m [i e x]) -> Block i C C -> m (Block i C C)
     mapBlockM a b = do
       let (f, ms, l) = unblock ( blockSplit b )
       f's  <- a f
       ms'  <- mapM a ms
       l's  <- a l
       case (f's, l's) of
          ([f'] , [l']) ->
            return $ blockJoin f' (blockFromList $ concat ms' ) l'
          _ ->
             error $ "mapBlockM found wrong number of blocks"
      where unblock (f, ms_blk, l) = (f, blockToList ms_blk, l)

     substIn' :: Insn' e x -> State (Map LLVar LLVar) [Insn' e x]
     substIn' (CCRebindId _ v1 v2) = do modify (Map.insert v1 v2)
                                        return []
     substIn' insn = do
       subst <- get
       let s v = Map.findWithDefault v v subst
       return [substIn s insn]

     substIn :: VarSubstFor (Insn' e x)
     substIn s insn  = case insn of
          (CCLabel   {}        ) -> insn
          (CCGCLoad  v root org) -> CCGCLoad        (s v) (s   root) (s org)
          (CCGCInit vr v toroot) -> CCGCInit (s vr) (s v) (s toroot)
          (CCGCKill enabld roots) -> CCGCKill enabld (Set.map s roots)
          (CCTupleStore vs  v r) -> CCTupleStore (map s vs) (s v) r
          (CCLetVal id letable ) -> CCLetVal id (substVarsInLetable s letable)
          (CCLetFuns ids fns   ) -> CCLetFuns ids $ map (substForInClo s) fns
          (CCRebindId {}       ) -> error $ "Unexpected rebinding!"
          (CCLast l  cclast    ) -> case cclast of
              CCCont b vs          -> CCLast l (CCCont b (map s vs))
              CCCase v cs mb       -> CCLast l (CCCase (s v) cs mb)

     substForInClo :: VarSubstFor Closure
     substForInClo s clo =
       clo { closureCaptures = (map s (closureCaptures clo)) }


type VarSubstFor a = (LLVar -> LLVar) -> a -> a
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data TC = TCtup        [LLVar]
        | TCtor CtorId [LLVar]

-- TODO populate availTuples and availTuples' when binding ILTuple
--      when rewriting occ nodes, check if we can peek through (via availTuples)
-- TODO we can also use availTuples' to avoid redundant allocations of ctors

-- |||||||||||| Pre-allocation redundancy elimination |||||||||||{{{
data Avails = Avails { availSubst    :: AvailMap LLVar LLVar
                     , availTuples   :: AvailMap Ident [LLVar]
                     --, availTuples'  :: AvailMap [LLVar] LLVar
                     , availOccs     :: AvailMap (LLVar, Occurrence TypeLL) LLVar
                     }  -- note: AvailMap works here because LLVar == LLRootVar...
                     deriving Show

--instance Show Avails where show a = show (pretty a)
--instance Pretty Avails where
--  pretty (Avails uk lr fr) = text "(Avails unkilledRoots=" <> text (show uk)
--                         <+> text "loadedRoots="   <> text (show uk)
--                         <+> text "loadsForRoots=" <> text (show $ Map.map (Set.map tidIdent) fr) <> text ")"

availsXfer :: FwdTransfer Insn' Avails
availsXfer = mkFTransfer3 go go (distributeXfer availsLattice go)
  where
    go :: Insn' e x -> Avails -> Avails
    go (CCLetVal id (ILOccurrence ty v occ)) f = f { availOccs = insertAvailMap (v, occ) (TypedId ty id) (availOccs f) }
    go (CCLetVal id (ILTuple _kind vs _)) f = f { availTuples = insertAvailMap id vs (availTuples f) }
    go (CCRebindId _ v1 v2 ) f = f { availSubst = insertAvailMap v1 v2 (availSubst f) }
    go _ f = f

availsRewrite :: forall m. FuelMonad m => FwdRewrite m Insn' Avails
availsRewrite = mkFRewrite d
  where
    d :: Insn' e x -> Avails -> m (Maybe (Graph Insn' e x))

    d (CCLetVal id (ILOccurrence ty v occ)) a =
      case lookupAvailMap (v, occ) (availOccs a) of
        -- If we have  t = (v0, v1)
        --             ...
        --             o0 = occ t [0]
        --             o1 = occ t [0]
        -- we would like to rewrite it to
        --             t = (v0, v1)
        --             ...
        --             o0 = occ t [0]
        --             o1 = o0         <<<<
        -- This rewrite is triggered by (for example) test-vlist.
        (v' : _) -> return $ Just (mkMiddle $ CCRebindId (text "occ-reuse") (TypedId ty id) v' )
        
        [] -> case (occ, lookupAvailMap (tidIdent v) (availTuples a)) of
                -- If we have  t = (v0, v1)
                --             ...
                --             o0 = occ t [0]
                -- we would like to rewrite it to
                --             t = (v0, v1)
                --             ...
                --             o0 = v0   <<<<
                ([(n, _)], [vs]) -> let vk = vs !! n in
                                    --trace ("replacing occ " ++ show (tidIdent v) ++ "&" ++ show n ++ " with " ++ show vk)
                                      (return $ Just $ mkMiddle $ CCRebindId (text "static tuple lookup")
                                                                             (TypedId (tidType vk) id)  vk)
                _ -> return Nothing

    d _ _ = return Nothing

    {-
    s a v = case lookupAvailMap v (availSubst a) of
              [    ] -> v
              [ v' ] -> v'
              [ _v1, _v2 ] -> trace ("CFGOptimizations.hs: OOPS, " ++ show v ++ " mapped to two vars! choosing neither") v
              s -> error $ "GCRoots.hs: Expected avail. subst to map " ++ show v
                           ++ " to zero or one variables, but had " ++ show s
-}
runAvails :: BasicBlockGraph' -> Compiled BasicBlockGraph'
runAvails bbgp = do
         uref <- gets ccUniqRef
         liftIO $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M BasicBlockGraph'
    go bbgp = do
        let ((_,blab), _) = bbgpEntry bbgp
        let init = Avails emptyAvailMap emptyAvailMap emptyAvailMap
        (body' , _, _) <- analyzeAndRewriteFwd fwd (JustC [bbgpEntry bbgp])
                                                           (bbgpBody bbgp)
                           (mapSingleton blab init)
        return bbgp { bbgpBody = body' }

    --__fwd = debugFwdTransfers trace showing (\_ _ -> True) fwd
    --_fwd = debugFwdJoins trace (\_ -> True) fwd
    fwd = FwdPass { fp_lattice  = availsLattice
                  , fp_transfer = availsXfer
                  , fp_rewrite  = availsRewrite
                  }

--showing :: Insn' e x -> String
--showing insn = show (pretty insn)

availsLattice :: DataflowLattice Avails
availsLattice = DataflowLattice
  { fact_name = "Availables"
  , fact_bot  = Avails botAvailMap botAvailMap botAvailMap
  , fact_join = add
  }
    where add _lab (OldFact (Avails os ot ox)) (NewFact (Avails ns nt nx))
                 = let r = (ch, Avails js jt jx)
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
              (js, c1) = os `intersectAvailMap` ns
              (jt, c2) = ot `intersectAvailMap` nt
              (jx, c3) = ox `intersectAvailMap` nx
              ch = changeIf (c1 || c2 || c3)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

freeIdentsL :: Letable TypeLL -> [Ident]
freeIdentsL letable = map tidIdent $ (freeTypedIds letable :: [LLVar])

freeIdentsC :: Closure -> [Ident]
freeIdentsC (Closure procvar envvar captvars _) = map tidIdent (procvar:envvar:captvars)

-- |||||||||||||||||||| Liveness ||||||||||||||||||||||||||||||||{{{
type Live = Set.Set Ident

liveLattice :: DataflowLattice Live
liveLattice = DataflowLattice
  { fact_name = "Live variables"
  , fact_bot  = Set.empty
  , fact_join = add
  }
    where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `Set.union` old
              ch = changeIf (Set.size j > Set.size old)

liveness :: BwdTransfer Insn' Live
liveness = mkBTransfer go
  where
    go :: Insn' e x -> Fact x Live -> Live
    go (CCLabel  {} ) s = s
    go (CCLetVal  id letable ) s = Set.union   (without s [id]) (Set.fromList $ freeIdentsL letable)
    go (CCLetFuns ids clzs   ) s = Set.unions ((without s ids):(map (Set.fromList . freeIdentsC) clzs))
    go (CCGCLoad     v rv _  ) s = insert (without s [tidIdent v]) [rv]
    go (CCGCInit   _ v rv    ) s = insert (without s [tidIdent v]) [rv]
    go (CCGCKill (Enabled _) vs) s = insert s (Set.toList vs)
    go (CCGCKill Disabled   _vs) s = s
    go (CCTupleStore vs v _) s = insert s (v:vs)
    go (CCRebindId   _ v1 v2) s = insert (without s [tidIdent v1]) [v2]
    go node@(CCLast _ last) fdb =
          let s = Set.unions (map (fact fdb) (successors node)) in
          case last of
            (CCCont _         vs) -> insert s vs
            (CCCase v _ _)        -> insert s [v]

    without s ids = Set.difference s (Set.fromList ids)
    insert s vs = Set.union s (Set.fromList (map tidIdent vs))

    fact :: FactBase Live -> Label -> Live
    fact f l = fromMaybe (fact_bot liveLattice) $ lookupFact l f

deadBindElim :: forall m . FuelMonad m => BwdRewrite m Insn' Live
deadBindElim = mkBRewrite d
  where
    isDead id live = not (Set.member id live)

    d :: Insn' e x -> Fact x Live -> m (Maybe (Graph Insn' e x))
    d (CCLetVal id letable) live |
      isDead id live && isPure letable = return $ Just emptyGraph
    d (CCRebindId _ v _) live | isDead (tidIdent v) live
                                       = return $ Just emptyGraph
    d _ _ = return Nothing
    -- TODO drop fns/closures?
    --d (ILetFuns [id] [_])  live |
    --  not (id `Set.member` live)                   = return $ Just emptyGraph
    -- If LetFuns forms a SCC, then we can't drop any entry unless we can drop
    -- every entry. However, if it's not a SCC, then we can drop any entry which
    -- is dead and does not appear in any of the other functions.

runLiveness :: BasicBlockGraph' -> Compiled BasicBlockGraph'
runLiveness bbgp = do
    uref <- gets ccUniqRef
    liftIO $ runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M BasicBlockGraph'
    go bbgp = do
        (body' , _, _) <- analyzeAndRewriteBwd bwd (JustC [bbgpEntry bbgp])
                                                           (bbgpBody bbgp)
                                                           mapEmpty
        return bbgp { bbgpBody = body' }

    -- bwd' = debugBwdTransfers trace showing (\_ _ -> True) bwd
    bwd = BwdPass { bp_lattice  = liveLattice
                  , bp_transfer = liveness
                  , bp_rewrite  = deadBindElim
                  }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

runPreAllocationOptimizations b0 = do
  (_av_time, b1) <- ioTime $ runAvails b0
  --liftIO $ putDocLn $ text "  runAvails   time: " <> text (Criterion.secs av_time)
  (_lv_time, b2) <- ioTime $ runLiveness b1
  --liftIO $ putDocLn $ text "  runLiveness time: " <> text (Criterion.secs lv_time)
  return b2

-- ||||||||||| Bottom-up May-GC constraint propagation ||||||||||{{{
type MGCM a = State MayGCConstraints a -- MGCM = "may-gc monad"

collectMayGCConstraints :: CCBody -> MayGCConstraints
collectMayGCConstraints (CCBody procs _bindings) =
      -- TODO do we need to worry about GC in top-level bindings?
      execState (mapM collectMayGCConstraints_CCProc procs) Map.empty

collectMayGCConstraints_CCProc :: CCProc -> MGCM ()
collectMayGCConstraints_CCProc proc =
    collectMayGCConstraints_CFG (procBlocks proc) (procIdent proc)

collectMayGCConstraints_CFG :: BasicBlockGraph' -> Ident -> MGCM ()
collectMayGCConstraints_CFG bbgp fnid = let (bid,_) = bbgpEntry bbgp in
                                        mapGraphNodesM_ go bid (bbgpBody bbgp)
  where
        go :: forall e x. Insn' e x -> MGCM ()
        go (CCLabel  _    )    = return ()
        -- This is a conservative approximation; we may not actually call v
        -- through the ident it is bound to, but it's good enough for now...
        -- The indirect constraint is a hack to ensure that the SCC/call graph
        -- built during may-gc resolution will not be under-approximated.
        -- The aliasing bit makes sure that calls to x are treated as being
        -- GCUnknown rather than MayGC.
        go (CCLetVal x (ILBitcast _ v)) = do addIndirectConstraint (tidIdent v)
                                             modify $ aliasing x v
        go (CCLetVal _  lt)    = withGC $ canGC Map.empty lt
        go (CCLetFuns [] []) = error $ "empty CCLetFuns spotted by collectMayGCConstraints in ILExpr.hs"
        go (CCLetFuns _ids _closures) = withGC MayGC
        go (CCLast _ cclast)     = case cclast of
                     CCCont {}      -> return ()
                     CCCase {}      -> return ()

        go (CCGCLoad     {}) = return ()
        go (CCGCInit     {}) = return ()
        go (CCGCKill     {}) = return ()
        go (CCTupleStore {}) = return ()
        go (CCRebindId   {}) = return ()

        aliasing x v = \m -> Map.insert x (looky m (tidIdent v) `addAlias` v) m
        addAlias (maygc, s) v = (maygc, Set.insert (tidIdent v) s)
        looky m id = Map.findWithDefault defaultMayGCConstraint id m
        defaultMayGCConstraint = (GCUnknown "maygc-init", Set.empty)

        withGC WillNotGC     = return ()
        withGC MayGC         = modify $ Map.adjust (\_ -> (MayGC, Set.empty)) fnid
        withGC (GCUnknown _) = return ()

        addIndirectConstraint id =
          modify $ Map.adjust (\(maygc, indirs) ->
                                (maygc, Set.insert id indirs)) fnid
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{
showILProgramStructure :: ILProgram -> Doc
showILProgramStructure (ILProgram procdefs vals _decls _dtypes _lines) =
        vcat (map pretty vals)
    <$> vcat (map showProcStructure procdefs)
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
            text ("vvvvvvvvvvvvvvvvvv")
        <$> text (show blockid)
        <$> text (concatMap (\m -> "\t" ++ show m ++ "\n") mids)
        <$> text (show last ++ "\n^^^^^^^^^^^^^^\n")

instance Pretty MayGC where pretty = text . show

instance Show ILLast where
  show (ILRetVoid     ) = "ret void"
  show (ILRet v       ) = "ret " ++ show v
  show (ILBr  bid args) = "br " ++ show bid ++ " , " ++ show args
  show (ILCase v arms def) = "case(" ++ show v ++ ")"
                                ++ "\n" ++ concatMap (\arm -> "\t" ++ show arm ++ "\n") arms
                                ++ show def
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

