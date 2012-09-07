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

import Foster.Base
import Foster.CFG
import Foster.CloConv
import Foster.TypeLL
import Foster.Letable
import Foster.GCRoots

import Data.IORef
import Data.Map(Map)
import Data.List(zipWith4)
import qualified Data.Set as Set(toList, map)
import qualified Data.Map as Map(singleton, insertWith, lookup, empty, fromList,
                                                         union, findWithDefault)
import qualified Data.Text as T(pack, unpack)

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
              | ILRebindId    Ident    LLVar
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

-- ||||||||||||||||||||||||| Allocation Explication  ||||||||||||{{{
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
    (CCLetVal id (ILAppCtor genty (CtorInfo cid _) vs)) -> do
            id' <- fresh "ctor-alloc"
            let tynm = ctorTypeName cid ++ "." ++ ctorCtorName cid
            let tag  = ctorSmallInt cid
            let t = LLStructType (map tidType vs)
            let obj = (TypedId (LLPtrType t) id' )
            let memregion = MemRegionGlobalHeap
            let info = AllocInfo t memregion tynm (Just tag) Nothing "ctor-allocator" NoZeroInit
            return $
              (mkMiddle $ CCLetVal id' (ILAllocate info)) <*>
              (mkMiddle $ CCTupleStore vs obj memregion)  <*>
              (mkMiddle $ CCLetVal id  (ILBitcast genty obj))
    (CCTupleStore   {}   ) -> return $ mkMiddle insn
    (CCLetVal  _id  _l   ) -> return $ mkMiddle insn
    (CCLetFuns ids clos)   -> makeClosureAllocationExplicit fresh ids clos
    (CCRebindId     {}   ) -> return $ mkMiddle insn
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
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

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
     midmany (CCGCKill Disabled     _root) = error $ "Invariant violated: saw disabled root kill pseudo-insn!"
     midmany (CCGCKill (Enabled cgc) roots) = [ILGCRootKill root cgc | root <- Set.toList roots]
     midmany insn = [mid insn]

     mid :: Insn' O O -> ILMiddle
     mid (CCLetVal id letable)    = ILLetVal   id  letable
     mid (CCGCLoad v   fromroot)  = ILLetVal (tidIdent v) (ILDeref (tidType v) fromroot)
     mid (CCGCInit _ src toroot)  = ILGCRootInit src toroot
     mid (CCTupleStore vs tid r)  = ILTupleStore vs tid r
     mid (CCRebindId v1 v2)       = ILRebindId (tidIdent v1) v2 -- (tidIdent v2) v1 -- ugh :-(
     mid (CCLetFuns {}          ) = error $ "Invariant violated: CCLetFuns should have been eliminated!"
     mid (CCGCKill  {}          ) = error $ "Invariant violated: GCKill should have been handled by `midmany`..."

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
          (CCGCKill enabld roots) -> CCGCKill enabld (Set.map s roots)
          (CCTupleStore vs  v r) -> CCTupleStore (map s vs) (s v) r
          (CCLetVal  id letable) -> CCLetVal id $ substVarsInLetable s letable
          (CCLetFuns ids fns   ) -> CCLetFuns ids $ map (substForInClo s) fns
          (CCRebindId v1 v2    ) -> CCRebindId (s v1) (s v2)
          (CCLast    cclast    ) -> case cclast of
              (CCCont b vs)        -> CCLast (CCCont b (map s vs))
              (CCCall b t id v vs) -> CCLast (CCCall b t id (s v) (map s vs))
              (CCCase v cs mb occ) -> CCLast (CCCase (s v) cs mb occ)

     substForInClo :: VarSubstFor Closure
     substForInClo s clo =
       clo { closureCaptures = (map s (closureCaptures clo)) }

type VarSubstFor a = (LLVar -> LLVar) -> a -> a
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

