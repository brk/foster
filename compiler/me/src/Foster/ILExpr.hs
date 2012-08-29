{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns, RankNTypes, ScopedTypeVariables #-}
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
import Foster.MonoType
import Foster.Letable
import Foster.Output(out, Output)

import Data.Maybe(fromMaybe)
import Data.IORef
import Data.Map(Map)
import qualified Data.Set as Set
import qualified Data.Map as Map(singleton, insertWith, lookup, empty, fromList,
                                 elems, keysSet, insert, union, findWithDefault)
import qualified Data.Text as T(pack)
import Control.Monad.State(evalStateT, get, put, StateT)

--------------------------------------------------------------------

-- | Inserts GC roots with live ranges using a flow-based analysis, and
-- | also transforms back from Hoopl's CFG representation to lists-of-blocks.
-- |
-- | We also perform pattern match compilation at this stage.
-- |
-- | The primary differences in the general structure are:
-- |  #. LetFuns replaced with (Let)Closures
-- |  #. Module  replaced with ILProgram
-- |  #. Fn replaced with ProcDef
-- |  #. Decision trees replaced with flat switches

-- ||||||||||||||||||||||||| Datatypes ||||||||||||||||||||||||||{{{
-- A program consists of top-level data types and mutually-recursive procedures.
data ILProgram = ILProgram [ILProcDef]
                           [MoExternDecl]
                           [DataType MonoType]
                           SourceLines

data ILExternDecl = ILDecl String MonoType
data ILProcDef = ILProcDef (Proc [ILBlock]) NumPredsMap [RootVar]
type NumPredsMap = Map BlockId Int

-- The standard definition of a basic block and its parts.
-- This is equivalent to MinCaml's make_closure ...
data ILBlock  = Block BlockEntry [ILMiddle] ILLast
data ILMiddle = ILLetVal      Ident    Letable
              | ILGCRootKill  MoVar
              | ILGCRootInit  MoVar    RootVar
              | ILTupleStore  [MoVar]  MoVar    AllocMemRegion
              | ILClosures    [Ident] [Closure]
              deriving Show

-- Drop call-as-a-terminator and implicitly re-allow it as a letable value,
-- which better matches LLVM's IR. (If/when we support exception handling,
-- note that a possibly-exception-raising call remains a block terminator!)
data ILLast = ILRetVoid
            | ILRet      MoVar
            | ILBr       BlockId [MoVar]
            | ILCase     MoVar [(CtorId, BlockId)] (Maybe BlockId) (Occurrence MonoType)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

prepForCodegen :: ModuleIL CCBody MonoType -> IORef Uniq -> IO ILProgram
prepForCodegen m uref = do
    let decls = map (\(s,t) -> MoExternDecl s t) (moduleILdecls m)
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
         Block (frs f) (map mid (blockToList ms) ++ lastmids) last
   where
     mid :: Insn' O O -> ILMiddle
     mid (CCLetVal id letable)    = ILLetVal   id  letable
     mid (CCGCLoad v   fromroot)  = ILLetVal (tidIdent v) (ILDeref (tidType v) fromroot)
     mid (CCGCInit _ src toroot)  = ILGCRootInit src toroot
     mid (CCGCKill True    root)  = ILGCRootKill root
     mid (CCGCKill False  _root)  = error $ "Invariant violated: saw disabled root kill pseudo-insn!"
     mid (CCTupleStore vs tid r)  = ILTupleStore vs tid r
     mid (CCLetFuns ids closures) = ILClosures ids closures

     frs :: Insn' C O -> BlockEntry
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

     mergeAdjacent :: Map MoVar MoVar -> (Block Insn' C O, Insn' O C)
                                      -> (Insn' C O, Block Insn' O C)
                                      -> Maybe (Block Insn' C C, Map MoVar MoVar)
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

type VarSubstFor a = (MoVar -> MoVar) -> a -> a
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| GC Root Insertion |||||||||||||||||||||||{{{

instance TExpr Closure MonoType where freeTypedIds _ = []

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
type LiveGCRoots    = Set.Set MoVar
type RootLiveWhenGC = Set.Set MoVar
type LiveAGC2 = (LiveGCRoots, RootLiveWhenGC)

liveAtGCPointLattice2 :: DataflowLattice LiveAGC2
liveAtGCPointLattice2 = DataflowLattice
  { fact_name = "Live GC roots"
  , fact_bot  = (Set.empty, Set.empty)
  , fact_join = add
  }
    where add _lab (OldFact (ol,og)) (NewFact (nl,ng)) = (ch, (jl, jg))
            where
              jl = nl `Set.union` ol
              jg = ng `Set.union` og
              ch = changeIf (Set.size jl > Set.size ol
                          || Set.size jg > Set.size og)

liveAtGCPointXfer2 :: BwdTransfer Insn' LiveAGC2
liveAtGCPointXfer2 = mkBTransfer go
  where
    markLive root (s, g) = (Set.insert root s, g)
    markDead root (s, g) = (Set.delete root s, g)

    ifgc mayGC (s, g) = if mayGC then (s, g `Set.union` s)
                                 else (s, g)

    go :: Insn' e x -> Fact x LiveAGC2 -> LiveAGC2
    go (CCLabel   {}        ) sg = ifgc False            sg
    go (CCGCLoad _v fromroot) sg = markLive fromroot     sg
    go (CCGCInit _ _v toroot) sg = markDead   toroot     sg
    go (CCGCKill {}         ) sg = {- just ignore it  -} sg
    go (CCLetVal  _id  l    ) sg = ifgc (canGCLetable l) sg
    go (CCLetFuns _ids _clos) sg = ifgc True             sg
    go (CCTupleStore   {}   ) sg = ifgc False            sg
    go node@(CCLast    cclast) fdb =
          let sg = union2s (map (fact fdb) (successors node)) in
          case cclast of
            (CCCont {}       ) -> ifgc False sg
            (CCCall _ _ _ v _) -> ifgc (canGCCalled v) sg
            (CCCase {}       ) -> ifgc False sg

    union2s xys = let (xs,ys) = unzip xys
                  in  (Set.unions xs, Set.unions ys)

    fact :: FactBase LiveAGC2 -> Label -> LiveAGC2
    fact f l = fromMaybe (fact_bot liveAtGCPointLattice2) $ lookupFact l f

liveAtGCPointRewrite2 :: forall m. FuelMonad m => BwdRewrite m Insn' LiveAGC2
liveAtGCPointRewrite2 = mkBRewrite d
  where
    d :: Insn' e x -> Fact x LiveAGC2 -> m (Maybe (Graph Insn' e x))
    d (CCLabel lab) (s,g) = do
        return $ trace ("agc @ " ++ show lab ++ ": " ++ show (s,g)) Nothing
    d (CCGCLoad v  fromroot) (s,g) = do
        return $ trace ("agc @ GCLOAD " ++ show v ++ " from root " ++ show fromroot ++ " : " ++ show (s,g)) Nothing
    d (CCGCInit _ _ toroot) (s,g) = do
        return $ trace ("agc @ GCINIT " ++ show toroot ++ " : " ++ show (s,g)) Nothing
    d (CCGCKill True   _root) (_,_) = return Nothing -- leave as-is.
    d (CCGCKill False   root) (s,g) =
          if trace ("agc @ GCKILL " ++ show root ++ " : " ++ "live? " ++ show (Set.member root s) ++ show (s,g)) $ Set.member root s
            then return $ Just emptyGraph
             -- If a root is live, remove its fake kill node.
             -- Otherwise, toggle the node from disabled to enabled.
            else return $ Just (mkMiddle (CCGCKill True root))
    d (CCTupleStore _ _ _) _sg = do return Nothing
    d (CCLetVal id _) (s,g) = do
        return $ trace ("agc @ LET " ++ show id ++ ": " ++ show (s,g)) Nothing
    d (CCLetFuns ids _) (s,g) = do
        return $ trace ("agc @ " ++ show ids ++ ": " ++ show (s,g)) Nothing
    d node@(CCLast cclast) fdb =
        let (s,g) = union2s (map (fact fdb) (successors node)) in do
        return $ trace ("agc @ " ++ show cclast ++ ": " ++ show (s,g)) Nothing

    union2s xys = let (xs,ys) = unzip xys
                  in  (Set.unions xs, Set.unions ys)

    fact :: FactBase LiveAGC2 -> Label -> LiveAGC2
    fact f l = fromMaybe (fact_bot liveAtGCPointLattice2) $ lookupFact l f

runLiveAtGCPoint2 :: IORef Uniq -> BasicBlockGraph' -> IO RootLiveWhenGC
runLiveAtGCPoint2 uref bbgp = runWithUniqAndFuel uref infiniteFuel (go bbgp)
  where
    go :: BasicBlockGraph' -> M RootLiveWhenGC
    go bbgp = do
        let ((_,blab), _) = bbgpEntry bbgp
        (_, fdb, _) <- analyzeAndRewriteBwd bwd (JustC [bbgpEntry bbgp]) (bbgpBody bbgp)
                         (mapSingleton blab (fact_bot liveAtGCPointLattice2))
        return (snd $ fromMaybe (error "runLiveAtGCPoint failed") $
                            lookupFact blab fdb)

    bwd = BwdPass { bp_lattice  = liveAtGCPointLattice2
                  , bp_transfer = liveAtGCPointXfer2
                  , bp_rewrite  = liveAtGCPointRewrite2
                  }
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

insertSmartGCRoots :: IORef Uniq -> BasicBlockGraph' -> IO ( BasicBlockGraph' , [RootVar] )
insertSmartGCRoots uref bbgp0 = do
  bbgp1 <- makeAllocationsExplicit bbgp0 uref
  (bbgp' , gcr) <- insertDumbGCRoots uref bbgp1
  rootsLiveAtGCPoints <- runLiveAtGCPoint2 uref bbgp'
  bbgp'' <- removeDeadGCRoots bbgp' (mapInverse gcr) rootsLiveAtGCPoints
  putStrLn $ "these roots were live at GC points: " ++ show rootsLiveAtGCPoints
  return ( bbgp1 , Set.toList rootsLiveAtGCPoints)
 where
    mapInverse m = let ks = Map.keysSet m in
                   let es = Set.fromList (Map.elems m) in
                   if Set.size ks == Set.size es
                     then Map.fromList (zip (Set.toList es) (Set.toList ks))
                     else error $ "mapInverse can't reverse a non-one-to-one map!"
                               ++ "\nkeys: " ++ show ks ++ "\nelems:" ++ show es

type GCRootsForVariables = Map MoVar RootVar
type VariablesForGCRoots = Map RootVar MoVar

measure :: String -> Boxes.Box
measure s = Boxes.vcat Boxes.left (map Boxes.text $ lines s)

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
insertDumbGCRoots :: IORef Uniq -> BasicBlockGraph' -> IO (BasicBlockGraph'
                                                          ,GCRootsForVariables)
insertDumbGCRoots uref bbgp = do
   (g' , fini) <- rebuildGraphAccM (case bbgpEntry bbgp of (bid, _) -> bid)
                                       (bbgpBody bbgp) Map.empty transform

   if False then return ()
     else do
           let catboxes bbgs = Boxes.hsep 1 Boxes.left $ map (boxify . measure) $
                                                         map (show . pretty) bbgs
           Boxes.printBox $ catboxes [bbgpBody bbgp , g' ]

   return (bbgp { bbgpBody =  g' }, fini)

 where
  transform :: GCRootsForVariables -> Insn' e x -> IO (Graph Insn' e x, GCRootsForVariables)
  transform gcr insn = case insn of
    CCLabel {}                    -> do return (mkFirst insn <*> mkMiddles [
                                                 CCGCKill False root | root <- Map.elems gcr]
                                                                                      , gcr)
    CCGCLoad  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCGCInit  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCGCKill  {}                  -> do return (mkMiddle $ insn                       , gcr)
    CCTupleStore vs v r           -> do withGCLoads gcr (v:vs) (\(v' : vs' ) ->
                                         mkMiddle $ CCTupleStore vs' v' r)
    CCLetVal id val               -> do let vs = freeTypedIds val
                                        withGCLoads gcr vs (\vs' ->
                                         let m = Map.fromList (zip vs vs' ) in
                                         let s v = Map.findWithDefault v v m in
                                         mkMiddle $ CCLetVal id (substVarsInLetable s val))
    CCLetFuns {}                  -> do -- The strategy for inserting GC loads here is a bit
                                        -- subtle, because we want to make sure that
                                        return (mkMiddle $ insn                       , gcr)
    CCLast (CCCont b vs)          -> do withGCLoads gcr vs (\vs'  ->
                                               (mkLast $ CCLast (CCCont b vs' )))
    CCLast (CCCall b t id v vs)   -> do withGCLoads gcr (v:vs) (\(v' : vs' ) ->
                                               (mkLast $ CCLast (CCCall b t id v' vs' )))
    CCLast (CCCase v arms mb occ) -> do withGCLoads gcr [v] (\[v' ] ->
                                               (mkLast $ CCLast (CCCase v' arms mb occ)))

  -- A helper function to assist in rewriting instructions to use loads from
  -- GC roots for variables which are subject to garbage collection.
  withGCLoads :: GCRootsForVariables -> [MoVar]
                                     -> ([MoVar] -> Graph Insn' O x)
                                     -> IO (Graph Insn' O x, GCRootsForVariables)
  withGCLoads gcr vs mkG = do
    let fresh str = do u <- modifyIORef uref (+1) >> readIORef uref
                       return (Ident (T.pack str) u)
        -- We'll rewrite something like ``call @foo (x,n)`` (where ``x`` is
        -- GCable and ``n`` isn't) with::
        --      x.load = load x.root
        --      kill x.root (disabled)
        ---     call @foo (x.load , n)
        -- We'll removed kills for live roots and enable the remainder.
        retLoaded root gcr oos = do
            id <- fresh (show (tidIdent root) ++ ".load")
            let loadedvar = TypedId (tidType root) id
            return ((oos ++ [CCGCLoad loadedvar root
                            ,CCGCKill False     root], loadedvar), gcr)

        withGCLoad :: MoVar -> GCRootsForVariables
                            -> IO (([Insn' O O], MoVar), GCRootsForVariables)
        withGCLoad v gcr = do
          if not $ isGCable v
            then return (([], v), gcr)
            else case Map.lookup v gcr of
                   Just root -> do retLoaded root gcr []
                   Nothing   -> do rootid <- fresh (show (tidIdent v) ++ ".root")
                                   let root = TypedId (tidType v) rootid
                                   let gcr' = Map.insert v root gcr
                                   junkid <- fresh (show (tidIdent v) ++ ".junk")
                                   let junk = TypedId (TupleType []) junkid
                                   retLoaded root gcr' [CCGCInit junk v root]

    (loadsAndVars , gcr' ) <- mapFoldM' vs gcr withGCLoad
    let (loads, vs' ) = unzip loadsAndVars
    return (mkMiddles (concat loads) <*> mkG vs' , gcr' )

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

   if False then return ()
     else do
           let catboxes bbgs = Boxes.hsep 1 Boxes.left $ map (boxify . measure) $
                                                         map (show . pretty) bbgs
           Boxes.printBox $ catboxes [bbgpBody bbgp , g' ]
   return bbgp { bbgpBody =  g' }
 where
  isLive root = Set.member root liveRoots
  iflive root g = if isLive root then return g else return emptyGraph

  transform :: Insn' e x -> RootMapped (Graph Insn' e x)
  transform insn = case insn of
    CCLabel {}                    -> do return $ mkFirst $ insn
    CCGCLoad  v     root          -> do m <- get
                                        put (Map.insert v root m)
                                        iflive root $ mkMiddle $ insn
    CCGCInit  _ _   root          -> do iflive root $ mkMiddle $ insn
    CCGCKill  True  root          -> do iflive root $ mkMiddle $ insn
    CCGCKill  False root          -> do return emptyGraph -- TODO remove this
    CCTupleStore vs v r           -> do undoDeadGCLoads (v:vs) (\(v' : vs' ) ->
                                         mkMiddle $ CCTupleStore vs' v' r)
    CCLetVal id val               -> do let vs = freeTypedIds val
                                        undoDeadGCLoads vs (\vs' ->
                                         let m = Map.fromList (zip vs vs' ) in
                                         let s v = Map.findWithDefault v v m in
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

canGCLetable l = let rv = canGC  l in if rv then {- trace ("canGCL: " ++ show l) -} rv else rv
canGCCalled  v = let rv = canGCF v in if rv then {- trace ("canGCF: " ++ show v) -} rv else rv

-- Filter out non-pointer-typed variables from live set.
gcable vs = Set.fromList $ filter isGCable vs
isGCable v = case tidType v of
               PrimInt _            -> False
               PrimFloat64          -> False
               StructType _         -> False
               FnType _ _ _ FT_Proc -> False
               FnType _ _ _ FT_Func -> True
               PtrType _            -> True -- could have further annotations on ptr types
               TyConApp   {}        -> True
               TupleType  {}        -> True
               CoroType _ _         -> True
               ArrayType _          -> True
               PtrTypeUnknown       -> True
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
showILProgramStructure :: ILProgram -> Output
showILProgramStructure (ILProgram procdefs _decls _dtypes _lines) =
    concatMap showProcStructure procdefs
  where
    showProcStructure (ILProcDef proc _ roots) =
        out (show $ procIdent proc) ++ (out " // ")
            ++ (out $ show $ map procVarDesc (procVars proc))
            ++ (out " ==> ") ++ (out $ show $ procReturnType proc)
          ++ out ("\n" ++ unlines (map show roots))
          ++ out "\n" ++ concatMap showBlock (procBlocks proc)
          ++ out "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

    showBlock (Block blockid mids last) =
           out (show blockid ++ "\n")
        ++ out (concatMap (\m -> "\t" ++ show m ++ "\n") mids)
        ++ out (show last ++ "\n\n")

instance Show ILLast where
  show (ILRetVoid     ) = "ret void"
  show (ILRet v       ) = "ret " ++ show v
  show (ILBr  bid args) = "br " ++ show bid ++ " , " ++ show args
  show (ILCase v _arms _def _occ) = "case(" ++ show v ++ ")"
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


makeAllocationsExplicit :: BasicBlockGraph' -> IORef Uniq -> IO BasicBlockGraph'
makeAllocationsExplicit bbgp uref = do
     let (bid,_) = bbgpEntry bbgp
     bb' <- rebuildGraphM bid (bbgpBody bbgp) explicate
     return $ bbgp { bbgpBody = bb' }
 where
  fresh str = do u <- modifyIORef uref (+1) >> readIORef uref
                 return (Ident (T.pack str) u)

  explicate :: Insn' e x -> IO (Graph Insn' e x)
  explicate insn = case insn of
    (CCLabel   {}        ) -> return $ mkFirst $ insn
    (CCGCLoad _v fromroot) -> return $ mkMiddle $ insn
    (CCGCInit _ _v toroot) -> return $ mkMiddle $ insn
    (CCGCKill {}         ) -> return $ mkMiddle $ insn
    (CCLetVal id (ILAlloc v memregion)) -> do
            id' <- fresh "ref-alloc"
            let t = tidType v
            let info = AllocInfo t memregion Nothing "ref-allocator"
            return $
              (mkMiddle $ CCLetVal id  (ILAllocate info)) <*>
              (mkMiddle $ CCLetVal id' (ILStore v (TypedId t id)))
    (CCLetVal id (ILTuple vs allocsrc)) -> do
            id' <- fresh "tup-alloc"
            let t = StructType (map tidType vs)
            let memregion = MemRegionGlobalHeap
            let info = AllocInfo t memregion Nothing "tup-allocator"
            return $
              (mkMiddle $ CCLetVal id (ILAllocate info)) <*>
              (mkMiddle $ CCTupleStore vs (TypedId t id) memregion)
    (CCTupleStore   {}   ) -> return $ mkMiddle $ insn
    (CCLetVal  _id  l    ) -> return $ mkMiddle $ insn
    (CCLetFuns _ids _clos) -> return $ mkMiddle $ insn
    (CCLast    cclast)     ->
          case cclast of
            (CCCont {}       ) -> return $ mkLast $ insn
            (CCCall _ _ _ v _) -> return $ mkLast $ insn
            (CCCase {}       ) -> return $ mkLast $ insn
