{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CloConv where

import qualified Data.Text as T
import qualified Data.List as List(and)
import Data.Set(Set)
import qualified Data.Set as Set(empty, singleton, union, unions, notMember,
                                                                       fromList)
import Data.Map(Map)
import qualified Data.Map as Map((!), insert, lookup, empty, fromList, elems,
                                 singleton, insertWith, union, findWithDefault)

import Control.Monad.State

import Debug.Trace(trace)
import Control.Exception.Base(assert)

import Compiler.Hoopl

import Foster.Base
import Foster.CFG
import Foster.MonoType
import Foster.Letable
import Foster.PatternMatch
import Foster.Output(out)

data CCBody = CCB_Procs [CCProc] CCMain
data CCMain = CCMain TailQ MonoType MoVar [MoVar]
type CCProc = Proc BasicBlockGraph'
type Blocks = (BasicBlockGraph' , Map BlockId Int)
type Block' = Block Insn' C C
type BlockG = Graph Insn' C C

mkBlockG :: BlockEntry -> [Insn' O O] -> Insn' O C -> BlockG
mkBlockG lab mids last = blockGraph (mkBlock' lab mids last)

mkBlock' :: BlockEntry -> [Insn' O O] -> Insn' O C -> Block'
mkBlock' lab mids last = (blockJoin (CCLabel lab) (blockFromList mids) last)

data BasicBlockGraph' = BasicBlockGraph' { bbgpEntry :: BlockEntry
                                         , bbgpRetK  :: BlockId
                                         , bbgpBody  :: BlockG
                                         }
-- type BlockEntry = (BlockId, [TypedId MonoType])

-- A Closure records the information needed to generate code for a closure.
-- The environment name is recorded so that the symbol table contains
-- the right entry when mutually-recursive functions capture multiple envs.
data Closure = Closure { closureProcIdent :: MoVar
                       , closureEnvIdent  :: Ident
                       , closureCaptures  :: [MoVar]
                       , closureAllocSrc  :: AllocationSource
                       } deriving Show

data Insn' e x where
        CCLabel   :: BlockEntry           -> Insn' C O
        CCLetVal  :: Ident   -> Letable   -> Insn' O O
        CCLetFuns :: [Ident] -> [Closure] -> Insn' O O
        CCLast    :: ILLast               -> Insn' O C

-- The biggest difference from CFLast to ILLast is the decision tree in ILCase.
data ILLast = ILRetVoid
            | ILRet      MoVar
            | ILBr       BlockId [MoVar]
            | ILCase     MoVar [(CtorId, BlockId)] (Maybe BlockId) (Occurrence MonoType)

data Proc blocks =
     Proc { procReturnType :: MonoType
          , procIdent      :: Ident
          , procVars       :: [MoVar]
          , procRange      :: SourceRange
          , procBlocks     :: blocks
          , procBlockPreds :: Map BlockId Int
          }

closureConvertAndLift :: DataTypeSigs
                      -> [Ident]
                      -> Uniq
                      -> ModuleIL CFBody MonoType
                      -> ModuleIL CCBody MonoType
closureConvertAndLift dataSigs globalIds u m =
    -- We lambda lift top level functions, since we know a priori
    -- that they don't have any "real" free vars.
    -- Lambda lifting then closure converts any nested functions.
    let initialState = ILMState u Map.empty Map.empty dataSigs in
    let (ccmain, st) = runState (closureConvertToplevel globalIds $ moduleILbody m)
                                                                 initialState in
    m { moduleILbody = CCB_Procs (Map.elems $ ilmProcs st) ccmain }

closureConvertToplevel :: [Ident] -> CFBody -> ILM CCMain
closureConvertToplevel globalIds body = do
  cvt (Set.fromList globalIds) body
     where
       -- Iterate through the SCCs of definitions, keeping track of a state
       -- parameter (the set of globalized variables, which need not appear in
       -- a function's environment). For each definition, if it doesn't need
       -- an environment, we'll lift it; otherwise, closure convert it.
       -- We directly return a list of the top-level proc definitions, and also
       -- (via the ILM monad) a list of all procs generated, including those
       -- from nested functions.
       cvt :: Set Ident -> CFBody -> ILM CCMain
       cvt _ (CFB_Call tc t v vs) = return (CCMain tc t v vs)

       cvt globalized (CFB_LetFuns ids fns body) =
         let
             unliftable fn glbl = [ id | (TypedId _ id) <- fnFreeIds fn
                                       , Set.notMember id glbl]
             allUnliftables = filter (not . null) (map (\fn -> unliftable fn globalized' ) fns)
             -- If a recursive nest of functions don't close over any other
             -- variables, they can all be globalized as long as every use
             -- of their peers happens to be a direct call. So, we'll assume
             -- we can globalize, but enforce the side condition.
             --
             -- TODO the reason for the side condition is that coercing a
             --      proc to a closure involves allocation, which we can skip
             --      if we don't lambda lift. But we could take an alternate
             --      approach: for each liftable proc, associate with it a
             --      global-symbol trivial closure, allocated at startup time.
             --      Then instead of an allocating coercion, we can just
             --      reference the global variable instead.
             globalized' = Set.union globalized (Set.fromList ids)
             gonnaLift   = null allUnliftables && noFirstClassUses fns
             noFirstClassUses fns = List.and $ map onlySecondClassUses fns
             onlySecondClassUses fn = let bbg = fnBody fn in
                                      let allIds = foldGraphNodes collectBitcasts
                                                           (bbgBody bbg) ids in
                                        foldGraphNodes (checkUses allIds (bbgRetK bbg))
                                                       (bbgBody bbg) (trace ("all ids: " ++ show allIds) True)

             checkUses :: [Ident] -> BlockId -> Insn e x -> Bool -> Bool
             checkUses _      _    _   False = False
             checkUses allIds retk insn True = case insn of
                 ILabel {}                  -> True
                 ILetVal id (ILBitcast _ v) -> id `elem` allIds || ok [v]
                 ILetVal _ (ILCall _ _v vs) -> ok vs -- ignore v
                 ILetVal _ l                -> ok (freeTypedIds l)
                 ILetFuns _ fns             -> noFirstClassUses fns
                 ILast (CFCont bid    vs)   -> bid /= retk || ok vs
                 ILast (CFCall _ _ _v vs)   -> ok vs
                 ILast (CFCase _ _)         -> True
               where
                 ok :: [MoVar] -> Bool
                 ok vs =
                    let usedFirstClass = [v | v <- vs, tidIdent v `elem` allIds] in
                    if null usedFirstClass
                       then True
                       else trace ("ok:used first class: " ++ show usedFirstClass) False

             -- Make sure we treat bitcasts of ids the same as the ids themselves.
             collectBitcasts :: Insn e x -> [Ident] -> [Ident]
             collectBitcasts insn ids = case insn of
                 ILetVal id (ILBitcast _ v) | tidIdent v `elem` ids -> id:ids
                 _ -> ids
         in
            if trace ("gonna lift " ++ show ids ++ "? " ++ show gonnaLift ++ " ;; " ++ show allUnliftables
                 ++ " ***** " ++ show ids ++ "//" ++ show globalized) gonnaLift
              then do _ <- mapM (lambdaLift []) fns      ; cvt globalized' body
              else do _ <- closureConvertLetFuns ids fns ; cvt globalized  body

-- For example, if we have something like
--      let y = blah in
--      (\x -> x + y) foobar
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \yy x -> x + yy
--      let y = blah in p y foobar
lambdaLift :: [MoVar] -> CFFn -> ILM CCProc
lambdaLift freeVars f = do
    newbody <- closureConvertBlocks (fnBody f)
    -- Add *all* of the free variables to the signature of the lambda-lifted
    -- procedure. We could (should?) add only some of them, like Chez Scheme.
    -- (As it happens, at the moment we only do lambda-lifting for top-level
    --  functions, which have no free variables by definition. But still.)
    let liftedProcVars = freeVars ++ fnVars f
    ilmPutProc (closureConvertedProc liftedProcVars f newbody)

-- blockGraph is a Hoopl util function. As mentioned in CFG.hs,
-- we use Graphs instead of Blocks (as provided by Hoopl)
-- for representing basic blocks because they're easier to build.
basicBlock hooplBlock = blockGraph hooplBlock

-- We serialize a basic block graph by computing a depth-first search
-- starting from the graph's entry block.
closureConvertBlocks :: BasicBlockGraph -> ILM Blocks
closureConvertBlocks bbg = do
   let jumpTo bbg = case bbgEntry bbg of (bid, _) -> ILast $ CFCont bid undefined
   let cfgBlocks = map (splitBasicBlock . basicBlock) $
                     preorder_dfs $ mkLast (jumpTo bbg) |*><*| bbgBody bbg
   -- Because we do a depth-first search, "renaming" blocks are guaranteed
   -- to be adjacent to each other in the list.
   let numPreds   = computeNumPredecessors (bbgEntry bbg) cfgBlocks
   let cfgBlocks' = mergeCallNamingBlocks cfgBlocks numPreds
   blocks <- mapM closureConvertBlock cfgBlocks'
   let numPreds'  = computeNumPredecessors (bbgEntry bbg) cfgBlocks'
   return (BasicBlockGraph' {
                 bbgpEntry = bbgEntry bbg,
                 bbgpRetK  = bbgRetK  bbg,
                 bbgpBody = foldr (|*><*|) emptyClosedGraph (map blockGraph (concat blocks))
          }
          , numPreds' )
  where
    computeNumPredecessors elab blocks =
      -- The entry (i.e. postalloca) label will get an incoming edge in LLVM
      let startingMap = Map.singleton (blockId elab) 1 in
      foldr (\sbb m ->
            let  (_, _, terminator) = sbb in
            incrPredecessorsDueTo terminator m) startingMap blocks

    incrPredecessorsDueTo terminator m =
        foldr (\tgt mm -> Map.insertWith (+) tgt 1 mm) m (blockTargetsOf terminator)

    -- A BasicBlock which ends in a decision tree will, in the general case,
    -- expand out to multiple blocks to encode the tree.
    closureConvertBlock :: (BlockEntry, [Insn O O], Insn O C) -> ILM [ Block' ]
    closureConvertBlock (bid, mids, last) = do
        (blocks, lastmid, newlast) <- ilLast last
        newmids <- mapM closureConvertMid mids
        return $ mkBlock' bid (newmids ++ lastmid) newlast : blocks
     where
      -- Translate continuation application to br or ret, as appropriate.
      cont k vs =
           case (k == bbgRetK bbg, vs) of
                (True,  [] ) -> ILRetVoid
                (True,  [v]) -> ILRet   v
                (True,   _ ) -> error $ "ILExpr.hs:No support for multiple return values yet\n" ++ show vs
                (False,  _ ) -> ILBr k vs

      ilLast :: Insn O C -> ILM ( [Block' ], [Insn' O O], Insn' O C)
      ilLast (ILast last) =
        case last of
           -- [[f k vs]] ==> let x = f vs in [[k x]]
           CFCall k t v vs -> do
               id <- ilmFresh (T.pack ".call")
               return ([], [CCLetVal id (ILCall t v vs)], CCLast $ cont k [TypedId t id])
           CFCont k vs -> return ([], [], CCLast $ cont k vs)
           CFCase a pbs    -> do
               allSigs  <- gets ilmCtors
               let dt = compilePatterns pbs allSigs
               let usedBlocks = eltsOfDecisionTree dt
               let _unusedPats = [pat | (pat, bid) <- pbs
                                , Set.notMember bid usedBlocks]
               -- TODO print warning if any unused patterns
               (BlockFin blocks id) <- compileDecisionTree a dt
               return $ (blocks, [], CCLast $ ILBr id [])
              where
                -- The decision tree we get from pattern-match compilation may
                -- contain only a subset of the pattern branche.
                eltsOfDecisionTree :: (Show a, Ord a) => DecisionTree a t -> Set a
                eltsOfDecisionTree DT_Fail = Set.empty
                eltsOfDecisionTree (DT_Leaf a _) = Set.singleton a
                eltsOfDecisionTree (DT_Switch _ idsDts maybeDt) = Set.union
                   (Set.unions (map (\(_, dt) -> eltsOfDecisionTree dt) idsDts))
                   (case maybeDt of
                       Just dt -> eltsOfDecisionTree dt
                       Nothing -> Set.empty)

      closureConvertMid :: Insn O O -> ILM (Insn' O O)
      closureConvertMid mid =
        case mid of
          ILetVal id val -> return $ CCLetVal id val
          ILetFuns ids fns -> do closures <- closureConvertLetFuns ids fns
                                 return $ CCLetFuns ids closures

closureConvertLetFuns :: [Ident] -> [CFFn] -> ILM [Closure]
closureConvertLetFuns ids fns = do
    let genFreshId id = ilmFresh (".env." `prependedTo` identPrefix id)
    cloEnvIds <- mapM genFreshId ids
    let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
    let idfns = zip ids fns
    mapM (closureOfKnFn infoMap) idfns

data BlockFin = BlockFin [ Block' ]       -- new blocks generated
                         BlockId          -- entry block for decision tree logic

bogusVar (id, _) = TypedId (PrimInt I1) id

compileDecisionTree :: MoVar -> DecisionTree BlockId MonoType -> ILM BlockFin
-- Translate an abstract decision tree to ILBlocks, also returning
-- the label of the entry block into the decision tree logic.
-- For now, we don't do any available values computation, which means that
-- nested pattern matching will load the same subterm multiple times:
-- once on the path to a leaf, and once more inside the leaf itself.

compileDecisionTree _scrutinee (DT_Fail) = error "can't do dt_FAIL yet"

compileDecisionTree _scrutinee (DT_Leaf armid []) = do
        return $ BlockFin [] armid

-- Because of the way decision trees can be copied, we can end up with
-- multiple DT_Leaf nodes for the same armid. Since we don't want to emit
-- bindings multiple times, we associate each armid with the id of a basic
-- block which binds the arm's free variables, and make all the leafs jump
-- to the wrapper instead of directly to the arm.
compileDecisionTree scrutinee (DT_Leaf armid idsoccs) = do
        wrappers <- gets ilmBlockWrappers
        case Map.lookup armid wrappers of
           Just id -> do return $ BlockFin [] id
           Nothing -> do let binders = map (emitOccurrence scrutinee) idsoccs
                         (id, block) <- ilmNewBlock ".leaf" binders (CCLast $ ILBr armid []) -- TODO
                         ilmAddWrapper armid id
                         return $ BlockFin [block] id

compileDecisionTree scrutinee (DT_Switch occ subtrees maybeDefaultDt) = do
        let splitBlockFin (BlockFin blocks id) = (blocks, id)
        let (ctors, subdts) = unzip subtrees
        fins  <- mapM (compileDecisionTree scrutinee) subdts
        (dblockss, maybeDefaultId) <- case maybeDefaultDt of
           Nothing -> do return ([], Nothing)
           Just dt -> do (BlockFin dblockss did) <- compileDecisionTree scrutinee dt
                         return (dblockss, Just did)
        let (blockss, ids) = unzip (map splitBlockFin fins)
        (id, block) <- ilmNewBlock ".dt.switch" [] $ (CCLast $
                          mkSwitch scrutinee (zip ctors ids) maybeDefaultId occ)
        return $ BlockFin (block : concat blockss ++ dblockss) id

emitOccurrence :: MoVar -> (Ident, Occurrence MonoType) -> Insn' O O
emitOccurrence scrutinee (id, occ) = CCLetVal id (ILOccurrence scrutinee occ)

type InfoMap = Map Ident (CFFn, Ident) -- fn ident => (fn, env id)

fnFreeIds :: CFFn -> [MoVar]
fnFreeIds fn = freeTypedIds fn

closureOfKnFn :: InfoMap
              -> (Ident, CFFn)
              -> ILM Closure
closureOfKnFn infoMap (self_id, fn) = do
    let varsOfClosure = closedOverVarsOfKnFn
    let transformedFn = makeEnvPassingExplicit fn
    (envVar, newproc) <- closureConvertFn transformedFn varsOfClosure
    let procid        = TypedId (procType newproc) (procIdent newproc)
    return $ Closure procid envVar varsOfClosure
                   (AllocationSource (show procid ++ ":") (procRange newproc))
  where
    procType proc =
      let retty = procReturnType proc in
      let argtys = map tidType (procVars proc) in
      FnType argtys retty FastCC FT_Proc

    -- Each closure converted proc need not capture its own environment
    -- variable, because it will be added as an implicit parameter, but
    -- the environments for others in the same rec SCC *are* closed over.
    closedOverVarsOfKnFn :: [MoVar]
    closedOverVarsOfKnFn =
        let nonGlobalVars = [tid | tid@(TypedId _ (Ident _ _)) <- fnFreeIds fn] in
        let capturedVarsFor  tid v envid =
               if tid == self_id -- If we close over ourself,
                 then [v]        -- don't try to capture the env twice.
                 else [v, fakeCloVar envid]
        in
        -- Capture env. vars in addition to closure vars.
        -- When making direct calls, we only need the environment variable,
        -- since we can refer to the other closure's code function directly.
        -- However, if we want to return one closure from another, we (probably)
        -- do not wish turn that variable reference into a closure allocation.
        concatMap (\v -> let tid = tidIdent v in case Map.lookup tid infoMap of
                              Nothing ->   [v]
                              Just (_, envid) -> capturedVarsFor tid v envid)
             nonGlobalVars

    fakeCloVar id = TypedId fakeCloEnvType id
                      where fakeCloEnvType = TyConApp "Foster$GenericClosureEnvPtr" []

    -- This is where the magic happens: given a function and its free variables,
    -- we create a procedure which also takes an extra (strongly-typed) env ptr
    -- argument. The new body does case analysis to bind the free variable names
    -- to the contents of the slots of the environment.
    closureConvertFn :: CFFn -> [MoVar] -> ILM (Ident, CCProc)
    closureConvertFn f varsOfClosure = do
        let envId  = snd (infoMap Map.! self_id)
        -- Note that this env var has a precise type! The other's is missing.
        let envVar = TypedId (TupleType $ map tidType varsOfClosure) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- do
            let BasicBlockGraph bodyentry rk oldbodygraph = fnBody f
            let norange = MissingSourceRange ""
            let patVar a = P_Variable norange a
            let cfcase = CFCase envVar [
                           ((P_Tuple norange t (map patVar varsOfClosure),
                                                           varsOfClosure)
                           , fst bodyentry) ]
                        where t = TupleType (map tidType varsOfClosure)
            -- We change the entry block of the new body (versus the old).
            lab <- freshLabel
            let bid = (("caseof", lab), [])
            let caseblock = mkFirst (ILabel bid) <*>
                            mkMiddles []         <*>
                            mkLast (ILast cfcase)
            closureConvertBlocks $
               BasicBlockGraph bid rk (caseblock |*><*| oldbodygraph)

        proc <- ilmPutProc $ closureConvertedProc (envVar:(fnVars f)) f newbody
        return (envId, proc)

    mapBasicBlock f (BasicBlockGraph entry rk bg) = BasicBlockGraph entry rk (f bg)

    -- Making environment passing explicit simply means rewriting calls
    -- of closure variables from   v(args...)   ==>   v_proc(v_env, args...).
    makeEnvPassingExplicit fn =
      let mapBlock g = mapGraphBlocks (mapBlock' go) g in
      fn { fnBody = mapBasicBlock mapBlock (fnBody fn) }
        where
          go :: Insn e x -> Insn e x
          go insn = case insn of
            ILabel   {}      -> insn
            ILetVal  {}      -> insn
            ILetFuns ids fns -> ILetFuns ids $ map makeEnvPassingExplicit fns
            ILast cf -> case cf of
              CFCont {} -> insn
              CFCase {} -> insn
              CFCall b t v vs ->
                case Map.lookup (tidIdent v) infoMap of
                  Nothing -> insn
                  -- The only really interesting case: call to let-bound function!
                  Just (f, envid) ->
                    let env = fakeCloVar envid in
                    ILast $ CFCall b t (fnVar f) (env:vs) -- Call proc with env as first arg.
                    -- We don't know the env type here, since we don't
                    -- pre-collect the set of closed-over envs from other procs.
                    -- This works because (A) we never type check ILExprs, and
                    -- (B) the LLVM codegen doesn't check the type field in this case.

--------------------------------------------------------------------

closureConvertedProc :: [MoVar] -> CFFn -> Blocks -> ILM CCProc
closureConvertedProc procArgs f (newbody, numPreds) = do
  case fnVar f of
    TypedId (FnType _ ftrange _ _) id ->
       return $ Proc ftrange id procArgs (fnRange f) newbody numPreds
    tid -> error $ "Expected closure converted proc to have fntype, had " ++ show tid

--------------------------------------------------------------------

-- Canonicalize single-consequent cases to unconditional branches,
-- and use the first case as the default for exhaustive pattern matches.
-- mkSwitch :: MoVar -> [(CtorId, BlockId)] -> Maybe BlockId -> Occurrence MonoType -> ILLast
mkSwitch _ [arm]      Nothing _   = ILBr   (snd arm) []
mkSwitch v (a:arms)   Nothing occ = ILCase v arms (Just $ snd a) occ
mkSwitch v    arms    def     occ = ILCase v arms def            occ

--------------------------------------------------------------------

-- This little bit of unpleasantness is needed to ensure that we
-- don't need to create gcroot slots for the phi nodes corresponding
-- to blocks inserted from using CPS-like calls.
-- TODO we can probably do this as a Block->Block translation...
mergeCallNamingBlocks blocks numpreds = go Map.empty [] blocks
  where go !subst !acc !blocks =
         case blocks of
           [] -> finalize acc subst
           [b] -> go subst (b:acc) []
           (x:y:zs) ->
              case mergeAdjacent subst x y of
                Just (m,s) -> go s        acc  (m:zs)
                Nothing    -> go subst (x:acc) (y:zs)
        mergeAdjacent :: Map MoVar MoVar
                      -> (BlockEntry, [Insn O O], Insn O C)
                      -> (BlockEntry, [Insn O O], Insn O C)
               -> Maybe ((BlockEntry, [Insn O O], Insn O C), Map MoVar MoVar)
        mergeAdjacent subst (xe,xm,xl) ((yb,yargs),ym,yl) =
          case (yargs, xl) of
            ([yarg], ILast (CFCall cb t v vs)) | cb == yb ->
                if Map.lookup yb numpreds == Just 1
                    then Just ((xe,xm++[ILetVal (tidIdent yarg) (ILCall t v vs)]++ym,yl), subst)
                    else Nothing
            (_, ILast (CFCont cb   avs))       | cb == yb ->
                if Map.lookup yb numpreds == Just 1
                    then assert (length yargs == length avs) $
                         let subst' = Map.union subst (Map.fromList $ zip yargs avs) in
                         Just ((xe,xm++ym,yl), subst' )
                    else Nothing
            _ -> Nothing

        finalize revblocks subst =
            let s v = Map.findWithDefault v v subst in
            let si  = substIn s in
            map (\(be, insns, lastinsn) -> (be, map si insns, si lastinsn))
                (reverse revblocks)

        substIn :: VarSubstFor (Insn e x)
        substIn s insn  = case insn of
             (ILabel   {}        ) -> insn
             (ILetVal  id letable) -> ILetVal id $ substVarsInLetable s letable
             (ILetFuns ids fns   ) -> ILetFuns ids $ map (substForInFn s) fns
             (ILast    cflast    ) -> case cflast of
                 (CFCont b vs)     -> ILast (CFCont b (map s vs))
                 (CFCall t b v vs) -> ILast (CFCall t b (s v) (map s vs))
                 (CFCase v cs)     -> ILast (CFCase (s v) cs)

        substForInFn :: VarSubstFor CFFn
        substForInFn s fn =
          assert (fnVars fn == map s (fnVars fn)) $
          fn { fnBody     = substInGraph s (fnBody fn) }

        substInGraph :: VarSubstFor BasicBlockGraph
        substInGraph s bbg =
          let (_, block_vs) = bbgEntry bbg in
          assert (block_vs == map s block_vs) $
          bbg { bbgBody = mapGraph (substIn s) (bbgBody bbg) }

type VarSubstFor a = (MoVar -> MoVar) -> a -> a
--------------------------------------------------------------------

-- As usual, a unique state monad, plus the accumulated procedure definitions.
-- The data type signatures are only needed for pattern match compilation, but
-- we keep them here for convenience.
data ILMState = ILMState {
    ilmUniq          :: Uniq
  , ilmBlockWrappers :: Map BlockId BlockId          -- read-write
  , ilmProcs         :: Map Ident   CCProc           -- read-write
  , ilmCtors         :: DataTypeSigs                 -- read-only per-program
}
type ILM a = State ILMState a

--------------------------------------------------------------------

ilmNewUniq = do old <- get
                put (old { ilmUniq = (ilmUniq old) + 1 })
                return (ilmUniq old)

ilmFresh :: T.Text -> ILM Ident
ilmFresh t = do u <- ilmNewUniq
                return (Ident t u)

ilmNewBlock :: String -> [Insn' O O] -> Insn' O C -> ILM (BlockId, Block')
ilmNewBlock s mids last = do u <- freshLabel
                             let id = (s, u)
                             return $ (id, mkBlock' (id,[]) mids last)

ilmAddWrapper armid id = do old <- get
                            put (old { ilmBlockWrappers = Map.insert armid id
                                      (ilmBlockWrappers old) })

ilmPutProc :: ILM CCProc -> ILM CCProc
ilmPutProc p_action = do
        p   <- p_action
        old <- get
        put (old { ilmProcs = Map.insert (procIdent p) p (ilmProcs old) })
        return p

ilmGetProc :: Ident -> ILM (Maybe CCProc)
ilmGetProc id = do
        old <- get
        return $ Map.lookup id (ilmProcs old)

--------------------------------------------------------------------

instance Structured (String, Label) where
    textOf (str, lab) _width = out $ str ++ "." ++ show lab
    childrenOf _ = []

instance UniqueMonad (State ILMState) where
  freshUnique = ilmNewUniq >>= (return . intToUnique)


instance Show (Insn e x) where
  show (ILabel   bid) = "ILabel " ++ show bid
  show (ILetVal  id letable) = "ILetVal  " ++ show id  ++ " = " ++ show letable
  show (ILetFuns ids fns   ) = "ILetFuns " ++ show ids ++ " = " ++ show ["..." | _ <- fns]
  show (ILast    cflast    ) = "ILast    " ++ show cflast


instance NonLocal Insn' where
  entryLabel (CCLabel ((_,l), _)) = l
  successors (CCLast last) = map blockLabel (block'TargetsOf (CCLast last))
                           where blockLabel (_, label) = label

block'TargetsOf :: Insn' O C -> [BlockId]
block'TargetsOf (CCLast last) =
    case last of
        ILRetVoid                   -> []
        ILRet      _                -> []
        ILBr       b _              -> [b]
        ILCase     _ cbs (Just b) _ -> b:map snd cbs
        ILCase     _ cbs Nothing  _ ->   map snd cbs

