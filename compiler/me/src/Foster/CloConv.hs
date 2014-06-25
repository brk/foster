{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns, RankNTypes #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CloConv where

import qualified Data.Text as T
import Data.Set(Set)
import qualified Data.Set as Set(empty, singleton, union, unions, notMember,
                                                      size, fromList, toList)
import Data.Map(Map)
import qualified Data.Map as Map((!), insert, lookup, empty, fromList, elems)

import Control.Monad.State

import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace(trace)

import Compiler.Hoopl

import Foster.Base
import Foster.CFG
import Foster.TypeLL
import Foster.MonoType
import Foster.Letable
import Foster.PatternMatch

-- | Closure conversion and lambda lifting.
-- |
-- | We convert from CF(G)Procs to ClosureConvertedProcs.
-- | Besides converting all Fns to Closures, we also extend
-- | the IR definition with allocation- and GC-related primitives.
-- |
-- | We also perform pattern match compilation at this stage;
-- |    as a reusult, nested patterns are translated,
-- |    via decision trees, to flat switches.

-- Previous stage: optimizeCFGs   in CFGOptimizations.hs
-- Next     stage: prepForCodegen in ILExpr.hs

-- ||||||||||||||||||||||||| Datatypes ||||||||||||||||||||||||||{{{
data CCBody = CCB_Procs [CCProc] CCMain
data CCMain = CCMain TailQ TypeLL LLVar [LLVar]
type CCProc = Proc BasicBlockGraph'
type Block' = Block Insn' C C
type BlockG = Graph Insn' C C
type BlockEntryL = BlockEntry' TypeLL

mkBlockG :: BlockEntryL -> [Insn' O O] -> Insn' O C -> BlockG
mkBlockG lab mids last = blockGraph (mkBlock' lab mids last)

mkBlock' :: BlockEntryL -> [Insn' O O] -> Insn' O C -> Block'
mkBlock' lab mids last = (blockJoin (CCLabel lab) (blockFromList mids) last)

data BasicBlockGraph' = BasicBlockGraph' { bbgpEntry :: BlockEntryL
                                         , bbgpRetK  :: BlockId
                                         , bbgpBody  :: BlockG
                                         }

-- A Closure records the information needed to generate code for a closure.
-- The environment name is recorded so that the symbol table contains
-- the right entry when mutually-recursive functions capture multiple envs.
data Closure = Closure { closureProcVar  :: LLVar
                       , closureEnvVar   :: LLVar
                       , closureCaptures :: [LLVar]
                       , closureAllocSrc :: AllocationSource
                       } deriving (Eq, Show)
type LLRootVar = LLVar
data Enabled = Disabled | Enabled Bool -- bool: gc may happen in continuation.
data Insn' e x where
        CCLabel      :: BlockEntryL                        -> Insn' C O
        CCLetVal     :: Ident   -> Letable TypeLL          -> Insn' O O
        CCLetFuns    :: [Ident] -> [Closure]               -> Insn' O O
        CCGCLoad     :: LLVar   -> LLRootVar               -> Insn' O O
        CCGCInit     :: LLVar   -> LLVar -> LLRootVar      -> Insn' O O
        CCGCKill     :: Enabled -> Set      LLRootVar      -> Insn' O O
        CCTupleStore :: [LLVar] -> LLVar -> AllocMemRegion -> Insn' O O
        CCRebindId   :: Doc     -> LLVar -> LLVar          -> Insn' O O
        CCLast       :: CCLast                             -> Insn' O C

type RootVar = LLVar

data Proc blocks =
     Proc { procReturnType :: TypeLL
          , procIdent      :: Ident
          , procVars       :: [LLVar]
          , procAnnot      :: ExprAnnot
          , procBlocks     :: blocks
          }

data CCLast = CCCont        BlockId [LLVar] -- either ret or br
            | CCCall        BlockId TypeLL Ident LLVar [LLVar] -- add ident for later let-binding
            | CCCase        LLVar [((CtorId, CtorRepr), BlockId)] (Maybe BlockId)
            deriving (Show)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| The Driver |||||||||||||||||||||||||{{{
closureConvertAndLift :: DataTypeSigs
                      -> [Ident]
                      -> Uniq
                      -> ModuleIL CFBody MonoType
                      -> (ModuleIL CCBody TypeLL, Uniq)
closureConvertAndLift dataSigs globalIds u m =
    -- We lambda lift top level functions, since we know a priori
    -- that they don't have any "real" free vars.
    -- Lambda lifting then closure converts any nested functions.
    let initialState = ILMState u Map.empty Map.empty Map.empty dataSigs in
    let (ccmain, st) = runState (closureConvertToplevel globalIds $ moduleILbody m)
                                                                 initialState in
    (ModuleIL {
          moduleILbody        = CCB_Procs (Map.elems $ ilmProcs st) ccmain
        , moduleILdecls       = map (\(s,t) -> (s, monoToLL t)) (moduleILdecls m)
        , moduleILdataTypes   = map (fmap monoToLL) (moduleILdataTypes m)
        , moduleILprimTypes   = map (fmap monoToLL) (moduleILprimTypes m)
        , moduleILsourceLines = moduleILsourceLines m
        }, (ilmUniq st))

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
       cvt _ (CFB_Call t v vs) = return (CCMain YesTail (monoToLL t) (llv v) (map llv vs))

       cvt globalized (CFB_LetFuns ids fns body) =
         let
             unliftable glbl fn =
             {-
                 trace (if (identPrefix $ tidIdent $ fnVar fn) == T.pack "problem4" then
                        "Computing unliftables for fn " ++ show (fnVar fn)
                        ++ "\nfree ids: " ++ show (fnFreeIds fn)
                        -- ++ "\nglobals: " ++ show glbl
                        ++ "\n"
                        else "") $ -}
                                  [ id | (TypedId _ id) <- fnFreeIds fn
                                       , Set.notMember id glbl]
             allUnliftables = filter (not . null)
                                     (map (unliftable globalized' ) fns)
             -- If a recursive nest of functions don't close over any other
             -- variables, they can all be globalized as long as every use
             -- of their peers happens to be a direct call. So, we'll assume
             -- we can globalize, but enforce the side condition.
             globalized' = Set.union globalized (Set.fromList ids)
             gonnaLift   = null allUnliftables
         in
          let traced = if gonnaLift then id
                          else trace ("not gonna lift " ++ show ids ++
                                 " due to unliftables " ++ show allUnliftables)
          in if traced gonnaLift
              then do _ <- mapM (lambdaLift []) fns      ; cvt globalized' body
              else do _ <- closureConvertLetFuns ids fns ; cvt globalized  body
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Lambda Lifter ||||||||||||||||||||||{{{
-- For example, if we have something like
--      let y = blah in
--      (\x -> x + y) foobar
-- then, because the lambda is directly called*,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \yy x -> x + yy
--      let y = blah in p y foobar
--
-- * implying that every call site is known, and every call site
--   has available the free variables needed by the lambda.
lambdaLift :: [MoVar] -> CFFn -> ILM CCProc
lambdaLift freeVars f = do
    newbody <- closureConvertBlocks (fnBody f)
    -- Add *all* of the free variables to the signature of the lambda-lifted
    -- procedure. We could (should?) add only some of them, like Chez Scheme.
    -- (As it happens, at the moment we only do lambda-lifting for top-level
    --  functions, which have no free variables by definition. But still.)
    let liftedProcVars = freeVars ++ fnVars f
    ilmPutProc (closureConvertedProc liftedProcVars f newbody)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- TyConApp translates to LLNamedType and drops the arg types.
-- This is because the LLVM backend constructs canonical types
-- for each datatype before codegenning the module body, and
-- references to the datatype (i.e. via TyConApp) simply look up
-- the canonical type using the data type's name.
monoToLL :: MonoType -> TypeLL
monoToLL mt = case mt of
   PrimInt       isb            -> LLPrimInt       isb
   PrimFloat64                  -> LLPrimFloat64
   TyConApp      dtn _tys       -> LLNamedType dtn
   TupleType     tys            -> llTupleType     (map q tys)
   StructType    tys            -> LLStructType    (map q tys)
   CoroType      s t            -> LLCoroType      (q s) (q t)
   ArrayType     t              -> LLArrayType     (q t)
   PtrType       t              -> LLPtrType       (q t)
   PtrTypeUnknown               -> LLPtrTypeUnknown
   FnType     d r _p cc FT_Proc -> LLProcType (map q d)  (q r) cc
   FnType     d r _p cc FT_Func -> LLPtrType (LLStructType [procty,envty])
                              where procty = LLProcType (envty:(map q d)) (q r) cc
                                    envty  = LLPtrType (LLPrimInt I8)
 where q = monoToLL
       llTupleType tys = LLPtrType (LLStructType tys)

llv :: MoVar -> LLVar
llv v = fmap monoToLL v

llb :: BlockEntry' MonoType -> BlockEntry' TypeLL
llb (s,vs) = (s, map llv vs)

-- ||||||||||||||||||||||||| Closure Conversion, pt 1 |||||||||||{{{
-- We serialize a basic block graph by computing a depth-first search
-- starting from the graph's entry block.
closureConvertBlocks :: BasicBlockGraph -> ILM BasicBlockGraph'
closureConvertBlocks bbg = do
   g' <- rebuildGraphM (case bbgEntry bbg of (bid, _) -> bid) (bbgBody bbg)
                                                                       transform
   return BasicBlockGraph' {
                 bbgpEntry = llb (bbgEntry bbg),
                 bbgpRetK  =      bbgRetK  bbg,
                 bbgpBody  = g'
          }
  where
      transform :: Insn e x -> ILM (Graph Insn' e x)
      transform insn = case insn of
        ILabel l                -> do return $ mkFirst $ CCLabel (llb l)
        ILetVal id val          -> do return $ mkMiddle $ CCLetVal id (fmap monoToLL val)
        ILetFuns ids fns        -> do closures <- closureConvertLetFuns ids fns
                                      return $ mkMiddle $ CCLetFuns ids closures
        ILast (CFCont b vs)     -> do return $ mkLast $ CCLast (CCCont b (map llv vs))
        ILast (CFCall b t v vs) -> do id <- ilmFresh (T.pack ".call")
                                      return $ mkLast $ CCLast (CCCall b (monoToLL t) id (llv v) (map llv vs))
        ILast (CFCase a arms) -> do
           allSigs <- gets ilmCtors
           let dt = compilePatterns arms allSigs
           let usedBlocks = eltsOfDecisionTree dt
           let _unusedPats = [pat | (CaseArm pat bid _ _ _) <- arms
                            , Set.notMember bid usedBlocks]
           -- TODO print warning if any unused patterns
           (BlockFin blocks id _) <- compileDecisionTree a dt
           return $ (mkLast $ CCLast $ CCCont id []) |*><*| blocks
          where
            -- The decision tree we get from pattern-match compilation may
            -- contain only a subset of the pattern branches.
            eltsOfDecisionTree :: (Show a, Ord a) => DecisionTree a t -> Set a
            eltsOfDecisionTree (DT_Fail   _) = Set.empty
            eltsOfDecisionTree (DT_Leaf a _) = Set.singleton a
            eltsOfDecisionTree (DT_Switch _ idsDts maybeDt) = Set.union
               (Set.unions (map (\(_, dt) -> eltsOfDecisionTree dt) idsDts))
               (case maybeDt of
                   Just dt -> eltsOfDecisionTree dt
                   Nothing -> Set.empty)

closureConvertLetFuns :: [Ident] -> [CFFn] -> ILM [Closure]
closureConvertLetFuns ids fns = do
    let mkProcType ft id = case ft of
                 FnType s t p cc FT_Func -> FnType s t p cc FT_Proc
                 other -> error $ "CloConv.hs: mkProcType given non-function type?? " ++ show id ++ " ; " ++ show other

    let mkProcVar  (TypedId ft id) = TypedId (mkProcType ft id) id

    let proc_vars = map (mkProcVar . fnVar) fns
    let genFreshId id = do rv <- ilmFresh (".env." `prependedTo` identPrefix id)
                           return $ -- trace ("genFreshId for " ++ show id ++ " is " ++ show rv ++ " ;; " ++ show (map fnIdent fns) ++ "; fn: " ++ show (map pretty (tail fns)))
                                      rv
    cloEnvIds <- mapM genFreshId ids
    let infoMap = Map.fromList (zip ids (zip proc_vars cloEnvIds))
    let idfns = zip ids fns
    mapM (closureOfKnFn infoMap) idfns
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data BlockFin = BlockFin BlockG           -- new blocks generated
                         BlockId          -- entry block for decision tree logic
                         DT_Ord           -- subtree to use for hash-consing

bogusVar (id, _) = TypedId (PrimInt I1) id

-- ||||||||||||||||||||||||| Decision Tree Compilation ||||||||||{{{

-- A specialized variant of DecisionTree, for easier hash-consing.
data DT_Ord =
               DTO_Leaf BlockId [(TypedId MonoType, Occurrence MonoType)]
            |  DTO_Switch (Occurrence MonoType)
                          [((CtorId, CtorRepr), DT_Ord)]
                          (Maybe DT_Ord)
               deriving (Eq, Ord)

compileDecisionTree :: MoVar -> DecisionTree BlockId MonoType -> ILM BlockFin
-- Translate an abstract decision tree to ILBlocks, also returning
-- the label of the entry block into the decision tree logic.
-- For now, we don't do any available values computation, which means that
-- nested pattern matching will load the same subterm multiple times:
-- once on the path to a leaf, and once more inside the leaf itself.

compileDecisionTree _scrutinee (DT_Fail ranges) =
  error $ "can't do dt_FAIL yet, for scrutinee " ++ show _scrutinee
            ++ "\n" ++ concatMap highlightFirstLine ranges

compileDecisionTree _scrutinee (DT_Leaf armid []) = do
        return $ BlockFin emptyClosedGraph armid (DTO_Leaf armid [])

-- Because of the way decision trees can be copied, we can end up with
-- multiple DT_Leaf nodes for the same armid. Since we don't want to emit
-- bindings multiple times, we associate each armid with the id of a basic
-- block which binds the arm's free variables, and make all the leafs jump
-- to the wrapper instead of directly to the arm.
compileDecisionTree scrutinee (DT_Leaf armid varoccs) = do
        wrappers <- gets ilmBlockWrappers
        case Map.lookup armid wrappers of
           Just id -> do return $ BlockFin emptyClosedGraph id (DTO_Leaf armid varoccs)
           Nothing -> do let binders = map (emitOccurrence scrutinee) varoccs
                         (id, block) <- ilmNewBlock ".leaf" binders (CCLast $ CCCont armid []) -- TODO
                         ilmAddWrapper armid id
                         return $ BlockFin block id (DTO_Leaf armid varoccs)

compileDecisionTree scrutinee (DT_Switch occ subtrees maybeDefaultDt) = do
    let splitBlockFin (BlockFin blocks id dto) = (blocks, id, dto)

    let (ctors, subdts) = unzip subtrees
    fins  <- mapM (compileDecisionTree scrutinee) subdts
    let (blockss, ids, subtrees' ) = unzip3 (map splitBlockFin fins)
    (dblockss, maybeDefaultId, maybeDefaultDt' ) <- case maybeDefaultDt of
       Nothing -> do return (emptyClosedGraph, Nothing, Nothing)
       Just dt -> do (BlockFin dblockss did dto) <- compileDecisionTree scrutinee dt
                     return (dblockss, Just did, Just dto)
    let dto = DTO_Switch occ (zip ctors subtrees' ) maybeDefaultDt'
    (id, blockg) <- do
       cached <- gets ilmDecisionTrees
       case Map.lookup dto cached of
         Just id -> do return (id, emptyClosedGraph)
         Nothing -> do scrut_occ_id <- ilmFresh (T.pack "scrut.occ")
                       let scrut_occ = TypedId (occType scrutinee occ) scrut_occ_id
                       (id, blockg) <- ilmNewBlock ".dt.switch"
                         [emitOccurrence scrutinee (scrut_occ, occ)]
                         (CCLast $ mkSwitch (llv scrut_occ) (zip ctors ids) maybeDefaultId)
                       ilmAddDecisionTree dto id
                       return (id, blockg)
    let catClosedGraphs = foldr (|*><*|) emptyClosedGraph
    return $ BlockFin (blockg |*><*| catClosedGraphs blockss |*><*| dblockss) id dto

llOcc occ = map (\(i,c) -> (i, fmap monoToLL c)) occ

emitOccurrence :: MoVar -> (TypedId MonoType, Occurrence MonoType) -> Insn' O O
emitOccurrence scrutinee (v, occ) =
    CCLetVal (tidIdent v) $ ILOccurrence (monoToLL $ tidType v)
                                         (llv scrutinee) (llOcc occ)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

type InfoMap = Map Ident (MoVar, Ident) -- fn ident => (proc_var, env id)

fnFreeIds :: CFFn -> [MoVar]
fnFreeIds fn = freeTypedIds fn

-- ||||||||||||||||||||||||| Closure Conversion, pt 2 |||||||||||{{{
closureOfKnFn :: InfoMap
              -> (Ident, CFFn)
              -> ILM Closure
closureOfKnFn infoMap (self_id, fn) = do
    let varsOfClosure = closedOverVarsOfKnFn

    let envId  = snd (infoMap Map.! self_id)
    -- Note that this env var has a precise type! The other's is missing.
    let envVar = TypedId (TupleType $ map tidType varsOfClosure) envId

    -- Note that this will also rewrite recursive calls in nested functions,
    -- which changes the set of closed-over variables for the nested function
    -- (from outer fn to outer env).
    let transformedFn = makeEnvPassingExplicit envVar fn
    newproc          <- closureConvertFn transformedFn envVar varsOfClosure
    let procid        = TypedId (procType newproc) (procIdent newproc)
    return $ Closure procid (llv envVar) (map llv varsOfClosure)
                   (AllocationSource (show procid ++ ":")
                                     (rangeOf $ procAnnot newproc))
  where
    procType proc =
      let retty = procReturnType proc in
      let argtys = map tidType (procVars proc) in
      LLProcType argtys retty FastCC

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
        concatMap (\v -> let tid = tidIdent v in
                         case Map.lookup tid infoMap of
                              Nothing ->   [v]
                              Just (_, envid) -> capturedVarsFor tid v envid) $
             -- trace ("nonGlobalVars for " ++ show self_id ++ " is " ++ show nonGlobalVars ++ "\n" ++ show (pretty fn))
                nonGlobalVars

    fakeCloVar id = TypedId fakeCloEnvType id
                      where fakeCloEnvType = TyConApp "Foster$GenericClosureEnvPtr" []

    -- This is where the magic happens: given a function and its free variables,
    -- we create a procedure which also takes an extra (strongly-typed) env ptr
    -- argument. The new body does case analysis to bind the free variable names
    -- to the contents of the slots of the environment.
    closureConvertFn :: CFFn -> MoVar -> [MoVar] -> ILM CCProc
    closureConvertFn f envVar varsOfClosure = do
        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- do
            let BasicBlockGraph bodyentry rk oldbodygraph = fnBody f
            let cfcase = CFCase envVar [
                           (CaseArm (PR_Tuple norange t (map patVar varsOfClosure))
                                    (fst bodyentry)
                                    Nothing
                                    varsOfClosure
                                    norange) ]
                        where t        = tidType envVar
                              patVar a = PR_Atom $ P_Variable norange a
                              norange  = MissingSourceRange ""
            -- We change the entry block of the new body (versus the old).
            lab <- freshLabel
            let bid = ((".env.caseof", lab), [envVar])
            let caseblock = mkFirst (ILabel bid) <*>
                            mkMiddles []         <*>
                            mkLast (ILast cfcase)
            closureConvertBlocks $
               BasicBlockGraph bid rk (caseblock |*><*| oldbodygraph)

        ilmPutProc $ closureConvertedProc (envVar:(fnVars f)) f newbody

    mapBasicBlock f (BasicBlockGraph entry rk bg) = BasicBlockGraph entry rk (f bg)

    -- Making environment passing explicit simply means rewriting calls
    -- of closure variables from   v(args...)   ==>   v_proc(v_env, args...).
    makeEnvPassingExplicit envVar fn =
      let mapBlock :: forall e x. Graph' Block Insn e x -> Graph' Block Insn e x
          mapBlock g = mapGraphBlocks (mapBlock' go) g in
      fn { fnBody = mapBasicBlock mapBlock (fnBody fn) }
        where
          go :: Insn e x -> Insn e x
          go insn = case insn of
            ILabel   {}      -> insn
            ILetVal  {}      -> insn
            ILetFuns ids fns -> ILetFuns ids $ map (makeEnvPassingExplicit envVar) fns
            ILast cf -> case cf of
              CFCont {} -> insn
              CFCase {} -> insn
              CFCall b t v vs ->
                case Map.lookup (tidIdent v) infoMap of
                  Nothing -> insn
                  -- The only really interesting case: call to let-bound function!
                  Just (proc_var, envid) ->
                    let env = if envid == tidIdent envVar
                               then envVar
                               else fakeCloVar envid in
                    ILast $ CFCall b t proc_var (env:vs) -- Call proc with env as first arg.
                    -- We don't know the env type here, since we don't
                    -- pre-collect the set of closed-over envs from other procs.
                    -- This works because (A) we never type check ILExprs, and
                    -- (B) the LLVM codegen doesn't check the type field in this case.

--------------------------------------------------------------------

closureConvertedProc :: [MoVar] -> CFFn -> BasicBlockGraph' -> ILM CCProc
closureConvertedProc procArgs f newbody = do
  case fnVar f of
    TypedId (FnType _ ftrange _ _ _) id ->
       return $ Proc (monoToLL ftrange) id (map llv procArgs) (fnAnnot f) newbody
    tid -> error $ "Expected closure converted proc to have fntype, had " ++ show tid
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- Canonicalize single-consequent cases to unconditional branches,
-- and use the first case as the default for exhaustive pattern matches.
-- mkSwitch :: LLVar -> [(CtorId, BlockId)] -> Maybe BlockId -> CCLast
mkSwitch _ [arm]      Nothing = CCCont (snd arm) []
mkSwitch v (a:arms)   Nothing = CCCase v arms (Just $ snd a)
mkSwitch v    arms    def     = CCCase v arms def

--------------------------------------------------------------------

-- ||||||||||||||||||||||||| ILM Monad ||||||||||||||||||||||||||{{{
-- As usual, a unique state monad, plus the accumulated procedure definitions.
-- The data type signatures are only needed for pattern match compilation, but
-- we keep them here for convenience.
data ILMState = ILMState {
    ilmUniq          :: Uniq
  , ilmBlockWrappers :: Map BlockId BlockId          -- read-write
  , ilmDecisionTrees :: Map DT_Ord  BlockId          -- read-write
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

ilmNewBlock :: String -> [Insn' O O] -> Insn' O C -> ILM (BlockId, BlockG)
ilmNewBlock s mids last = do u <- freshLabel
                             let id = (s, u)
                             return $ (id, mkBlockG (id,[]) mids last)

ilmAddDecisionTree dto id = do old <- get
                               put old { ilmDecisionTrees = Map.insert dto id
                                        (ilmDecisionTrees old) }

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
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{
renderCC m put = if put then putDoc (pretty m) >>= (return . Left)
                        else return . Right $ show (pretty m)

instance Structured (String, Label) where
    textOf (str, lab) _width = text $ str ++ "." ++ show lab
    childrenOf _ = []

instance UniqueMonad (State ILMState) where
  freshUnique = ilmNewUniq >>= (return . intToUnique)

instance Pretty BlockG where
  pretty bb = foldGraphNodes prettyInsn' bb empty

prettyInsn' :: Insn' e x -> Doc -> Doc
prettyInsn' i d = d <$> pretty i

prettyBlockId (b,l) = text b <> text "." <> text (show l)

instance Pretty Enabled where
  pretty (Enabled _) = text "Enabled"
  pretty Disabled    = text "Disabled"

instance Pretty (Set LLRootVar) where
  pretty s = list (map pretty $ Set.toList s)

instance Pretty (Insn' e x) where
  pretty (CCLabel   bentry     ) = line <> prettyBlockId (fst bentry) <+> list (map pretty (snd bentry))
  pretty (CCLetVal id letable  ) = indent 4 (text "let" <+> text (show id) <+> text "="
                                                       <+> pretty letable)
  pretty (CCLetFuns ids fns    ) = let recfun = if length ids == 1 then "fun" else "rec" in
                                  indent 4 (align $
                                   vcat [text recfun <+> text (show id) <+> text "=" <+> pretty fn
                                        | (id,fn) <- zip ids fns])
  pretty (CCGCLoad  loadedvar root) = indent 4 $ dullwhite $ text "load from" <+> pretty root <+> text "to" <+> pretty loadedvar
  pretty (CCGCInit  _  srcvar root) = indent 4 $ dullgreen $ text "init root" <+> pretty root <+> text ":=" <+> pretty srcvar
  pretty (CCGCKill  Disabled roots) = indent 4 $ (dullwhite $ text "kill roots") <+> prettyR roots <+> pretty Disabled
  pretty (CCGCKill  enabled  roots) | Set.size roots == 0
                                    = indent 4 $ (dullwhite $ text "kill roots") <+> prettyR roots <+> pretty enabled
  pretty (CCGCKill  enabled  roots) = indent 4 $ (dullred  $ text "kill roots") <+> prettyR roots <+> pretty enabled
  pretty (CCTupleStore vs tid _memregion) = indent 4 $ text "stores " <+> pretty vs <+> text "to" <+> pretty tid
  pretty (CCRebindId d v1 v2) = indent 4 $ text "REPLACE " <+> pretty v1 <+> text "WITH" <+> pretty v2 <+> parens d
  pretty (CCLast    cclast     ) = pretty cclast

prettyR roots = (if Set.size roots > 15 then text "..." else pretty roots) <> parens (pretty (Set.size roots))

isProc ft = case ft of FnType _ _ _ _ FT_Proc -> True
                       _                      -> False

isFunc ft = case ft of FnType _ _ _ _ FT_Func     -> True
                       PtrType (StructType (t:_)) -> isProc t
                       _                          -> False

instance Pretty CCLast where
  pretty (CCCont bid       vs) = text "cont" <+> prettyBlockId bid <+>              list (map pretty vs)
  pretty (CCCall bid _ _ v vs) =
        case tidType v of
          LLProcType _ _ _ -> text ("call (proc)") <+> prettyBlockId bid <+> pretty v <+> list (map pretty vs)
          _                -> text ("call (func)") <+> prettyBlockId bid <+> pretty v <+> list (map pretty vs)
  pretty (CCCase v arms def) = align $
    text "case" <+> pretty v <$> indent 2
       ((vcat [ arm (text "of" <+> pretty ctor) bid
              | (ctor, bid) <- arms
              ]) <> (case def of Nothing -> empty
                                 Just bid -> line <> arm (text "default:") bid))

   where arm lhs bid = fill 20 lhs <+> text "->" <+> prettyBlockId bid

prettyTypedVar v = pretty (tidIdent v) <+> text "::" <+> pretty (tidType v)

instance Pretty Closure where
  pretty clo = text "(Closure" <+> text "env =(" <> pretty (tidIdent $ closureEnvVar clo)
                         <>  text ") proc =(" <+> pretty (closureProcVar clo)
                         <+> text ") captures" <+> text (show (map prettyTypedVar (closureCaptures clo)))
                         <+> text ")"

instance Pretty BasicBlockGraph' where
 pretty bbg =
         (indent 4 (text "ret k =" <+> pretty (bbgpRetK bbg)
                <$> text "entry =" <+> pretty (fst $ bbgpEntry bbg)
                <$> text "------------------------------"))
          <> pretty (bbgpBody bbg)

instance Pretty CCBody where
 pretty (CCB_Procs procs _) = vcat (map (\p -> line <> pretty p) procs)

instance Pretty TypeLL where pretty t = text (show t) -- TODO fix

instance Pretty CCProc where
 pretty proc = pretty (procIdent proc) <+> list (map pretty (procVars proc))
               <$> text "{"
               <$> indent 4 (pretty (procBlocks proc))
               <$> text "}"

instance Show (Insn e x) where
  show (ILabel   bid) = "ILabel " ++ show bid
  show (ILetVal  id letable) = "ILetVal  " ++ show id  ++ " = " ++ show letable
  show (ILetFuns ids fns   ) = "ILetFuns " ++ show ids ++ " = " ++ show ["..." | _ <- fns]
  show (ILast    cflast    ) = "ILast    " ++ show cflast

instance NonLocal Insn' where
  entryLabel (CCLabel ((_,l), _)) = l
  successors (CCLast last) = map blockLabel (block'TargetsOf (CCLast last))
                           where blockLabel (_, label) = label

instance FosterNode Insn' where branchTo bid = CCLast $ CCCont bid []

block'TargetsOf :: Insn' O C -> [BlockId]
block'TargetsOf (CCLast last) =
    case last of
        CCCont     b _            -> [b]
        CCCall     b _ _ _ _      -> [b]
        CCCase     _ cbs (Just b) -> b:map snd cbs
        CCCase     _ cbs Nothing  ->   map snd cbs


instance IntSizedBits MonoType where
        intSizeBitsOf (PrimInt isb) = isb
        intSizeBitsOf _ = error $ "Unable to compute IntSizedBits for non-PrimInt type"

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


-- canGCCalled  v = let rv = canGCF v in if rv then {- trace ("canGCF: " ++ show v) -} rv else rv
--canGCLetable msg l = let rv = canGC msg l in if rv then {- trace ("canGCL: " ++ show l) -} rv else rv

