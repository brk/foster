{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Control.Monad.State
import Data.Set(Set)
import qualified Data.Set as Set(empty, singleton, union, unions, notMember,
                                                       insert, fromList, toList)
import Data.Map(Map)
import qualified Data.Map as Map((!), insert, lookup, empty, fromList, elems)
import qualified Data.Text as T
import qualified Data.List as List(and)

import Compiler.Hoopl

import Debug.Trace(trace)

import Foster.Base
import Foster.CFG
import Foster.MonoType
import Foster.Letable
import Foster.PatternMatch
import Foster.Output(out, Output)

--------------------------------------------------------------------

-- | Performs closure conversion and lambda lifting, and also
-- | transforms back from Hoopl's CFG representation to lists-of-blocks.
-- |
-- | We also perform pattern match compilation at this stage.
-- |
-- | The primary differences in the general structure are:
-- |  #. LetFuns replaced with Closures
-- |  #. Module  replaced with ILProgram
-- |  #. Fn replaced with ProcDef
-- |  #. Decision trees replaced with flat switches

--------------------------------------------------------------------

-- ILClosure records the information needed to generate code for a closure.
-- The environment name is recorded so that the symbol table contains
-- the right entry when mutually-recursive functions capture multiple envs.
data ILClosure = ILClosure { ilClosureProcIdent :: MoVar
                           , ilClosureEnvIdent  :: Ident
                           , ilClosureCaptures  :: [MoVar]
                           , ilClosureAllocSrc  :: AllocationSource
                           } deriving Show

-- A program consists of top-level data types and mutually-recursive procedures.
data ILProgram = ILProgram (Map Ident ILProcDef)
                           [MoExternDecl]
                           [DataType MonoType]
                           [ILProcDef] -- These are the original toplevel functions.
                           SourceLines

data ILExternDecl = ILDecl String MonoType deriving (Show)

-- Procedures can be polymorphic when an ILProgram is first created,
-- but after monomorphization, all the polymorphism should be gone.
data ILProcDef =
     ILProcDef { ilProcReturnType :: MonoType
               , ilProcIdent      :: Ident
               , ilProcVars       :: [MoVar]
               , ilProcRange      :: SourceRange
               , ilProcBlocks     :: [ILBlock]
               , ilProcBlockPreds :: Map BlockId Int
               }

-- The standard definition of a basic block and its parts.
data ILBlock  = Block BlockEntry [ILMiddle] ILLast {- num preds? -}
data ILMiddle = ILLetVal      Ident    Letable
              -- This is equivalent to MinCaml's make_closure ...
              | ILClosures    [Ident] [ILClosure]
              deriving Show

-- The only difference from CFLast to ILLast is the decision tree in ILCase.
data ILLast = ILRetVoid
            | ILRet      MoVar
            | ILBr       BlockId [MoVar]
            | ILCase     MoVar [(CtorId, BlockId)] (Maybe BlockId) (Occurrence MonoType)
--------------------------------------------------------------------

closureConvertAndLift :: DataTypeSigs
                      -> [Ident]
                      -> Uniq
                      -> (ModuleIL CFBody MonoType)
                      -> ILProgram
closureConvertAndLift dataSigs globalIds u m =
    -- We lambda lift top level functions, since we know a priori
    -- that they don't have any "real" free vars.
    -- Lambda lifting then closure converts any nested functions.
    let initialState = ILMState u Map.empty Map.empty dataSigs in
    let (topProcs, newstate) = runState (closureConvertToplevel globalIds $ moduleILbody m)
                                        initialState in
    let decls = map (\(s,t) -> MoExternDecl s t) (moduleILdecls m) in
    let dts = moduleILprimTypes m ++ moduleILdataTypes m in
    ILProgram (ilmProcDefs newstate) decls dts topProcs (moduleILsourceLines m)

instance Show (Insn e x) where
  show (ILabel   bid) = "ILabel " ++ show bid
  show (ILetVal  id letable) = "ILetVal  " ++ show id  ++ " = " ++ show letable
  show (ILetFuns ids fns   ) = "ILetFuns " ++ show ids ++ " = " ++ show ["..." | _ <- fns]
  show (ILast    cflast    ) = "ILast    " ++ show cflast

closureConvertToplevel :: [Ident] -> CFBody -> ILM [ILProcDef]
closureConvertToplevel globalIds body = do
  (procdefs, _) <- cvt ([], Set.fromList globalIds) body
  return procdefs
     where
       -- Iterate through the SCCs of definitions, keeping track of a state
       -- parameter (the set of globalized variables, which need not appear in
       -- a function's environment). For each definition, if it doesn't need
       -- an environment, we'll lift it; otherwise, closure convert it.
       -- We directly return a list of the top-level proc definitions, and also
       -- (via the ILM monad) a list of all procs generated, including those
       -- from nested functions.
       cvt :: ([ILProcDef], Set Ident) -> CFBody -> ILM ([ILProcDef], Set Ident)
       cvt (topprocs, globalized) (CFB_Call {} {- tc t v vs -}) =
         return (topprocs, globalized)

       cvt (topprocs, globalized) (CFB_LetFuns ids fns body) =
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
              then do newprocs <- mapM (\fn -> lambdaLift fn []) fns
                      cvt (newprocs ++ topprocs, globalized' ) body
              else do _        <- closureConvertLetFuns ids fns
                      cvt (            topprocs, globalized  ) body

-- For example, if we have something like
--      let y = blah in
--      (\x -> x + y) foobar
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \yy x -> x + yy
--      let y = blah in p y foobar
lambdaLift :: CFFn -> [MoVar] -> ILM ILProcDef
lambdaLift f freeVars = do
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

jumpTo bbg = case bbgEntry bbg of (bid, _) -> ILast $ CFCont bid undefined

type ClosureConvertedBlocks = ([ILBlock], Map BlockId Int)

-- We serialize a basic block graph by computing a depth-first search
-- starting from the graph's entry block.
closureConvertBlocks :: BasicBlockGraph -> ILM ClosureConvertedBlocks
closureConvertBlocks bbg = do
   let cfgBlocks = map (splitBasicBlock . basicBlock) $
                     preorder_dfs $ mkLast (jumpTo bbg) |*><*| bbgBody bbg
   -- Because we do a depth-first search, "renaming" blocks are guaranteed
   -- to be adjacent to each other in the list.
   let cfgBlocks' = mergeCallNamingBlocks cfgBlocks (bbgNumPreds bbg)
   blocks <- mapM closureConvertBlock cfgBlocks'
   return (concat blocks, bbgNumPreds bbg)
  where
    -- A BasicBlock which ends in a decision tree will, in the general case,
    -- expand out to multiple blocks to encode the tree.
    closureConvertBlock (bid, mids, last) = do
        (blocks, lastmid, newlast) <- ilLast last
        newmids <- mapM closureConvertMid mids
        return $ Block bid (newmids ++ lastmid) newlast : blocks
     where
      -- Translate continuation application to br or ret, as appropriate.
      cont k vs =
           case (k == bbgRetK bbg, vs) of
                (True,  [] ) -> ILRetVoid
                (True,  [v]) -> ILRet   v
                (True,   _ ) -> error $ "ILExpr.hs:No support for multiple return values yet\n" ++ show vs
                (False,  _ ) -> ILBr k vs

      ilLast :: Insn O C -> ILM ([ILBlock], [ILMiddle], ILLast)
      ilLast (ILast last) =
        case last of
           -- [[f k vs]] ==> let x = f vs in [[k x]]
           CFCall k t v vs -> do
               id <- ilmFresh (T.pack ".call")
               return ([], [ILLetVal id (ILCall t v vs)], cont k [TypedId t id])
           CFCont k vs -> return ([], [], cont k vs)
           CFCase a pbs    -> do
               allSigs  <- gets ilmCtors
               let dt = compilePatterns pbs allSigs
               let usedBlocks = eltsOfDecisionTree dt
               let _unusedPats = [pat | (pat, bid) <- pbs
                                , Set.notMember bid usedBlocks]
               -- TODO print warning if any unused patterns
               (BlockFin blocks id) <- compileDecisionTree a dt
               return $ (blocks, [], ILBr id [])
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

      closureConvertMid :: Insn O O -> ILM ILMiddle
      closureConvertMid mid =
        case mid of
          ILetVal id val -> return $ ILLetVal id val
          ILetFuns ids fns -> do closures <- closureConvertLetFuns ids fns
                                 return $ ILClosures ids closures

closureConvertLetFuns :: [Ident] -> [CFFn] -> ILM [ILClosure]
closureConvertLetFuns ids fns = do
    let genFreshId id = ilmFresh (".env." `prependedTo` identPrefix id)
    cloEnvIds <- mapM genFreshId ids
    let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
    let idfns = zip ids fns
    mapM (closureOfKnFn infoMap) idfns

data BlockFin = BlockFin [ILBlock]      -- new blocks generated
                         BlockId        -- entry block for decision tree logic

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
                         (id, block) <- ilmNewBlock ".leaf" binders (ILBr armid []) -- TODO
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
        (id, block) <- ilmNewBlock ".dt.switch" []
                         (mkSwitch scrutinee (zip ctors ids) maybeDefaultId occ)
        return $ BlockFin (block : concat blockss ++ dblockss) id

emitOccurrence :: MoVar -> (Ident, Occurrence MonoType) -> ILMiddle
emitOccurrence scrutinee (id, occ) = ILLetVal id (ILOccurrence scrutinee occ)

type InfoMap = Map Ident (CFFn, Ident) -- fn ident => (fn, env id)

fnFreeIds :: CFFn -> [MoVar]
fnFreeIds fn = freeTypedIds fn

closureOfKnFn :: InfoMap
              -> (Ident, CFFn)
              -> ILM ILClosure
closureOfKnFn infoMap (self_id, fn) = do
    let varsOfClosure = closedOverVarsOfKnFn
    let transformedFn = makeEnvPassingExplicitFn fn
    (envVar, newproc) <- closureConvertFn transformedFn varsOfClosure
    let procid        = TypedId (procType newproc) (ilProcIdent newproc)
    return $ ILClosure procid envVar varsOfClosure
                   (AllocationSource (show procid ++ ":") (ilProcRange newproc))
  where
    procType proc =
      let retty = ilProcReturnType proc in
      let argtys = map tidType (ilProcVars proc) in
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
    closureConvertFn :: CFFn -> [MoVar] -> ILM (Ident, ILProcDef)
    closureConvertFn f varsOfClosure = do
        let envId  = snd (infoMap Map.! self_id)
        -- Note that this env var has a precise type! The other's is missing.
        let envVar = TypedId (TupleType $ map tidType varsOfClosure) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- do
            let BasicBlockGraph bodyentry rk oldbodygraph numPreds = fnBody f
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
                               (incrPredecessorsDueTo (ILast cfcase) numPreds)

        proc <- ilmPutProc $ closureConvertedProc (envVar:(fnVars f)) f newbody
        return (envId, proc)

    mapBasicBlock f (BasicBlockGraph entry rk bg np) = BasicBlockGraph entry rk (f bg) np

    -- Making environment passing explicit simply means rewriting calls
    -- of closure variables from   v(args...)   ==>   v_proc(v_env, args...).
    makeEnvPassingExplicitFn fn =
      let mapBlock g = graphMapBlocks (blockMapNodes3 (id, mid, fin)) g in
      fn { fnBody = mapBasicBlock mapBlock (fnBody fn) }
        where
              mid :: Insn O O -> Insn O O
              mid m = case m of
                ILetVal  {}      -> m
                ILetFuns ids fns -> ILetFuns ids
                                         (map makeEnvPassingExplicitFn fns)

              fin :: Insn O C -> Insn O C
              fin z@(ILast cf) = case cf of
                CFCont {} -> z
                CFCase {} -> z
                CFCall b t v vs ->
                  case Map.lookup (tidIdent v) infoMap of
                    Nothing -> z
                    -- The only really interesting case: call to let-bound function!
                    Just (f, envid) ->
                      let env = fakeCloVar envid in
                      ILast $ CFCall b t (fnVar f) (env:vs) -- Call proc with env as first arg.
                      -- We don't know the env type here, since we don't
                      -- pre-collect the set of closed-over envs from other procs.
                      -- This works because (A) we never type check ILExprs, and
                      -- (B) the LLVM codegen doesn't check the type field in this case.

--------------------------------------------------------------------

closureConvertedProc :: [MoVar]
                     -> CFFn
                     -> ClosureConvertedBlocks
                     -> ILM ILProcDef
closureConvertedProc procArgs f (newbody, numPreds) = do
  let (TypedId ft id) = fnVar f
  case ft of
    FnType _ ftrange _ _ ->
       return $ ILProcDef ftrange id procArgs (fnRange f) newbody numPreds
    _ -> error $ "Expected closure converted proc to have fntype, had " ++ show ft

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
mergeCallNamingBlocks blocks numpreds = go [] blocks
  where go !acc !blocks =
         case blocks of
           [] -> reverse acc
           [b] -> go (b:acc) []
           (x:y:zs) ->
              case mergeAdjacent x y of
                Just  m -> go    acc  (m:zs)
                Nothing -> go (x:acc) (y:zs)
        mergeAdjacent :: (BlockEntry, [Insn O O], Insn O C)
                      -> (BlockEntry, [Insn O O], Insn O C)
                -> Maybe (BlockEntry, [Insn O O], Insn O C)
        mergeAdjacent (xe,xm,xl) ((yb,[yarg]),ym,yl) =
          case xl of
            (ILast (CFCall cb t v vs)) | cb == yb ->
                if Map.lookup yb numpreds == Just 1
                    then Just (xe,xm++[ILetVal (tidIdent yarg) (ILCall t v vs)]++ym,yl)
                    else Nothing
            _ -> Nothing
        mergeAdjacent _ _ = Nothing

--------------------------------------------------------------------

-- As usual, a unique state monad, plus the accumulated procedure definitions.
-- The data type signatures are only needed for pattern match compilation, but
-- we keep them here for convenience.
data ILMState = ILMState {
    ilmUniq          :: Uniq
  , ilmBlockWrappers :: Map BlockId BlockId          -- read-write
  , ilmProcDefs      :: Map Ident ILProcDef          -- read-write
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

ilmNewBlock :: String -> [ILMiddle] -> ILLast -> ILM (BlockId, ILBlock)
ilmNewBlock s mids last = do u <- freshLabel
                             let id = (s, u)
                             return $ (id, Block (id,[]) mids last)

ilmAddWrapper armid id = do old <- get
                            put (old { ilmBlockWrappers = Map.insert armid id
                                      (ilmBlockWrappers old) })

ilmPutProc :: ILM ILProcDef -> ILM ILProcDef
ilmPutProc p_action = do
        p   <- p_action
        old <- get
        let newDefs = Map.insert (ilProcIdent p) p (ilmProcDefs old)
        put (old { ilmProcDefs = newDefs })
        return p

ilmGetProc :: Ident -> ILM (Maybe ILProcDef)
ilmGetProc id = do
        old <- get
        return $ Map.lookup id (ilmProcDefs old)

--------------------------------------------------------------------

instance Structured (String, Label) where
    textOf (str, lab) _width = out $ str ++ "." ++ show lab
    childrenOf _ = []

instance UniqueMonad (State ILMState) where
  freshUnique = ilmNewUniq >>= (return . intToUnique)

showILProgramStructure :: ILProgram -> Output
showILProgramStructure (ILProgram procdefs _decls _dtypes _topfns _lines) =
    concatMap showProcStructure (Map.elems procdefs)
  where
    showProcStructure proc =
        out (show $ ilProcIdent proc) ++ (out " // ")
            ++ (out $ show $ map procVarDesc (ilProcVars proc))
            ++ (out " ==> ") ++ (out $ show $ ilProcReturnType proc)
          ++ out "\n" ++ concatMap showBlock (ilProcBlocks proc)
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

instance TExpr BasicBlockGraph MonoType where
  freeTypedIds bbg =
       let (bvs,fvs) = foldGraphNodes go (bbgBody bbg) (Set.empty, Set.empty) in
       filter (\v -> Set.notMember (tidIdent v) bvs) (Set.toList fvs)
       -- We rely on the fact that these graphs are alpha-converted, and thus
       -- have a unique-binding property. This means we can  get away with just
       -- sticking all the binders in one set, and all the occurrences in
       -- another, and get the right answer back out.
     where insert :: Ord a => Set a -> [a] -> Set a
           insert s ids = Set.union s (Set.fromList ids)
           insertV s vs = Set.union s (Set.fromList $ map tidIdent vs)

           go :: Insn e x -> (Set Ident, Set MoVar) -> (Set Ident, Set MoVar)
           go (ILabel (_,bs))    (bvs,fvs) = (insertV bvs bs, fvs)
           go (ILetVal id lt)    (bvs,fvs) = (Set.insert id bvs, insert fvs $ freeTypedIds lt)
           go (ILetFuns ids fns) (bvs,fvs) = (insert bvs ids, insert fvs (concatMap freeTypedIds fns))
           go (ILast cflast)     (bvs,fvs) = case cflast of
                    CFCont _ vs          -> (bvs, insert fvs vs)
                    CFCall _ _ v vs      -> (bvs, insert fvs (v:vs))
                    CFCase v patbinds    -> (insertV bvs pvs, Set.insert v fvs)
                         where pvs = concatMap (\((_,vs),_) -> vs) patbinds

