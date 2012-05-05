{-# LANGUAGE GADTs, TypeSynonymInstances #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Control.Monad.State
import Data.Set(Set)
import qualified Data.Set as Set(empty, singleton, union, unions, notMember)
import Data.Map(Map)
import qualified Data.Map as Map((!), insert, lookup, empty, fromList, elems)
import qualified Data.Text as T

import Compiler.Hoopl

import Foster.Base
import Foster.Kind
import Foster.CFG
import Foster.TypeIL
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
data ILClosure = ILClosure { ilClosureProcIdent :: Ident
                           , ilClosureEnvIdent  :: Ident
                           , ilClosureCaptures  :: [AIVar] } deriving Show

-- A program consists of top-level data types and mutually-recursive procedures.
data ILProgram = ILProgram (Map Ident ILProcDef)
                           [ILExternDecl]
                           [DataType TypeIL]
                           SourceLines

data ILExternDecl = ILDecl String TypeIL deriving (Show)

-- Procedures can be polymorphic when an ILProgram is first created,
-- but after monomorphization, all the polymorphism should be gone.
data ILProcDef =
     ILProcDef { ilProcReturnType :: TypeIL
               , ilProcPolyTyVars :: Maybe [(TyVar, Kind)]
               , ilProcIdent      :: Ident
               , ilProcVars       :: [AIVar]
               , ilProcRange      :: SourceRange
               , ilProcBlocks     :: [ILBlock]
               , ilProcBlockPreds :: Map BlockId Int
               }

-- The standard definition of a basic block and its parts.
data ILBlock  = Block BlockEntry [ILMiddle] ILLast
data ILMiddle = ILLetVal      Ident    Letable
              -- This is equivalent to MinCaml's make_closure ...
              | ILClosures    [Ident] [ILClosure]
              -- Have an explicit notion of "delayed" renaming in the
              -- continuation. This is 1 line in LLCodegen.cpp instead of
              -- many lines to do substitutions on CFGs.
              | ILRebindId    Ident    AIVar
              deriving Show

-- The only difference from CFLast to ILLast is the decision tree in ILCase.
data ILLast = ILRetVoid
            | ILRet      AIVar
            | ILBr       BlockId [AIVar]
            | ILCase     AIVar [(CtorId, BlockId)] (Maybe BlockId) Occurrence
--------------------------------------------------------------------

closureConvertAndLift :: DataTypeSigs -> Uniq
                      -> (ModuleIL BasicBlockGraph TypeIL)
                      -> ILProgram
closureConvertAndLift dataSigs u m =
    -- We lambda lift top level functions, since we know a priori
    -- that they don't have any "real" free vars.
    -- Lambda lifting then closure converts any nested functions.
    let procsILM     = forM fns (\fn -> lambdaLift fn []) where
                            fns = moduleILfunctions m in
    let initialState = ILMState u Map.empty Map.empty dataSigs in
    let newstate     = execState procsILM initialState in
    let decls = map (\(s,t) -> ILDecl s t) (moduleILdecls m) in
    let dts = moduleILprimTypes m ++ moduleILdataTypes m in
    ILProgram (ilmProcDefs newstate) decls dts (moduleILsourceLines m)

-- For example, if we have something like
--      let y = blah in
--      (\x -> x + y) foobar
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \yy x -> x + yy
--      let y = blah in p y foobar
lambdaLift :: CFFn -> [AIVar] -> ILM ILProcDef
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

jumpTo bbg = case bbgEntry bbg of (bid, _) -> ILast $ CFBr bid undefined

type ClosureConvertedBlocks = ([ILBlock], Map BlockId Int)

-- We serialize a basic block graph by computing a depth-first search
-- starting from the graph's entry block.
closureConvertBlocks :: BasicBlockGraph -> ILM ClosureConvertedBlocks
closureConvertBlocks bbg = do
   let cfgBlocks = map basicBlock $
                     preorder_dfs $ mkLast (jumpTo bbg) |*><*| bbgBody bbg
   blocks <- mapM closureConvertBlock cfgBlocks
   return (concat blocks, bbgNumPreds bbg)
  where
    -- A BasicBlock which ends in a decision tree will, in the general case,
    -- expand out to multiple blocks to encode the tree.
    closureConvertBlock :: BasicBlock -> ILM [ILBlock]
    closureConvertBlock bb = do
        let (bid, mids, last) = splitBasicBlock bb
        newmids <- mapM closureConvertMid mids
        (blocks, newlast) <- ilLast last
        return $ Block bid (newmids) newlast : blocks
     where
      ilLast :: Insn O C -> ILM ([ILBlock], ILLast)
      ilLast (ILast last) =
        let ret i = return ([], i) in
        case last of
           CFRetVoid       -> ret $ ILRetVoid
           CFRet   v       -> ret $ ILRet   v
           CFBr    b args  -> ret $ ILBr    b args
           CFCase  a pbs   -> do allSigs <- gets ilmCtors
                                 let dt = compilePatterns pbs allSigs
                                 let usedBlocks = eltsOfDecisionTree dt
                                 let _unusedPats = [pat | (pat, bid) <- pbs
                                                  , Set.notMember bid usedBlocks]
                                 -- TODO print warning if any unused patterns
                                 (BlockFin blocks id) <- compileDecisionTree a dt
                                 return $ (blocks, ILBr id [])
              where
                -- The decision tree we get from pattern-match compilation may
                -- contain only a subset of the pattern branche.
                eltsOfDecisionTree :: (Show a, Ord a) => DecisionTree a -> Set a
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
          ILetFuns ids fns -> closureConvertLetFuns ids fns

      closureConvertLetFuns :: [Ident] -> [CFFn] -> ILM ILMiddle
      closureConvertLetFuns ids fns = do
          let genFreshId id = ilmFresh (".env." `prependedTo` identPrefix id)
          cloEnvIds <- mapM genFreshId ids
          let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
          let idfns = zip ids fns
          closures  <- mapM (closureOfKnFn infoMap) idfns
          return $ ILClosures ids closures

data BlockFin = BlockFin [ILBlock]      -- new blocks generated
                         BlockId        -- entry block for decision tree logic

bogusVar (id, _) = TypedId (PrimIntIL I1) id

compileDecisionTree :: AIVar -> DecisionTree BlockId -> ILM BlockFin
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
                           (ILCase scrutinee (zip ctors ids) maybeDefaultId occ)
        return $ BlockFin (block : concat blockss ++ dblockss) id

emitOccurrence :: AIVar -> (Ident, Occurrence) -> ILMiddle
emitOccurrence scrutinee (id, occ) = ILLetVal id (ILOccurrence scrutinee occ)

type InfoMap = Map Ident (CFFn, Ident) -- fn ident => (fn, env id)

closureOfKnFn :: InfoMap
              -> (Ident, CFFn)
              -> ILM ILClosure
closureOfKnFn infoMap (self_id, fn) = do
    let varsOfClosure = closedOverVarsOfKnFn
    let transformedFn = makeEnvPassingExplicitFn fn
    (envVar, newproc) <- closureConvertFn transformedFn varsOfClosure
    return $ ILClosure (ilProcIdent newproc) envVar varsOfClosure
  where
    -- Each closure converted proc need not capture its own environment
    -- variable, because it will be added as an implicit parameter, but
    -- the environments for others in the same rec SCC *are* closed over.
    closedOverVarsOfKnFn :: [AIVar]
    closedOverVarsOfKnFn =
        let nonGlobalVars = [tid | tid@(TypedId _ id@(Ident _ _)) <- fnFreeVars fn
                            , id /= self_id] in
        -- Capture env. vars instead of closure vars.
        map (\v -> case Map.lookup (tidIdent v) infoMap of
                                   Nothing ->         v
                                   Just (_, envid) -> fakeCloVar envid)
             nonGlobalVars

    fakeCloVar id = TypedId fakeCloEnvType id
                      where fakeCloEnvType = TupleTypeIL []

    -- This is where the magic happens: given a function and its free variables,
    -- we create a procedure which also takes an extra (strongly-typed) env ptr
    -- argument. The new body does case analysis to bind the free variable names
    -- to the contents of the slots of the environment.
    closureConvertFn :: CFFn -> [AIVar] -> ILM (Ident, ILProcDef)
    closureConvertFn f varsOfClosure = do
        let envId  = snd (infoMap Map.! self_id)
        -- Note that this env var has a precise type! The other's is missing.
        let envVar = TypedId (TupleTypeIL $ map tidType varsOfClosure) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- do
            let BasicBlockGraph bodyentry oldbodygraph numPreds = fnBody f
            let norange = MissingSourceRange ""
            let patVar a = P_Variable norange a
            let cfcase = CFCase envVar [
                           ((P_Tuple norange (map patVar varsOfClosure),
                                                         varsOfClosure)
                           , fst bodyentry) ]
            -- We change the entry block of the new body (versus the old).
            lab <- freshLabel
            let bid = (("caseof", lab), [])
            let caseblock = mkFirst (ILabel bid) <*>
                            mkMiddles []         <*>
                            mkLast (ILast cfcase)
            closureConvertBlocks $
               BasicBlockGraph bid (caseblock |*><*| oldbodygraph)
                               (incrPredecessorsDueTo (ILast cfcase) numPreds)

        proc <- ilmPutProc $ closureConvertedProc (envVar:(fnVars f)) f newbody
        return (envId, proc)

    mapBasicBlock f (BasicBlockGraph entry bg np) = BasicBlockGraph entry (f bg) np

    -- Making environment passing explicit simply means rewriting calls
    -- of closure variables from   v(args...)   ==>   v_proc(v_env, args...).
    makeEnvPassingExplicitFn fn =
      let mapBlock g = graphMapBlocks (blockMapNodes3 (id, mid, id)) g in
      fn { fnBody = mapBasicBlock mapBlock (fnBody fn) }
        where
              mid :: Insn O O -> Insn O O
              mid m = case m of
                ILetVal id val -> ILetVal id (makeEnvPassingExplicitVal val)
                ILetFuns ids fns -> ILetFuns ids
                                         (map makeEnvPassingExplicitFn fns)

    makeEnvPassingExplicitVal :: Letable -> Letable
    makeEnvPassingExplicitVal expr =
      case expr of
        ILCall t v vs ->
          case Map.lookup (tidIdent v) infoMap of
            Nothing -> expr
            -- The only really interesting case: call to let-bound function!
            Just (f, envid) ->
              let env = fakeCloVar envid in
              ILCall t (fnVar f) (env:vs) -- Call proc with env as first arg.
              -- We don't know the env type here, since we don't
              -- pre-collect the set of closed-over envs from other procs.
              -- This works because (A) we never type check ILExprs, and
              -- (B) the LLVM codegen doesn't check the type field in this case.
        _ -> expr

--------------------------------------------------------------------

closureConvertedProc :: [AIVar]
                     -> CFFn
                     -> ClosureConvertedBlocks
                     -> ILM ILProcDef
closureConvertedProc procArgs f (newbody, numPreds) = do
  let (TypedId ft id) = fnVar f
  case ft of
    FnTypeIL                  _ftd ftrange _ _ ->
       return $ ILProcDef ftrange Nothing        id procArgs (fnRange f) newbody numPreds
    ForAllIL ktyvars (FnTypeIL _ftd ftrange _ _) ->
       return $ ILProcDef ftrange (Just ktyvars) id procArgs (fnRange f) newbody numPreds
    _ -> error $ "Expected closure converted proc to have fntype, had " ++ show ft

--------------------------------------------------------------------

-- As usual, a unique state monad, plus the accumulated procedure definitions.
-- The data type signatures are only needed for pattern match compilation, but
-- we keep them here for convenience.
data ILMState = ILMState {
    ilmUniq          :: Uniq
  , ilmBlockWrappers :: Map BlockId BlockId -- read-write
  , ilmProcDefs      :: Map Ident ILProcDef -- read-write
  , ilmCtors         :: DataTypeSigs        -- read-only per-program
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

showProgramStructure :: ILProgram -> Output
showProgramStructure (ILProgram procdefs _decls _dtypes _lines) =
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
