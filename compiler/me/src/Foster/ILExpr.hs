{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Debug.Trace(trace)
import Control.Monad.State
import Data.Map(Map)
import qualified Data.Map as Map((!), insert, lookup, empty, fromList, elems)

import Foster.Base
import Foster.CFG
import Foster.TypeIL
import Foster.Letable
import Foster.PatternMatch

import Data.Functor.Identity
import Compiler.Hoopl

-- | Performs closure conversion and lambda lifting, and also
-- | transforms back from Hoopl's CFG representation to lists-of-blocks.
-- |
-- | The primary differences in the general structure are:
-- |  #. LetFuns replaced with Closures
-- |  #. Module  replaced with ILProgram
-- |  #. Fn replaced with ProcDef

data ILClosure = ILClosure { ilClosureProcIdent :: Ident
                           , ilClosureEnvIdent  :: Ident
                           , ilClosureCaptures  :: [AIVar] } deriving Show

data ILProgram = ILProgram (Map Ident ILProcDef)
                           [ILDecl]
                           [DataType TypeIL]
                           SourceLines

data ILDecl    = ILDecl String TypeIL deriving (Show)

data ILProcDef = ILProcDef { ilProcReturnType :: TypeIL
                           , ilProcPolyTyVars :: (Maybe [TyVar])
                           , ilProcIdent      :: Ident
                           , ilProcVars       :: [AIVar]
                           , ilProcRange      :: SourceRange
                           , ilProcCallConv   :: CallConv
                           , ilProcBlocks     :: [ILBlock]
                           }

data ILBlock = Block BlockId [ILMiddle] ILLast

data ILMiddle =
          ILLetVal      Ident    Letable
          -- This is equivalent to MinCaml's make_closure ...
        | ILClosures    [Ident] [ILClosure]
        -- Have an explicit notion of "delayed" renaming in the continuation.
        | ILRebindId    Ident    AIVar
        deriving (Show)

data ILLast =
          ILRetVoid
        | ILRet         AIVar
        | ILBr          BlockId
        | ILIf          TypeIL AIVar  BlockId   BlockId
        | ILCase        TypeIL AIVar [(Pattern, BlockId)] (DecisionTree BlockId)
        deriving (Show)


showProgramStructure :: ILProgram -> Output
showProgramStructure (ILProgram procdefs decls _dtypes _lines) =
    concatMap showProcStructure (Map.elems procdefs)
  where
    showProcStructure proc =
        out (show $ ilProcIdent proc) ++ (out " // ")
            ++ (out $ show $ map procVarDesc (ilProcVars proc))
            ++ (out " @@@ ") ++ (out $ show $ ilProcCallConv proc)
            ++ (out " ==> ") ++ (out $ show $ ilProcReturnType proc)
           -- ++ (out "\n") ++ (out $ joinWith "\n\n\t" $ map show
           --                                                (ilProcBlocks proc))
          ++ out "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

data ILMState = ILMState {
    ilmUniq      :: Uniq
  , ilmProcDefs  :: Map Ident ILProcDef
  , ilmCtors     :: DataTypeSigs
  , ilmInfoMap   :: InfoMap
}

type ILM a = State ILMState a

ilmNewUniq = do old <- get
                put (old { ilmUniq = (ilmUniq old) + 1 })
                return (ilmUniq old)

ilmFresh :: String -> ILM Ident
ilmFresh s = do u <- ilmNewUniq ; return (Ident s u)

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


closureConvertAndLift :: DataTypeSigs -> Uniq
                      -> (ModuleIL BasicBlockGraph TypeIL)
                      -> ILProgram
closureConvertAndLift dataSigs u m =
    let fns = moduleILfunctions m in
    let decls = map (\(s,t) -> ILDecl s t) (moduleILdecls m) in
    -- We lambda lift top level functions, since we know they
    -- don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let procsILM     = forM fns (\fn -> lambdaLift fn []) in
    let dataTypes    = moduleILdataTypes m in
    let initialState = ILMState u Map.empty dataSigs Map.empty in
    let newstate     = execState procsILM initialState in
    ILProgram (ilmProcDefs newstate) decls dataTypes (moduleILsourceLines m)

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
    -- Add free variables to the signature of the lambda-lifted procedure.
    let liftedProcVars = freeVars ++ fnVars f
    ilmPutProc (closureConvertedProc liftedProcVars f newbody)

closureConvertedProc :: [AIVar]
                     -> CFFn
                     -> [ILBlock]
                     -> ILM ILProcDef
closureConvertedProc liftedProcVars f newbody = do
    let (TypedId ft id) = fnVar f
    case ft of
        FnTypeIL ftd ftrange _ _ ->
            return $ ILProcDef ftrange Nothing       id liftedProcVars
                      (fnRange f) FastCC newbody
        ForAllIL tyvars (FnTypeIL ftd ftrange _ _) ->
            return $ ILProcDef ftrange (Just tyvars) id liftedProcVars
                      (fnRange f) FastCC newbody
        _ -> error $ "Expected closure converted proc to have fntype, had " ++ show ft

closureConvertBlocks :: BasicBlockGraph -> ILM [ILBlock]
closureConvertBlocks bbg =
  let blockGraphs = map blockGraph $
                      preorder_dfs $ mkLast (ILast (CFBr $ bbgEntry bbg))
                                      |*><*| bbgBody bbg in
  mapM closureConvertBlock blockGraphs

closureConvertBlock :: BasicBlock -> ILM ILBlock
closureConvertBlock bb = do
    let (bid, mids, last) = splitBasicBlock bb
    newmids <- mapM closureConvertMid mids
    newlast <- ilLast last
    return $ Block bid newmids newlast

closureConvertMid :: Insn O O -> ILM ILMiddle
closureConvertMid mid =
  case mid of
    ILetVal id val -> return $ ILLetVal id val
    ILetFuns ids fns -> closureConvertLetFuns ids fns

ilLast :: Insn O C -> ILM ILLast
ilLast (ILast last) =
  case last of
     CFRetVoid          -> return $ ILRetVoid
     CFRet   v          -> return $ ILRet   v
     CFBr    b          -> return $ ILBr    b
     CFIf    t a b1 b2  -> return $ ILIf    t a b1 b2
     CFCase  t a pbs    -> do allSigs <- gets ilmCtors
                              let dt = compilePatterns pbs allSigs
                              return $ ILCase  t a pbs dt

closureConvertLetFuns :: [Ident] -> [CFFn] -> ILM ILMiddle
closureConvertLetFuns ids fns = do
    cloEnvIds <- mapM (\id -> ilmFresh (".env." ++ identPrefix id)) ids
    let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
    let idfns = zip ids fns
    combined  <- mapM (closureOfKnFn infoMap) idfns
    let (closures, _procdefs) = unzip combined
    return $ ILClosures ids closures

fakeCloVar id = TypedId fakeCloEnvType id where fakeCloEnvType = TupleTypeIL []

type InfoMap = Map Ident (CFFn, Ident)

closedOverVarsOfKnFn :: InfoMap -> Ident -> CFFn -> [AIVar]
closedOverVarsOfKnFn infoMap self_id fn =
    -- Each closure converted proc need not capture its own environment
    -- variable, because it will be added as an implicit parameter, but
    -- the environment for f *is* closed over in g.
    let rawFreeIds = (map tidIdent $ fnFreeVars fn) `butnot` [self_id] in

    -- Capture env. vars instead of closure vars.
    let envVars = concatMap (\n -> case Map.lookup n infoMap of
                               Nothing ->  []
                               Just (_, envid) -> [fakeCloVar envid])
                            rawFreeIds in
    envVars ++ fnFreeVars fn

closureOfKnFn :: InfoMap
              -> (Ident, CFFn)
              -> ILM (ILClosure, ILProcDef)
closureOfKnFn infoMap (self_id, fn) = do
    let varsOfClosure = closedOverVarsOfKnFn infoMap self_id fn
    let transformedFn = makeEnvPassingExplicitFn fn
    (envVar, newproc) <- closureConvertFn transformedFn infoMap varsOfClosure
    return $ trace ("varsOfClosure for " ++ show (tidIdent $ fnVar fn) ++  ":"
                              ++ (show $ varsOfClosure)) $
             (ILClosure (ilProcIdent newproc) envVar varsOfClosure, newproc)
  where
    fnRetType f = tidType $ fnVar f

    closureConvertFn :: CFFn -> InfoMap -> [AIVar] -> ILM (Ident, ILProcDef)
    closureConvertFn f info varsOfClosure = do
        let envId  = snd (info Map.! self_id)
        let envVar = TypedId (TupleTypeIL $ map tidType varsOfClosure) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- do
            let BasicBlockGraph bodyid oldbodygraph = fnBody f
            let norange = MissingSourceRange ""
            let patVar a = P_Variable norange (tidIdent a)
            let cfcase = CFCase (fnRetType f) envVar [
                           (P_Tuple norange (map patVar varsOfClosure)
                           , bodyid) ]
            -- We change the entry block of the new body (versus the old).
            lab <- freshLabel
            let bid = ("caseof", lab)
            let caseblock = mkFirst (ILabel bid) <*>
                            mkMiddles []         <*>
                            mkLast (ILast cfcase)
            closureConvertBlocks $
               BasicBlockGraph bid (caseblock |*><*| oldbodygraph)

        proc <- ilmPutProc (closureConvertedProc (envVar:(fnVars f)) f newbody)
        return (envId, proc)

    mapBasicBlock f (BasicBlockGraph entry bg) = BasicBlockGraph entry (f bg)

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
        CFCall t v vs ->
          case Map.lookup (tidIdent v) infoMap of
            Nothing -> expr
            -- The only really interesting case: call to let-bound function!
            Just (f, envid) ->
              let env = fakeCloVar envid in
              CFCall t (fnVar f) (env:vs) -- Call proc with env as first arg.
              -- We don't know the env type here, since we don't
              -- pre-collect the set of closed-over envs from other procs.
              -- This works because (A) we never type check ILExprs,
              -- and (B) the LLVM codegen doesn't check the type field in this case.
        _ -> expr


instance UniqueMonad (StateT ILMState Identity) where
  freshUnique = ilmNewUniq >>= (return . intToUnique)
