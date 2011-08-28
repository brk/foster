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
import Foster.Context
import Foster.TypeIL
import Foster.PatternMatch

-- | Performs closure conversion and lambda lifting.
-- |
-- | The primary differences from CFG to ILG are:
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
                           } deriving Show

data ILBlock = ILBlock BlockId [ILMiddle] ILLast

data ILMiddle =
          ILLetVal      Ident     ILLetable
          -- This is equivalent to MinCaml's make_closure ...
        | ILClosures    [Ident] [ILClosure]
        -- Have an explicit notion of "delayed" renaming in the continuation.
        | ILRebindId    Ident    AIVar
        deriving (Show)

data ILLetable =
           ILBool        Bool
         | ILInt         TypeIL LiteralInt
         | ILTuple       [AIVar]

         | ILCallPrim    TypeIL ILPrim [AIVar]
         | ILCall        TypeIL AIVar  [AIVar]
         | ILAppCtor     TypeIL CtorId [AIVar]
         -- Stack/heap slot allocation
         | ILAllocate    ILAllocInfo
         -- Mutable ref cells
         -- The reason we have both ILAllocate and ILAlloc is that
         -- LLCodegen performs auto-loads from stack slots, which
         -- means that a derived ILAlloc can't return a stack slot value!
         | ILAlloc       AIVar
         | ILDeref       AIVar -- var has type ptr to t
         | ILStore       AIVar AIVar -- a stored in b
         -- Array operations
         | ILAllocArray  TypeIL AIVar
         | ILArrayRead   TypeIL AIVar  AIVar
         | ILArrayPoke          AIVar  AIVar  AIVar
         | ILTyApp       TypeIL AIVar TypeIL
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
            ++ (out "\n") ++ (out $ joinWith "\n\n\t" $ map show
                                                           (ilProcBlocks proc))
          ++ out "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

instance Show ILBlock where
  show (ILBlock id mids last) =
        "ILBlock " ++ show id ++ "\n\t\t"
        ++ (joinWith "\n\t\t" (map show mids))
        ++ "\n\t" ++ show last


data ILMState = ILMState {
    ilmUniq      :: Uniq
  , ilmProcDefs  :: Map Ident ILProcDef
  , ilmCtors     :: DataTypeSigs
  , ilmInfoMap   :: InfoMap
}

type ILM a = State ILMState a

ilmFresh :: String -> ILM Ident
ilmFresh s = do old <- get
                put (old { ilmUniq = (ilmUniq old) + 1 })
                return (Ident s (ilmUniq old))

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


closureConvertAndLift :: DataTypeSigs
                      -> (ModuleIL [CFBlock] TypeIL)
                      -> ILProgram
closureConvertAndLift dataSigs m =
    let fns = moduleILfunctions m in
    let decls = map (\(s,t) -> ILDecl s t) (moduleILdecls m) in
    -- We lambda lift top level functions, since we know they
    -- don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let procsILM     = forM fns (\fn -> lambdaLift fn []) in
    let dataTypes    = moduleILdataTypes m in
    let initialState = ILMState 0 Map.empty dataSigs Map.empty in
    let newstate     = execState procsILM initialState in
    ILProgram (ilmProcDefs newstate) decls dataTypes (moduleILsourceLines m)

-- For example, if we have something like
--      let y = blah in
--      (\x -> x + y) foobar
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \yy x -> x + yy
--      let y = blah in p y foobar
lambdaLift :: Fn [CFBlock] TypeIL -> [AIVar] -> ILM ILProcDef
lambdaLift f freeVars = do
    newbody <- closureConvertBlocks (fnBody f)
    -- Add free variables to the signature of the lambda-lifted procedure.
    let liftedProcVars = freeVars ++ fnVars f
    ilmPutProc (closureConvertedProc liftedProcVars f newbody)

closureConvertedProc :: [AIVar] -> (Fn [CFBlock] TypeIL) -> [ILBlock] -> ILM ILProcDef
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


closureConvertBlocks :: [CFBlock] -> ILM [ILBlock]
closureConvertBlocks blocks = mapM closureConvertBlock blocks

closureConvertBlock :: CFBlock -> ILM ILBlock
closureConvertBlock (CFBlock bid mids last) = do
    newmids <- mapM closureConvertMid mids
    newlast <- ilLast last
    return $ ILBlock bid newmids newlast

closureConvertMid :: CFMiddle -> ILM ILMiddle
closureConvertMid mid =
  case mid of
    CFLetVal id val -> return $ ILLetVal id (ilLetable val)
    CFLetFuns ids fns -> closureConvertLetFuns ids fns

ilLetable expr =
  case expr of
    CFBool        b       -> ILBool        b
    CFInt         t i     -> ILInt         t i
    CFTuple       vs      -> ILTuple       vs
    CFCallPrim    t p vs  -> ILCallPrim    t p vs
    CFCall        t a vs  -> ILCall        t a vs
    CFAppCtor     t c vs  -> ILAppCtor     t c vs
    CFAllocate    info    -> ILAllocate    info
    CFAlloc         a     -> ILAlloc         a
    CFDeref         a     -> ILDeref         a
    CFStore         a b   -> ILStore         a b
    CFAllocArray  t a     -> ILAllocArray  t a
    CFArrayRead   t a b   -> ILArrayRead   t a b
    CFArrayPoke   a b c   -> ILArrayPoke   a b c
    CFTyApp       t a p   -> ILTyApp       t a p

ilLast last =
  case last of
     CFRetVoid          -> return $ ILRetVoid
     CFRet   v          -> return $ ILRet   v
     CFBr    b          -> return $ ILBr    b
     CFIf    t a b1 b2  -> return $ ILIf    t a b1 b2
     CFCase  t a pbs    -> do allSigs <- gets ilmCtors
                              let dt = compilePatterns pbs allSigs
                              return $ ILCase  t a pbs dt

closureConvertLetFuns ids fns = do
    cloEnvIds <- mapM (\id -> ilmFresh (".env." ++ identPrefix id)) ids
    let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
    let idfns = zip ids fns
    combined  <- mapM (closureOfKnFn infoMap) idfns
    let (closures, _procdefs) = unzip combined
    return $ ILClosures ids closures

fakeCloVar id = TypedId fakeCloEnvType id where fakeCloEnvType = TupleTypeIL []

type InfoMap = Map Ident ((Fn [CFBlock] TypeIL), Ident)

closedOverVarsOfKnFn :: InfoMap -> Ident -> Fn [CFBlock] TypeIL -> [AIVar]
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
              -> (Ident, (Fn [CFBlock] TypeIL))
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

    firstBlockId [] = error $ "can't get first block id from empty list!"
    firstBlockId (CFBlock bid _ _:_) = bid

    closureConvertFn :: Fn [CFBlock] TypeIL
                     -> InfoMap -> [AIVar] -> ILM (Ident, ILProcDef)
    closureConvertFn f info varsOfClosure = do
        let envId  = snd (info Map.! self_id)
        let envVar = TypedId (TupleTypeIL $ map tidType varsOfClosure) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- let oldbody = fnBody f in
                   let norange = MissingSourceRange "" in
                   let patVar a = P_Variable norange (tidIdent a) in
                   do
                     bid <- ilmFresh "caseof"
                     let bodyid = firstBlockId oldbody
                     let cfcase = CFCase (fnRetType f) envVar [
                                    (P_Tuple norange (map patVar varsOfClosure)
                                    , bodyid) ]
                     let caseblock = CFBlock bid [] cfcase
                     closureConvertBlocks $ caseblock:oldbody

        proc <- ilmPutProc (closureConvertedProc (envVar:(fnVars f)) f newbody)
        return (envId, proc)

    makeEnvPassingExplicitFn fn =
       fn { fnBody = map makeEnvPassingExplicitBlock (fnBody fn) }

    makeEnvPassingExplicitBlock (CFBlock bid mids last) =
       let newmids = map makeEnvPassingExplicitMid mids in
       CFBlock bid newmids last

    makeEnvPassingExplicitMid :: CFMiddle -> CFMiddle
    makeEnvPassingExplicitMid mid =
      case mid of
        CFLetVal id val -> CFLetVal id (makeEnvPassingExplicitVal val)
        CFLetFuns ids fns -> CFLetFuns ids (map makeEnvPassingExplicitFn fns)

    makeEnvPassingExplicitVal :: CFLetable -> CFLetable
    makeEnvPassingExplicitVal expr =
      case expr of
        CFCall t v vs ->
          case Map.lookup (tidIdent v) infoMap of
            Nothing -> expr
            -- The only really interesting case: call to let-bound function!
            Just (f, envid) ->
              let env = fakeCloVar envid in
              CFCall t (fnVar f) (env:vs)  -- Call proc, passing env as first parameter.
              -- We don't know the env type here, since we don't
              -- pre-collect the set of closed-over envs from other procs.
              -- This works because (A) we never type check ILExprs,
              -- and (B) the LLVM codegen doesn't check the type field in this case.
        _ -> expr

class TypedIL a where
  typeIL :: a -> TypeIL

instance TypedIL ILLetable where
    typeIL (ILBool _)          = boolTypeIL
    typeIL (ILInt t _)         = t
    typeIL (ILTuple vs)        = TupleTypeIL (map tidType vs)
    typeIL (ILCall t id expr)  = t
    typeIL (ILCallPrim t id vs)= t
    typeIL (ILAppCtor t cid vs)= t
    typeIL (ILAllocate info)   = ilAllocType info
    typeIL (ILAllocArray elt_ty _) = ArrayTypeIL elt_ty
    typeIL (ILAlloc v)         = PtrTypeIL (tidType v)
    typeIL (ILDeref v)         = pointedToTypeOfVar v
    typeIL (ILStore _ _)       = TupleTypeIL []
    typeIL (ILArrayRead t _ _) = t
    typeIL (ILArrayPoke _ _ _) = TupleTypeIL []
    typeIL (ILTyApp overallType tm tyArgs) = overallType

patternBindings :: (Pattern, TypeIL) -> [ContextBinding TypeIL]
patternBindings (p, ty) =
  case p of
    P_Bool     rng _ -> []
    P_Int      rng _ -> []
    P_Wildcard rng   -> []
    P_Variable rng id -> [TermVarBinding (identPrefix id) $
                                           TypedId ty id]
    P_Ctor     rng pats _ ->
      error $ "ILExpr.patternBindings not yet implemented for " ++ show (p, ty)
    P_Tuple    rng pats ->
      case ty of
        TupleTypeIL tys -> concatMap patternBindings (zip pats tys)
        otherwise -> (error $ "patternBindings failed on typechecked pattern!"
                                ++ "\np = " ++ show p ++ " ; ty = " ++ show ty)
