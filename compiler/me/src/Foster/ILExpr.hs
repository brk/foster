-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Debug.Trace(trace)
import Control.Monad.State
import Data.Set(Set)
import Data.Set as Set(empty)
import Data.Map(Map)
import qualified Data.Map as Map((!), insert, lookup, empty, elems, fromList)

import Foster.Base
import Foster.Context
import Foster.TypeIL
import Foster.KNExpr
import Foster.PatternMatch

-- | Performs closure conversion and lambda lifting.
-- |
-- | The primary differences from KNExpr to ILExpr are:
-- |  #. Pattern match compilation for case expressions.
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
                           , ilProcBody       :: ILExpr
                           } deriving Show

data AllocMemRegion = MemRegionStack
                    | MemRegionGlobalHeap
data ILAllocInfo = ILAllocInfo AllocMemRegion (Maybe AIVar)

data ILExpr =
        -- Literals
          ILBool        Bool
        | ILInt         TypeIL LiteralInt
        | ILTuple       [AIVar]
        -- Control flow
        | ILIf          TypeIL AIVar  ILExpr ILExpr
        | ILUntil       TypeIL ILExpr ILExpr
        -- Creation of bindings
        | ILCase        TypeIL AIVar [(Pattern, ILExpr)] (DecisionTree ILExpr)
        | ILLetVal       Ident    ILExpr    ILExpr
        -- This is equivalent to MinCaml's make_closure ... in M.
        | ILClosures    [Ident] [ILClosure] ILExpr
        -- Use of bindings
        | ILVar         AIVar
        | ILCallPrim    TypeIL ILPrim [AIVar]
        | ILCall        TypeIL AIVar  [AIVar]
        | ILAppCtor     TypeIL CtorId [AIVar] -- ILDataCtor
        -- Mutable ref cells
        | ILAlloc              AIVar
        | ILDeref       TypeIL AIVar
        | ILStore       TypeIL AIVar AIVar
        -- Array operations
        | ILAllocArray  TypeIL AIVar
        | ILArrayRead   TypeIL AIVar AIVar
        | ILArrayPoke          AIVar AIVar AIVar
        | ILTyApp       TypeIL AIVar TypeIL
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
            ++ (out "\n") ++  showStructure (ilProcBody proc)
          ++ out "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

data ILMState = ILMState {
    ilmUniq      :: Uniq
  , ilmProcDefs  :: Map Ident ILProcDef
  , ilmKnownPoly :: Set Ident
  , ilmCtors     :: DataTypeSigs
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

fakeCloVar id = TypedId fakeCloEnvType id where fakeCloEnvType = TupleTypeIL []

closureConvertAndLift :: DataTypeSigs
                      -> (ModuleIL KNExpr TypeIL)
                      -> ILProgram
closureConvertAndLift dataSigs m =
    let fns = moduleILfunctions m in
    let decls = map (\(s,t) -> ILDecl s t) (moduleILdecls m) in
    -- We lambda lift top level functions, since we know they don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let procsILM     = forM fns (\fn -> lambdaLift fn []) in
    let dataTypes    = moduleILdataTypes m in
    let initialState = ILMState 0 Map.empty Set.empty dataSigs in
    let newstate     = execState procsILM initialState in
    ILProgram (ilmProcDefs newstate) decls dataTypes (moduleILsourceLines m)

-- Note that closure conversion is combined with the transformation from
-- AnnExpr to ILExpr, which mainly consists of making evaluation order for
-- the subexpressions of tuples and calls (etc) explicit.
closureConvert :: KNExpr -> ILM ILExpr
closureConvert expr =
        let g = closureConvert in
        case expr of
            -- These cases just swap the tag only. Boring!
            KNBool       b      -> return $ ILBool       b
            KNInt        t i    -> return $ ILInt        t i
            KNVar        v      -> return $ ILVar        v
            KNAllocArray t v    -> return $ ILAllocArray t v
            KNAlloc      v      -> return $ ILAlloc      v
            KNDeref      t v    -> return $ ILDeref      t v
            KNStore      t a b  -> return $ ILStore      t a b
            KNArrayRead  t a b  -> return $ ILArrayRead  t a b
            KNArrayPoke  a b c  -> return $ ILArrayPoke  a b c
            KNTuple      vs     -> return $ ILTuple      vs
            KNCallPrim   t p vs -> return $ ILCallPrim   t p vs
            KNAppCtor    t c vs -> return $ ILAppCtor    t c vs
            KNCall       t b vs -> return $ ILCall       t b vs
            KNTyApp t v argty   -> return $ ILTyApp t v argty

            -- These cases swap the tag and recur in uninteresting ways.
            KNIf t v a b    -> do [a', b'] <- mapM g [a, b] ; return $ ILIf t v a' b'
            KNUntil t a b   -> do [a', b'] <- mapM g [a, b] ; return $ ILUntil t a' b'
            KNLetVal id a b -> do [a', b'] <- mapM g [a, b] ; return $ ILLetVal id a' b'

            -- Pattern matching generalizes variable binding: Each branch
            -- expression must be converted in a suitably extended context,
            -- and while we're here, we also perform pattern match compilation.
            KNCase t v bs -> do
                -- convertBranch :: (Pattern, KNExpr) -> (Pattern, ILExpr)
                let convertBranch (p, a) = do a' <- g a ; return (p, a' )
                ibs <- mapM convertBranch bs
                allSigs <- gets ilmCtors
                let dt = compilePatterns ibs allSigs
                return $ ILCase t v ibs dt

            KNLetFuns ids fns e -> closureConvertLetFuns ids fns e

closureConvertLetFuns ids fns e = do
    cloEnvIds <- mapM (\id -> ilmFresh (".env." ++ identPrefix id)) ids
    let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
    let idfns = zip ids fns
    combined  <- mapM (closureOfKnFn infoMap) idfns
    let (closures, _procdefs) = unzip combined
    e' <- closureConvert e
    return $ ILClosures ids closures e'

closureConvertedProc :: [AIVar] -> (Fn KNExpr TypeIL) -> ILExpr -> ILM ILProcDef
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

-- For example, if we have something like
--      let y = blah in
--      (\x -> x + y) foobar
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \yy x -> x + yy
--      let y = blah in p y foobar
lambdaLift :: Fn KNExpr TypeIL -> [AIVar] -> ILM ILProcDef
lambdaLift f freeVars = do
    newbody <- closureConvert (fnBody f)
    -- Add free variables to the signature of the lambda-lifted procedure.
    let liftedProcVars = freeVars ++ fnVars f
    ilmPutProc (closureConvertedProc liftedProcVars f newbody)

bindingsForVars vars = [TermVarBinding (identPrefix i) v
                       | v@(TypedId t i) <- vars]

type FreeName = Ident
type InfoMap = Map Ident ((Fn KNExpr TypeIL), Ident)

closedOverVarsOfKnFn :: InfoMap -> Ident -> Fn KNExpr TypeIL -> [AIVar]
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
              -> (Ident, (Fn KNExpr TypeIL))
              -> ILM (ILClosure, ILProcDef)
closureOfKnFn infoMap (self_id, fn) = do
    let varsOfClosure = closedOverVarsOfKnFn infoMap self_id fn
    let transformedFn = makeEnvPassingExplicitFn fn
    (envVar, newproc) <- closureConvertFn transformedFn infoMap varsOfClosure
    return $ trace ("varsOfClosure for " ++ show (tidIdent $ fnVar fn) ++  ":"
                              ++ (show $ varsOfClosure)) $
             (ILClosure (ilProcIdent newproc) envVar varsOfClosure, newproc)
  where

    closureConvertFn :: Fn KNExpr TypeIL
                     -> InfoMap -> [AIVar] -> ILM (Ident, ILProcDef)
    closureConvertFn f info varsOfClosure = do
        let envId  = snd (info Map.! self_id)
        let envVar = TypedId (TupleTypeIL $ map tidType varsOfClosure) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- let oldbody = fnBody f in
                   let norange = MissingSourceRange "" in
                   let patVar a = P_Variable norange (tidIdent a) in
                   closureConvert $
                     KNCase (typeKN oldbody) envVar
                        [ (P_Tuple norange (map patVar varsOfClosure)
                          , oldbody) ]
        proc <- ilmPutProc (closureConvertedProc (envVar:(fnVars f)) f newbody)
        return (envId, proc)

    makeEnvPassingExplicitFn fn =
       fn { fnBody = makeEnvPassingExplicit (fnBody fn) }

    makeEnvPassingExplicit :: KNExpr -> KNExpr
    makeEnvPassingExplicit expr =
      q expr where
      fq = makeEnvPassingExplicitFn
      q e = case e of
        KNVar        {} -> e
        KNBool       {} -> e
        KNInt        {} -> e
        KNAllocArray {} -> e
        KNAlloc      {} -> e
        KNDeref      {} -> e
        KNStore      {} -> e
        KNArrayRead  {} -> e
        KNArrayPoke  {} -> e
        KNTuple      {} -> e
        KNCallPrim   {} -> e
        KNAppCtor    {} -> e
        KNTyApp      {} -> e

        KNIf      t  v b c  -> KNIf      t v (q b) (q c)
        KNUntil   t  a b    -> KNUntil   t   (q a) (q b)
        KNLetVal  id a b    -> KNLetVal  id  (q a) (q b)
        KNLetFuns ids fns e -> KNLetFuns ids (map fq fns) (q e)
        KNCase    t v bs    -> KNCase    t v [(p, q e) | (p, e) <- bs]

        KNCall t v vs ->
          case Map.lookup (tidIdent v) infoMap of
            Nothing -> e
            -- The only really interesting case: call to let-bound function!
            Just (f, envid) ->
              let env = fakeCloVar envid in
              KNCall t (fnVar f) (env:vs)  -- Call proc, passing env as first parameter.
              -- We don't know the env type here, since we don't
              -- pre-collect the set of closed-over envs from other procs.
              -- This works because (A) we never type check ILExprs,
              -- and (B) the LLVM codegen doesn't check the type field in this case.

typeIL :: ILExpr -> TypeIL
typeIL (ILBool _)          = boolTypeIL
typeIL (ILInt t _)         = t
typeIL (ILTuple vs)        = TupleTypeIL (map tidType vs)
typeIL (ILClosures n b e)  = typeIL e
typeIL (ILLetVal x b e)    = typeIL e
typeIL (ILCall t id expr)  = t
typeIL (ILCallPrim t id vs)= t
typeIL (ILAppCtor t cid vs)= t
typeIL (ILAllocArray elt_ty _) = ArrayTypeIL elt_ty
typeIL (ILIf t a b c)      = t
typeIL (ILUntil t a b)     = t
typeIL (ILAlloc v)         = PtrTypeIL (tidType v)
typeIL (ILDeref t _)       = t
typeIL (ILStore t _ _)     = t
typeIL (ILArrayRead t _ _) = t
typeIL (ILArrayPoke _ _ _) = TupleTypeIL []
typeIL (ILCase t _ _ _)    = t
typeIL (ILVar v)           = tidType v
typeIL (ILTyApp overallType tm tyArgs) = overallType

instance Structured ILExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            ILBool         b    -> out $ "ILBool      " ++ (show b)
            ILCall    t b a     -> out $ "ILCall      " ++ " :: " ++ show t
            ILCallPrim t prim a -> out $ "ILCallPrim  " ++ (show prim) ++ " :: " ++ show t
            ILAppCtor t cid vs  -> out $ "ILAppCtor   " ++ (show cid) ++ " :: " ++ show t
            ILClosures ns cs e  -> out $ "ILClosures  " ++ show (map showClosurePair (zip ns cs))
            ILLetVal   x b e    -> out $ "ILLetVal    " ++ (show x) ++ " :: " ++ (show $ typeIL b) ++ " = ... in ... "
            ILIf      t  a b c  -> out $ "ILIf        " ++ " :: " ++ show t
            ILUntil   t  a b    -> out $ "ILUntil     " ++ " :: " ++ show t
            ILInt ty int        -> out $ "ILInt       " ++ (litIntText int) ++ " :: " ++ show ty
            ILAlloc v           -> out $ "ILAlloc     "
            ILDeref t a         -> out $ "ILDeref     "
            ILStore t a b       -> out $ "ILStore     "
            ILCase t _ bnds dt  -> (out "ILCase     \n") ++ (showStructure dt)
            ILAllocArray _ _    -> out $ "ILAllocArray "
            ILArrayRead  t a b  -> out $ "ILArrayRead " ++ " :: " ++ show t
            ILArrayPoke v b i   -> out $ "ILArrayPoke "
            ILTuple     es      -> out $ "ILTuple     (size " ++ (show $ length es) ++ ")"
            ILVar (TypedId t (GlobalSymbol name))
                                -> out $ "ILVar(Global):   " ++ name ++ " :: " ++ show t
            ILVar (TypedId t i)
                                -> out $ "ILVar(Local):   " ++ show i ++ " :: " ++ show t
            ILTyApp t e argty   -> out $ "ILTyApp     [" ++ show argty ++ "] :: " ++ show t
        where
            showClosurePair :: (Ident, ILClosure) -> String
            showClosurePair (name, clo) = (show name) ++ " bound to " ++ (show clo)
    structuredChildren e =
        case e of
            ILLetVal x b a -> let (bindings, final) = slurpLets e
                              in (map SS bindings) ++ [SS final]
            _              -> map SS $ childrenOf e
    childrenOf e =
        let var v = ILVar v in
        case e of
            ILBool b                -> []
            ILInt t _               -> []
            ILUntil t a b           -> [a, b]
            ILTuple     vs          -> map var vs
            ILCase _ e bs _dt       -> (var e):(map snd bs)
            ILClosures bnds clos e  -> [e]
            ILLetVal x b e          -> [b, e]
            ILCall     t v vs       -> [var v] ++ [var v | v <- vs]
            ILCallPrim t v vs       ->            [var v | v <- vs]
            ILAppCtor t c vs       ->             [var v | v <- vs]
            ILIf    t v b c         -> [var v, b, c]
            ILAlloc   v             -> [var v]
            ILAllocArray _ v        -> [var v]
            ILDeref t v             -> [var v]
            ILStore t v w           -> [var v, var w]
            ILArrayRead t a b       -> [var a, var b]
            ILArrayPoke v b i       -> [var v, var b, var i]
            ILVar _                 -> []
            ILTyApp t v argty       -> [var v]

slurpLets :: ILExpr -> ([StructuredBinding Ident ILExpr], ILExpr)
slurpLets (ILLetVal x b a) =
                let (sbs, fin) = slurpLets a in
                ( (StructuredBinding x b):sbs, fin )
slurpLets a = ([], a)

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
