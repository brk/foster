-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Debug.Trace(trace)
import Control.Monad.State
import Data.Set(Set)
import Data.Set as Set(fromList, toList, difference, member)
import Data.Map(Map)
import qualified Data.Map as Map((!), fromList, member, keys, elems, findWithDefault)

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

data ILProgram = ILProgram [ILProcDef] [ILDecl] [DataType TypeIL] SourceLines
data ILDecl    = ILDecl String TypeIL deriving (Show)

data ILProcDef = ILProcDef { ilProcReturnType :: TypeIL
                           , ilProcIdent      :: Ident
                           , ilProcVars       :: [AIVar]
                           , ilProcRange      :: ESourceRange
                           , ilProcCallConv   :: CallConv
                           , ilProcBody       :: ILExpr
                           } deriving Show
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
        | ILTyApp       TypeIL ILExpr TypeIL
        deriving (Show)
data AllocMemRegion = MemRegionStack
                    | MemRegionGlobalHeap
data ILAllocInfo = ILAllocInfo AllocMemRegion (Maybe AIVar)

showProgramStructure :: ILProgram -> Output
showProgramStructure (ILProgram procdefs decls _dtypes _lines) =
    concatMap showProcStructure procdefs

procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

showProcStructure proc =
    out (show $ ilProcIdent proc) ++ (out " // ")
        ++ (out $ show $ map procVarDesc (ilProcVars proc))
        ++ (out " @@@ ") ++ (out $ show $ ilProcCallConv proc)
        ++ (out "\n") ++  showStructure (ilProcBody proc)
      ++ out "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"

type KnownVars = Set String

data ILMState = ILMState {
    ilmUniq    :: Uniq
  , ilmGlobals :: KnownVars
  , ilmProcDefs :: [ILProcDef]
  , ilmCtors   :: DataTypeSigs
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
        put (old { ilmProcDefs = p:(ilmProcDefs old) })
        return p

fakeCloEnvType = TupleTypeIL []

closureConvertAndLift :: Context TypeIL -> DataTypeSigs
                      -> (ModuleAST (Fn KNExpr) TypeIL)
                      -> ILProgram
closureConvertAndLift ctx dataSigs m =
    let fns = moduleASTfunctions m in
    let decls = map (\(s,t) -> ILDecl s t) (moduleASTdecls m) in
    -- We lambda lift top level functions, since we know they don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let nameOfBinding (TermVarBinding s _) = s in
    let globalVars = Set.fromList $ map nameOfBinding (contextBindings ctx) in
    let procsILM = forM fns (\fn -> lambdaLift ctx fn []) in
    let dataTypes = moduleASTdataTypes m in
    let newstate = execState procsILM (ILMState 0 globalVars [] dataSigs) in
    ILProgram (ilmProcDefs newstate) decls dataTypes (moduleASTsourceLines m)

prependILBinding :: (Ident, ILExpr) -> Context TypeIL -> Context TypeIL
prependILBinding (id, ile) ctx =
    let annvar = TypedId (typeIL ile) id in
    prependContextBinding ctx (TermVarBinding (identPrefix id) annvar)

-- Note that closure conversion is combined with the transformation from
-- AnnExpr to ILExpr, which mainly consists of making evaluation order for
-- the subexpressions of tuples and calls (etc) explicit.
closureConvert :: Context TypeIL -> KNExpr -> ILM ILExpr
closureConvert ctx expr =
        let g = closureConvert ctx in
        case expr of
            KNBool b          -> return $ ILBool b
            KNInt t i         -> return $ ILInt t i
            KNVar v           -> return $ ILVar v
            KNAllocArray t v  -> return $ ILAllocArray t v
            KNAlloc v         -> return $ ILAlloc v
            KNDeref t v       -> return $ ILDeref t v
            KNStore t a b     -> return $ ILStore t a b
            KNArrayRead t a b -> return $ ILArrayRead t a b
            KNArrayPoke a b c -> return $ ILArrayPoke a b c
            KNTuple     vs    -> return $ ILTuple vs
            KNCallPrim t p vs -> return $ ILCallPrim t p vs
            KNAppCtor  t c vs -> return $ ILAppCtor  t c vs
            KNCall     t b vs -> return $ ILCall     t b vs

            KNTyApp t e argty -> do e' <- g e ; return $ ILTyApp t e' argty
            KNIf t v a b      -> do [a', b'] <- mapM g [a, b] ; return $ ILIf t v a' b'
            KNUntil t a b     -> do [a', b'] <- mapM g [a, b] ; return $ ILUntil t a' b'

            KNLetVal id a b -> do a' <- closureConvert ctx  a
                                  let extctx = prependILBinding (id, a') ctx
                                  b' <- closureConvert extctx b
                                  return $ ILLetVal id a' b'

            KNLetFuns ids fns e   -> do
                cloEnvIds <- mapM (\id -> ilmFresh (".env." ++ identPrefix id)) ids

                let cloEnvBinding id = TermVarBinding (identPrefix id) (TypedId fakeCloEnvType id)
                let extctx = prependContextBindings ctx (map cloEnvBinding cloEnvIds)

                let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
                let idfns = zip ids fns

                closedNms <- mapM (closedNamesOfKnFn    infoMap) idfns
                combined  <- mapM (closureOfKnFn extctx infoMap) (zip closedNms idfns)
                let (closures, _procdefs) = unzip combined
                e' <- closureConvert extctx e
                return $ ILClosures ids closures e'

            KNCase t v bs -> do ibs <- mapM (\(p, a) -> do
                                               let bindings = patternBindings (p, tidType v)
                                               let extctx = prependContextBindings ctx bindings
                                               a' <- closureConvert extctx a
                                               return (p, a' )) bs
                                allSigs <- gets ilmCtors
                                let dt = compilePatterns ibs allSigs
                                return $ ILCase t v ibs dt

closureConvertedProc :: [AIVar] -> (Fn KNExpr) -> ILExpr -> ILM ILProcDef
closureConvertedProc liftedProcVars f newbody = do
    let (TypedId ft id) = fnVar f
    return $ ILProcDef (fnTypeILRange ft) id liftedProcVars
              (fnRange f) FastCC newbody

-- For example, if we have something like
--      let y = blah in ( (\x -> x + y) foobar )
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \y x -> x + y
--      let y = blah in p(y, foobar)
lambdaLift :: Context TypeIL -> (Fn KNExpr) -> [AIVar] -> ILM ILProcDef
lambdaLift ctx f freeVars =
    let liftedProcVars = freeVars ++ fnVars f in
    let extctx = prependContextBindings ctx (bindingsForVars liftedProcVars) in
    -- Ensure the free vars in the body are bound in the ctx...
     do newbody <- closureConvert extctx (fnBody f)
        ilmPutProc (closureConvertedProc liftedProcVars f newbody)

bindingsForVars vars = [TermVarBinding (identPrefix i) v
                       | v@(TypedId t i) <- vars]

type FreeName = Ident

contextVar :: String -> Context TypeIL -> FreeName -> AIVar
contextVar dbg ctx s =
    case termVarLookup (identPrefix s) (contextBindings ctx) of
            Just v -> v
            Nothing -> error $ "ILExpr: " ++ dbg ++ " free var not in context: " ++ show s ++ "\n" ++ showctx (contextBindings ctx)
                       --TypedId (NamedTypeIL "i32") (Ident ("{" ++ show s ++ "-NCTX-" ++ dbg ++ "}\n" ++ (showctx (contextBindings ctx))) 0)
    where showctx bindings =
            "Bindings in context: " ++
              (joinWith ", " $ map (\(TermVarBinding nm v) -> show $ tidIdent v) bindings)

excluding :: Ord a => [a] -> Set a -> [a]
excluding bs zs =  Set.toList $ Set.difference (Set.fromList bs) zs

type InfoMap = Map Ident ((Fn KNExpr), Ident)

instance (AExpr expr) => AExpr (Fn expr) where
    freeIdents f = let bodyvars =  freeIdents (fnBody f) in
                   let boundvars = map tidIdent (fnVars f) in
                   bodyvars `butnot` boundvars

instance AExpr KNExpr where
    freeIdents e = case e of
        KNVar v             -> [tidIdent v]
        KNLetVal id a b     -> freeIdents a ++ (freeIdents b `butnot` [id])
        KNCase _t v patbnds ->  tidIdent v : concatMap patBindingFreeIds patbnds
        -- Note that all free idents of the bound expr are free in letvar,
        -- but letfuns removes the bound name from that set!
        KNLetFuns ids fns e -> ((concatMap freeIdents fns) ++ (freeIdents e)) `butnot` ids
        _               -> concatMap freeIdents (childrenOf e)

closedNamesOfKnFn :: InfoMap
                  -> (Ident, (Fn KNExpr))
                  -> ILM [FreeName]
closedNamesOfKnFn infoMap (self_id, fn) = do
    -- ids are the names of the recursively bound functions
    let ids      =          Map.keys  infoMap
    let envIds   = map snd (Map.elems infoMap)
    {- Given   rec f = { ... f() .... };
                   g = { ... f() .... };
               in ... end;
       neither f nor g should close over the closure f itself, or any global
       vars. Nor does the closure converted proc capture its own environment
       variable, because it will be added as an implicit parameter. The
       environment for f, however, *is* closed over in g.
    -}
    let rawFreeIds = freeIdents fn `excluding` (Set.fromList [self_id])

    -- Have (i.e.) g capture f's env var instead of "f" itself,
    -- and make sure we filter out the global names.
    globalVars <- gets ilmGlobals
    let envFor = Map.fromList $ zip ids envIds
    let freeIds = map (\n -> Map.findWithDefault n n envFor) rawFreeIds

    return $ trace ("freeNames("++ show self_id++") = " ++ show freeIds)
             filter (\id -> not $ Set.member (identPrefix id) globalVars)
                    freeIds

closureOfKnFn :: Context TypeIL
               -> InfoMap
               -> ([FreeName], (Ident, (Fn KNExpr)))
               -> ILM (ILClosure, ILProcDef)
closureOfKnFn ctx0 infoMap (closedNames, (self_id, fn)) = do
    let extctx = prependContextBindings ctx0 (bindingsForVars (fnVars fn))
    let transformedFn = makeEnvPassingExplicitFn fn
    (envVar, newproc) <- closureConvertFn extctx transformedFn infoMap closedNames

    -- Look up each captured var in the environment to determine what its
    -- type is. This is a sanity check that the names we need to close over
    -- are actually there to be closed over, with known types.
    let capturedVars = map (\n -> contextVar ("closureOfKnFn (" ++ show self_id ++")")
                                              extctx n) closedNames
    return $ trace ("capturedVars for " ++ show self_id ++  ":" ++ (show $ capturedVars)) $
         --trace ("raw closedNames for " ++ show self_id ++  ":" ++ (show $ freeIdents (E_AIFn fn))) $
        (ILClosure (ilProcIdent newproc) envVar capturedVars, newproc)
  where
    closureConvertFn :: Context TypeIL -> Fn KNExpr -> InfoMap -> [FreeName] -> ILM (Ident, ILProcDef)
    closureConvertFn ctx f info freeNames = do
        let envId        = snd (info Map.! self_id)
        let uniqFreeVars = map (contextVar "closureConvertKnFnUFV" ctx) freeNames
        let envTypes = map tidType uniqFreeVars
        let envVar   = TypedId (TupleTypeIL envTypes) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- let oldbody = fnBody f in
                   let norange = EMissingSourceRange "" in
                   let patVar a = P_Variable norange (tidIdent a) in
                   closureConvert ctx $
                     KNCase (typeKN oldbody) envVar
                        [ (P_Tuple norange (map patVar uniqFreeVars)
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
        KNBool       {} -> e
        KNInt        {} -> e
        KNVar        {} -> e
        KNAllocArray {} -> e
        KNAlloc      {} -> e
        KNDeref      {} -> e
        KNStore      {} -> e
        KNArrayRead  {} -> e
        KNArrayPoke  {} -> e
        KNTuple      {} -> e
        KNCallPrim   {} -> e
        KNAppCtor    {} -> e

        KNIf t v b c           -> KNIf    t v (q b) (q c)
        KNUntil t a b          -> KNUntil t   (q a) (q b)
        KNLetVal id a b        -> KNLetVal id (q a) (q b)
        KNLetFuns ids fns e    -> KNLetFuns ids (map fq fns) (q e)
        KNCase t v bs          -> KNCase t v [(p, q e) | (p, e) <- bs]
        KNTyApp  t e argty     -> KNTyApp t (q e) argty

        -- The only really interesting case:
        KNCall t v vs
            | Map.member (tidIdent v) infoMap ->
                let (f, envid) = infoMap Map.! (tidIdent v) in
                -- We don't know the env type here, since we don't
                -- pre-collect the set of closed-over envs from other procs.
                let env = TypedId fakeCloEnvType envid in
                          -- This works because (A) we never type check ILExprs,
                          -- and (B) the LLVM codegen doesn't check the type field in this case.
                KNCall t (fnVar f) (env:vs)  -- Call proc, passing env as first parameter.
        -- TODO when is guard above false?
        KNCall   t v vs -> KNCall t v vs

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
            ILTyApp t e argty       -> [e]

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
