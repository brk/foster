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
import Foster.AnnExprIL
import Foster.PatternMatch

{--
Foster.ILExpr binds all intermediate values to named variables
via a variant of K-normalization. To avoid Yet Another Intermediate Language,
the transformation from AnnExpr to ILExpr is combined with closure conversion
and lambda lifting.

closureConvertAndLift :: Context TypeIL
                      -> (ModuleAST (Fn AIExpr) TypeIL)
                      -> ILProgram
--}

data ILClosure = ILClosure { ilClosureProcIdent :: Ident
                           , ilClosureEnvIdent  :: Ident
                           , ilClosureCaptures  :: [AIVar] } deriving Show

data ILProgram = ILProgram [ILProcDef] [ILDecl] SourceLines
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
showProgramStructure (ILProgram procdefs decls _lines) =
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

closureConvertAndLift :: Context TypeIL
                      -> (ModuleAST (Fn AIExpr) TypeIL)
                      -> ILProgram
closureConvertAndLift ctx m =
    let fns = moduleASTfunctions m in
    let decls = map (\(s,t) -> ILDecl s t) (moduleASTdecls m) in
    -- We lambda lift top level functions, since we know they don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let nameOfBinding (TermVarBinding s _) = s in
    let globalVars = Set.fromList $ map nameOfBinding (contextBindings ctx) in
    let procsILM = forM fns (\fn -> lambdaLift ctx fn []) in
    let newstate = execState procsILM (ILMState 0 globalVars []) in
    ILProgram (ilmProcDefs newstate) decls (moduleASTsourceLines m)

prependILBinding :: (Ident, ILExpr) -> Context TypeIL -> Context TypeIL
prependILBinding (id, ile) ctx =
    let annvar = TypedId (typeIL ile) id in
    prependContextBinding ctx (TermVarBinding (identPrefix id) annvar)

-- Note that closure conversion is combined with the transformation from
-- AnnExpr to ILExpr, which mainly consists of making evaluation order for
-- the subexpressions of tuples and calls (etc) explicit.
closureConvert :: Context TypeIL -> AIExpr -> ILM ILExpr
closureConvert ctx expr =
        let g = closureConvert ctx in
        case expr of
            AIBool b          -> return $ ILBool b
            AIInt t i         -> return $ ILInt t i
            E_AIVar v         -> return $ ILVar v
            E_AIPrim p -> error $ "ILExpr.closureConvert: Should have detected prim " ++ show p
            AIIf      t  a b c    -> do x <- ilmFresh ".ife"
                                        [a', b', c'] <- mapM g [a, b, c]
                                        let v = (TypedId (typeIL a') x)
                                        return $ buildLet x a' (ILIf t v b' c')

            AIUntil   t  a b      -> do [a', b'] <- mapM g [a, b]
                                        return $ (ILUntil t a' b')

            AILetVar id a b       -> do a' <- closureConvert ctx  a
                                        let ctx' = prependILBinding (id, a') ctx
                                        b' <- closureConvert ctx' b
                                        return $ buildLet id a' b'

            AILetFuns ids fns e   -> do
                cloEnvIds <- mapM (\id -> ilmFresh (".env." ++ identPrefix id)) ids

                let cloEnvBinding id = TermVarBinding (identPrefix id) (TypedId fakeCloEnvType id)
                let ext = prependContextBindings ctx (map cloEnvBinding cloEnvIds)

                let infoMap = Map.fromList (zip ids (zip fns cloEnvIds))
                let idfns = zip ids fns

                closedNms <- mapM (closedNamesOfAIFn infoMap) idfns
                combined  <- mapM (closureOfAIFn ext infoMap) (zip closedNms idfns)
                let (closures, _procdefs) = unzip combined
                e' <- closureConvert ext e
                return $ ILClosures ids closures e'

            AIAllocArray t a      -> do a' <- g a
                                        nestedLets [a'] (\[x] -> ILAllocArray t x)
            AIAlloc a             -> do a' <- g a
                                        nestedLets [a'] (\[x] -> ILAlloc x)
            AIDeref t a           -> do a' <- g a
                                        nestedLets [a'] (\[x] -> ILDeref t x)
            AIStore t a (AISubscript _t b c)
                                   -> do [a', b', c'] <- mapM g [a, b, c]
                                         nestedLets [a', b', c'] (\[x, y, z] ->
                                                ILArrayPoke x y z)
            AIStore t a b         -> do [a', b'] <- mapM g [a, b]
                                        nestedLets [a', b'] (\[x, y] -> ILStore t x y)
            AISubscript t a b     -> do [a', b'] <- mapM g [a, b]
                                        nestedLets [a', b'] (\[va, vb] -> ILArrayRead t va vb)

            AITuple     es        -> do cs <- mapM g es
                                        nestedLets cs (\vs -> ILTuple vs)

            AICase t e bs         -> do e' <- g e
                                        ibs <- mapM (\(p, a) -> do
                                                       let bindings = patternBindings (p, typeAI e)
                                                       let ctx' = prependContextBindings ctx bindings
                                                       a' <- closureConvert ctx' a
                                                       return (p, a' )) bs
                                        let allSigs = []
                                        let dt = compilePatterns ibs allSigs
                                        nestedLets [e'] (\[va] -> ILCase t va ibs (trace (show dt) dt))
            E_AITyApp t e argty   -> do e' <- g e
                                        return $ ILTyApp t e' argty

            -- Eliminate function literals by translating
            -- them to named closures.
            -- We avoid doing this earlier only to enable
            -- special-case optimization for {...}()
            x@(E_AIFn fn)        -> do
                clo_id <- ilmFresh "lit_clo"
                let clovar = E_AIVar $ TypedId (typeAI x) clo_id
                g (AILetFuns [clo_id] [fn] clovar)

            AICall    t b es -> do
                cargs <- mapM g es
                case b of
                    (E_AIFn f) -> do -- If we're calling a function directly,
                                     -- we know we can perform lambda lifting
                                     -- on it, by adding args for its free variables.
                                    globalVars <- gets ilmGlobals
                                    let freeNames = (map identPrefix $ freeIdents b) `excluding` globalVars
                                    let freevars = map (contextVar "ANnCall" ctx) freeNames
                                    newproc <- lambdaLift ctx f freevars
                                    let procid = (ilProcIdent newproc)
                                    let (argtys, retty, cc) = preProcType newproc
                                    let procty = FnTypeIL argtys retty cc FT_Proc
                                    let p = TypedId procty procid
                                    nestedLets cargs (\vars -> ILCall t p (freevars ++ vars))

                    (E_AIPrim p) -> do nestedLets cargs (\vars -> (ILCallPrim t p vars))
                    (E_AIVar v)  -> do nestedLets cargs (\vars -> (ILCall t v vars))
                    _ -> do cb <- g b; nestedLets (cb:cargs) (\(vb:vars) -> (ILCall t vb vars))

closureConvertedProc :: [AIVar] -> (Fn AIExpr) -> ILExpr -> ILM ILProcDef
closureConvertedProc liftedProcVars f newbody = do
    -- Ensure that return values are codegenned through a variable binding.
    namedReturnValue <- nestedLets [newbody] (\[rv] -> ILVar rv)
    return $ ILProcDef (fnTypeILRange (fnType f))
              (fnIdent f) liftedProcVars
              (fnRange f) FastCC namedReturnValue

-- For example, if we have something like
--      let y = blah in ( (\x -> x + y) foobar )
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \y x -> x + y
--      let y = blah in p(y, foobar)
lambdaLift :: Context TypeIL -> (Fn AIExpr) -> [AIVar] -> ILM ILProcDef
lambdaLift ctx f freeVars =
    let liftedProcVars = freeVars ++ fnVars f in
    let extctx = prependContextBindings ctx (bindingsForVars liftedProcVars) in
    -- Ensure the free vars in the body are bound in the ctx...
     do newbody <- closureConvert extctx (fnBody f)
        ilmPutProc (closureConvertedProc liftedProcVars f newbody)
    where
        bindingsForVars vars = [TermVarBinding (identPrefix i) v
                               | v@(TypedId t i) <- vars]

preProcType proc =
    let retty = ilProcReturnType proc in
    let argtys = TupleTypeIL (map tidType (ilProcVars proc)) in
    let cc = ilProcCallConv proc in
    (argtys, retty, cc)

contextVar :: String -> Context TypeIL -> String -> AIVar
contextVar dbg ctx s =
    case termVarLookup s (contextBindings ctx) of
            Just v -> v
            Nothing -> error $ "ILExpr: " ++ dbg ++ " free var not in context: " ++ s ++ "\n" ++ showctx (contextBindings ctx)
                       --TypedId (NamedTypeIL "i32") (Ident ("{" ++ s ++ "-NCTX-" ++ dbg ++ "}") 0)
    where showctx bindings =
            show $ map (\(TermVarBinding nm v) -> nm ++ "/" ++ (show $ tidIdent v)) bindings

buildLet :: Ident -> ILExpr -> ILExpr -> ILExpr
buildLet ident bound inexpr =
  case bound of
    (ILLetVal x' e' c') ->
         -- let i = (let x' = e' in c') in inexpr
         -- ==>
         -- let x' = e' in (let i = c' in inexpr)
         ILLetVal x' e' (buildLet ident c' inexpr)
    _ -> ILLetVal ident bound inexpr

-- | If we have a call like    base(foo, bar, blah)
-- | we want to transform it so that the args are all variables:
-- | let x1 = foo in
-- |  let x2 = bar in
-- |   let x3 = blah in
-- |     base(x1,x2,x3)
nestedLets :: [ILExpr] -> ([AIVar] -> ILExpr) -> ILM ILExpr
-- | The fresh variables will be accumulated and passed to a
-- | continuation which generates a LetVal expr using the variables.
nestedLets exprs g = nestedLets' exprs [] g
  where
    nestedLets' :: [ILExpr] -> [AIVar] -> ([AIVar] -> ILExpr) -> ILM ILExpr
    nestedLets' []     vars k = return $ k (reverse vars)
    nestedLets' (e:es) vars k =
        case e of
          -- No point in doing  let var1 = var2 in e...
          -- Instead, pass var2 to k instead of var1.
          (ILVar v) -> nestedLets' es (v:vars) k
          otherwise -> do
            x        <- ilmFresh ".x"
            let v = TypedId (typeIL e) x
            innerlet <- nestedLets' es (v:vars) k
            return $ buildLet x e innerlet

excluding :: Ord a => [a] -> Set a -> [a]
excluding bs zs =  Set.toList $ Set.difference (Set.fromList bs) zs

type InfoMap = Map Ident ((Fn AIExpr), Ident)

closedNamesOfAIFn :: InfoMap
                  -> (Ident, (Fn AIExpr))
                  -> ILM [String]
closedNamesOfAIFn infoMap (self_id, fn) = do
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
    let rawFreeIds = freeIdents (E_AIFn fn) `excluding` (Set.fromList [self_id])

    -- Have (i.e.) g capture f's env var instead of "f" itself,
    -- and make sure we filter out the global names.
    globalVars <- gets ilmGlobals
    let envFor = Map.fromList $ zip ids envIds
    let freeNames = map (\n -> Map.findWithDefault n n envFor) rawFreeIds

    return $ trace ("freeNames("++ show self_id++") = " ++ show freeNames)
             filter (\name -> not $ Set.member name globalVars)
                    (map identPrefix freeNames)

closureOfAIFn :: Context TypeIL
               -> InfoMap
               -> ([String], (Ident, (Fn AIExpr)))
               -> ILM (ILClosure, ILProcDef)
closureOfAIFn ctx infoMap (closedNames, (self_id, fn)) = do
    let transformedFn = makeEnvPassingExplicit (E_AIFn fn)
    (envVar, newproc) <- closureConvertFn transformedFn infoMap closedNames

    -- Look up each captured var in the environment to determine what its
    -- type is. This is a sanity check that the names we need to close over
    -- are actually there to be closed over, with known types.
    let capturedVars = map (\n -> contextVar ("closureOfAIFn (" ++ show self_id ++")")
                                              ctx n) closedNames
    return $ trace ("capturedVars for " ++ show self_id ++  ":" ++ (show $ capturedVars)) $
         --trace ("raw closedNames for " ++ show self_id ++  ":" ++ (show $ freeIdents (E_AIFn fn))) $
        (ILClosure (ilProcIdent newproc) envVar capturedVars, newproc)
  where
    closureConvertFn :: AIExpr -> InfoMap -> [String] -> ILM (Ident, ILProcDef)
    closureConvertFn (E_AIFn f) info freeNames = do
        let envId        = snd (info Map.! self_id)
        let uniqFreeVars = map (contextVar "closureConvertAIFn" ctx) freeNames
        let envTypes = map tidType uniqFreeVars
        let envVar   = TypedId (TupleTypeIL envTypes) envId

        -- If the body has x and y free, the closure converted body should be
        --     case env of (x, y, ...) -> body end
        newbody <- let oldbody = fnBody f in
                   let norange = EMissingSourceRange "closureConvertAIFn" in
                   let patVar a = P_Variable norange (tidIdent a) in
                   closureConvert ctx $
                     AICase (typeAI oldbody) (E_AIVar envVar)
                        [ (P_Tuple norange (map patVar uniqFreeVars)
                          , oldbody) ]
        proc <- ilmPutProc (closureConvertedProc (envVar:(fnVars f)) f newbody)
        return (envId, proc)
    closureConvertFn _ info freeNames = error "closureConvertAIFn called on non-fn"

    makeEnvPassingExplicit :: AIExpr -> AIExpr
    makeEnvPassingExplicit expr =
      q expr where
      fq (Fn ty id vars body rng) = (Fn ty id vars (q body) rng)
      q e = case e of
        AIBool  {}       -> e
        AIInt   {}       -> e
        E_AIVar {}       -> e -- We don't alter standalone references to closures
        E_AIPrim p       -> e
        AIIf t a b c         -> AIIf      t (q a) (q b) (q c)
        AIUntil t a b        -> AIUntil   t (q a) (q b)
        AILetVar id a b      -> AILetVar id (q a) (q b)
        AILetFuns ids fns e  -> AILetFuns ids (map fq fns) (q e)
        AIAllocArray t a -> AIAllocArray t (q a)
        AIAlloc a        -> AIAlloc   (q a)
        AIDeref t a      -> AIDeref t (q a)
        AIStore t a b    -> AIStore t (q a) (q b)
        E_AIFn f               -> E_AIFn (fq f)
        AISubscript t a b      -> AISubscript t (q a) (q b)
        AITuple es             -> AITuple (map q es)
        AICase t e bs          -> AICase t (q e) [(p, q e) | (p, e) <- bs]
        E_AITyApp  t e argty   -> E_AITyApp t (q e) argty
        -- The only really interesting case:
        AICall     t (E_AIVar v) es
            | Map.member (tidIdent v) infoMap ->
                let (f, envid) = infoMap Map.! (tidIdent v) in
                let procId = TypedId (fnType f) (fnIdent f) in
                -- We don't know the env type here, since we don't
                -- pre-collect the set of closed-over envs from other procs.
                let env = E_AIVar (TypedId fakeCloEnvType envid) in
                          -- This works because (A) we never type check ILExprs,
                          -- and (B) the LLVM codegen doesn't check the type field in this case.
                -- Call proc, passing env as first parameter.
                AICall t (E_AIVar procId) (env:(map q es))
        -- TODO when is guard above false?
        AICall   t b es -> AICall   t (q b) (map q es)

typeIL :: ILExpr -> TypeIL
typeIL (ILBool _)          = NamedTypeIL "i1"
typeIL (ILInt t _)         = t
typeIL (ILTuple vs)        = TupleTypeIL (map tidType vs)
typeIL (ILClosures n b e)  = typeIL e
typeIL (ILLetVal x b e)    = typeIL e
typeIL (ILCall t id expr)  = t
typeIL (ILCallPrim t id e) = t
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

typeAI :: AIExpr -> TypeIL
typeAI (AIBool _)          = NamedTypeIL "i1"
typeAI (E_AIVar tid)       = tidType tid
typeAI (E_AIPrim (ILNamedPrim tid)) = tidType tid
typeAI (E_AIPrim p) = error $ "typeAI not defined for prim " ++ show p
typeAI (AIInt t _)         = t
typeAI (AITuple es)        = TupleTypeIL (map typeAI es)
typeAI (AICall t b a)      = t
typeAI (AIAllocArray elt_ty _) = ArrayTypeIL elt_ty
typeAI (AIIf t a b c)      = t
typeAI (AIUntil t _ _)     = t
typeAI (AILetVar _ a b)    = typeAI b
typeAI (AILetFuns _ _ e)   = typeAI e
typeAI (AIAlloc e)         = PtrTypeIL (typeAI e)
typeAI (AIDeref t _)       = t
typeAI (AIStore t _ _)     = t
typeAI (AISubscript t _ _) = t
typeAI (AICase t _ _)      = t
typeAI (E_AITyApp substitutedTy tm tyArgs) = substitutedTy
typeAI (E_AIFn fn)       = fnType fn

instance Structured ILExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            ILBool         b    -> out $ "ILBool      " ++ (show b)
            ILCall    t b a     -> out $ "ILCall      " ++ " :: " ++ show t
            ILCallPrim t prim a -> out $ "ILCallPrim  " ++ (show prim) ++ " :: " ++ show t
            ILClosures ns cs e  -> out $ "ILClosures  " ++ show (map showClosurePair (zip ns cs))
            ILLetVal   x b e    -> out $ "ILLetVal    " ++ (show x) ++ " :: " ++ (show $ typeIL b) ++ " = ... in ... "
            ILIf      t  a b c  -> out $ "ILIf        " ++ " :: " ++ show t
            ILUntil   t  a b    -> out $ "ILUntil     " ++ " :: " ++ show t
            ILInt ty int        -> out $ "ILInt       " ++ (litIntText int) ++ " :: " ++ show ty
            ILAlloc v           -> out $ "ILAlloc     "
            ILDeref t a         -> out $ "ILDeref     "
            ILStore t a b       -> out $ "ILStore     "
            ILCase t _ bnds _   -> out $ "ILCase      " ++ (show $ map fst bnds)
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
    P_Tuple    rng pats ->
      case ty of
        TupleTypeIL tys -> concatMap patternBindings (zip pats tys)
        otherwise -> (error $ "patternBindings failed on typechecked pattern!"
                                ++ "\np = " ++ show p ++ " ; ty = " ++ show ty)
