-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Debug.Trace(trace)
import Control.Monad.State
import Data.Set(Set)
import Data.Set as Set(fromList, toList, difference, union)
import Data.Map(Map)
import qualified Data.Map as Map((!), fromList, member, elems)

import Foster.Base
import Foster.Context
import Foster.TypeAST
import Foster.ExprAST
import Foster.PatternMatch

data ILClosure = ILClosure { ilClosureProcIdent :: Ident
                           , ilClosureCaptures  :: [AnnVar] } deriving Show

data ILProgram = ILProgram [ILProcDef] [ILDecl] SourceLines
data ILDecl    = ILDecl String TypeAST deriving (Show)

data ILProcDef = ILProcDef { ilProcReturnType :: TypeAST
                           , ilProcIdent      :: Ident
                           , ilProcVars       :: [AnnVar]
                           , ilProcRange      :: ESourceRange
                           , ilProcCallConv   :: CallConv
                           , ilProcBody       :: ILExpr
                           } deriving Show
data ILExpr =
          ILBool        Bool
        | ILInt         TypeAST LiteralInt
        | ILTuple       [AnnVar]
        | ILVar         AnnVar
        -- Procedures may be implicitly recursive,
        -- but we need to put a smidgen of effort into
        -- codegen-ing closures so they can be mutually recursive.
        | ILClosures    [Ident] [ILClosure] ILExpr
        | ILLetVal       Ident    ILExpr    ILExpr
        | ILAlloc               AnnVar
        | ILDeref       TypeAST AnnVar
        | ILStore       TypeAST AnnVar AnnVar
        | ILSubscript   TypeAST AnnVar ILExpr
        | ILIf          TypeAST AnnVar ILExpr ILExpr
        | ILUntil       TypeAST ILExpr ILExpr
        | ILCase        TypeAST AnnVar [(Pattern, ILExpr)] (DecisionTree ILExpr)
        | ILCall        TypeAST AnnVar [AnnVar]
        | ILTyApp       TypeAST ILExpr TypeAST
        deriving (Show)

showProgramStructure :: ILProgram -> Output
showProgramStructure (ILProgram procdefs decls _lines) =
    concat [showProcStructure p | p <- procdefs]

procVarDesc (AnnVar ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

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

ilmPutProc :: ILProcDef -> ILM ILProcDef
ilmPutProc p = do
        old <- get
        put (old { ilmProcDefs = p:(ilmProcDefs old) })
        return p

closureConvertAndLift :: Context -> (ModuleAST AnnFn TypeAST) -> ILProgram
closureConvertAndLift ctx m =
    let fns = moduleASTfunctions m in
    let decls = map (\(s,t) -> ILDecl s t) (moduleASTdecls m) in
    -- We lambda lift top level functions, since we know they don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let globalVars = (Set.fromList $ map (\(TermVarBinding s _) -> s) (contextBindings ctx)) in
    let procsILM = forM fns (\fn -> lambdaLift ctx fn []) in
    let newstate = execState procsILM (ILMState 0 globalVars []) in
    ILProgram (ilmProcDefs newstate) decls (moduleASTsourceLines m)

prependAnnBinding (id, expr) ctx =
    let annvar = AnnVar (typeAST expr) id in
    prependContextBinding ctx (TermVarBinding (identPrefix id) annvar)

-- Note that closure conversion is combined with the transformation from
-- AnnExpr to ILExpr, which mainly consists of making evaluation order for
-- the subexpressions of tuples and calls (etc) explicit.
closureConvert :: Context -> AnnExpr -> ILM ILExpr
closureConvert ctx expr =
        let g = closureConvert ctx in
        case expr of
            AnnBool b              -> return $ ILBool b
            AnnCompiles c msg      -> return $ ILBool (c == CS_WouldCompile)
            AnnInt t i             -> return $ ILInt t i
            E_AnnVar v             -> return $ ILVar v

            AnnIf      t  a b c    -> do x <- ilmFresh ".ife"
                                         [a', b', c'] <- mapM g [a, b, c]
                                         let v = AnnVar (typeIL a') x
                                         return $ buildLet x a' (ILIf t v b' c')

            AnnUntil   t  a b      -> do x <- ilmFresh ".until"
                                         [a', b'] <- mapM g [a, b]
                                         return $ (ILUntil t a' b')

            AnnLetVar id a b       -> do let ctx' = prependAnnBinding (id, a) ctx
                                         a' <- closureConvert ctx' a
                                         b' <- closureConvert ctx' b
                                         return $ buildLet id a' b'

            AnnLetFuns ids fns e   -> do let idfns = zip ids fns
                                         cloEnvIds <- mapM (\id -> ilmFresh (".env." ++ identPrefix id)) ids
                                         let info = Map.fromList (zip ids (zip fns cloEnvIds))
                                         combined <- mapM (closureOfAnnFn ctx idfns info) idfns
                                         let (closures, _procdefs) = unzip combined
                                         e' <- g e
                                         return $ ILClosures ids closures e'

            AnnAlloc a             -> do a' <- g a
                                         nestedLets [a'] (\[x] -> ILAlloc x)
            AnnDeref t a           -> do a' <- g a
                                         nestedLets [a'] (\[x] -> ILDeref t x)
            AnnStore t a b         -> do [a', b'] <- mapM g [a, b]
                                         nestedLets [a', b'] (\[x, y] -> ILStore t x y)
            AnnSubscript t a b     -> do [a', b'] <- mapM g [a, b]
                                         nestedLets [a'] (\[va] -> ILSubscript t va b')

            AnnTuple     es        -> do cs <- mapM g es
                                         nestedLets cs (\vs -> ILTuple vs)

            AnnCase t e bs         -> do e' <- g e
                                         ibs <- mapM (\(p, a) -> do
                                                        let bindings = patternBindings (p, typeAST e)
                                                        let ctx' = prependContextBindings ctx bindings
                                                        a' <- closureConvert ctx' a
                                                        return (p, a' )) bs
                                         let allSigs = []
                                         let dt = compilePatterns ibs allSigs
                                         nestedLets [e'] (\[va] -> ILCase t va ibs (trace (show dt) dt))
            E_AnnTyApp t e argty   -> do e' <- g e
                                         return $ ILTyApp t e' argty

            E_AnnFn annFn          -> do
                clo_id <- ilmFresh "lit_clo"
                g (AnnLetFuns [clo_id] [annFn] (E_AnnVar $ AnnVar (typeAST (E_AnnFn annFn)) clo_id))

            AnnCall  r t b es -> do
                cargs <- mapM g es
                case b of
                    (E_AnnVar v) -> do nestedLets cargs (\vars -> (ILCall t v vars))
                    (E_AnnFn f) -> do -- If we're calling a function directly,
                                     -- we know we can perform lambda lifting
                                     -- on it, by adding args for its free variables.
                                    globalVars <- gets ilmGlobals
                                    let freeNames = (map identPrefix $ freeIdentsA b) `excluding` globalVars
                                    let freevars = map (contextVar "ANnCall" ctx) freeNames
                                    newproc <- lambdaLift ctx f freevars
                                    let procid = (ilProcIdent newproc)
                                    let procvar = (AnnVar (procType newproc) procid)
                                    nestedLets cargs (\vars -> ILCall t procvar (freevars ++ vars))

                    -- v[types](args) =>
                    -- let <fresh> = v[types] in <fresh>(args)
                    -- TODO generate coro primitives here?
                    -- Because the LLVM implementation specializes coro functions
                    -- (at compile time)
                    -- to produce a distinguished (function pointer) value,
                    -- whereas the interpreter treats the coroutine primitives specially.
                    (E_AnnTyApp ot (E_AnnVar v) argty) -> do
                                    x <- ilmFresh $ "appty_" ++ (identPrefix $ avarIdent v)
                                    let var = AnnVar ot x
                                    nlets <- nestedLets cargs (\vars -> ILCall t var vars)
                                    return $ buildLet x (ILTyApp ot (ILVar v) argty) nlets
                    _ -> error $ "AnnCall with non-var base of " ++ show b

closureConvertedProc :: [AnnVar] -> AnnFn -> ILExpr -> ILProcDef
closureConvertedProc liftedProcVars f newbody =
    ILProcDef (fnTypeRange (annFnType f))
              (annFnIdent f) liftedProcVars
              (annFnRange f) FastCC newbody

-- For example, if we have something like
--      let y = blah in ( (\x -> x + y) foobar )
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \y x -> x + y
--      let y = blah in p(y, foobar)
lambdaLift :: Context -> AnnFn -> [AnnVar] -> ILM ILProcDef
lambdaLift ctx f freeVars =
    let liftedProcVars = freeVars ++ annFnVars f in
    let extctx =  prependContextBindings ctx (bindingsForVars liftedProcVars) in
    -- Ensure the free vars in the body are bound in the ctx...
     do newbody <- closureConvert extctx (annFnBody f)
        ilmPutProc (closureConvertedProc liftedProcVars f newbody)
    where
        bindingsForVars vars = [TermVarBinding (identPrefix i) v
                               | v@(AnnVar t i) <- vars]

procType proc =
    let retty = ilProcReturnType proc in
    let argtys = TupleTypeAST (map avarType (ilProcVars proc)) in
    let cc = ilProcCallConv proc in
    if  cc == FastCC
        then FnTypeAST argtys retty cc (Just [])
        else FnTypeAST argtys retty cc  Nothing

contextVar :: String -> Context -> String -> AnnVar
contextVar dbg ctx s =
    case termVarLookup s (contextBindings ctx) of
            Just v -> v
            Nothing -> error $ "ILExpr: " ++ dbg ++ " free var not in context: " ++ s ++ "\n" ++ showctx (contextBindings ctx)
    where showctx bindings =
            show $ map (\(TermVarBinding nm v) -> nm ++ "/" ++ (show $ avarIdent v)) bindings

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
nestedLets :: [ILExpr] -> ([AnnVar] -> ILExpr) -> ILM ILExpr
-- | The fresh variables will be accumulated and passed to a
-- | continuation which generates a LetVal expr using the variables.
nestedLets exprs g = nestedLets' exprs [] g

nestedLets' :: [ILExpr] -> [AnnVar] -> ([AnnVar] -> ILExpr) -> ILM ILExpr
nestedLets' []     vars k = return $ k (reverse vars)
nestedLets' (e:es) vars k =
    case e of
      -- No point in doing  let var1 = var2 in e...
      (ILVar v) -> nestedLets' es (v:vars) k
      otherwise -> do
        x        <- ilmFresh ".x"
        innerlet <- nestedLets' es ((AnnVar (typeIL e) x):vars) k
        return $ buildLet x e innerlet

-- This works because (A) we never type check ILExprs,
-- and (B) the LLVM codegen doesn't check the type field in this case.
bogusEnvType = PtrTypeAST (TupleTypeAST [])

makeEnvPassingExplicit :: AnnExpr -> Map Ident (AnnFn, Ident) -> AnnExpr
makeEnvPassingExplicit expr fnAndEnvForClosure =
    q expr where
    fq (AnnFn ty id vars body clovars rng) = (AnnFn ty id vars (q body) clovars rng)
    q e = case e of
            AnnBool b         -> e
            AnnCompiles c msg -> e
            AnnInt t i        -> e
            E_AnnVar v        -> e -- We don't alter standalone references to closures
            AnnIf t a b c    -> AnnIf      t (q a) (q b) (q c)
            AnnUntil t a b   -> AnnUntil   t (q a) (q b)
            AnnLetVar id a b -> AnnLetVar id (q a) (q b)
            AnnLetFuns ids fns e  -> AnnLetFuns ids (map fq fns) (q e)
            AnnAlloc a     -> AnnAlloc   (q a)
            AnnDeref t a   -> AnnDeref t (q a)
            AnnStore t a b -> AnnStore t (q a) (q b)
            AnnSubscript t a b    -> AnnSubscript t (q a) (q b)
            AnnTuple es           -> AnnTuple (map q es)
            AnnCase t e bs        -> AnnCase t (q e) [(p, q e) | (p, e) <- bs]
            E_AnnTyApp t e argty  -> E_AnnTyApp t (q e) argty
            E_AnnFn f             -> E_AnnFn (fq f)
            AnnCall r t (E_AnnVar v) es
                | Map.member (avarIdent v) fnAndEnvForClosure ->
                    let (f, envid) = fnAndEnvForClosure Map.! (avarIdent v) in
                    let fnvar = E_AnnVar (AnnVar (annFnType f) (annFnIdent f)) in
                    -- We don't know the env type here, since we don't
                    -- pre-collect the set of closed-over envs from other procs.
                    let env = E_AnnVar (AnnVar bogusEnvType envid) in
                    (AnnCall r t fnvar (env:(map q es)))
            AnnCall r t b es -> AnnCall r t (q b) (map q es)


excluding :: Ord a => [a] -> Set a -> [a]
excluding bs zs =  Set.toList $ Set.difference (Set.fromList bs) zs

type InfoMap = Map Ident (AnnFn, Ident)

closureOfAnnFn :: Context -> [(Ident, AnnFn)] -> InfoMap
                           -> (Ident, AnnFn) -> ILM (ILClosure, ILProcDef)
closureOfAnnFn ctx allIdsFns infoMap (self_id, fn) = do
    let allIdNames = map (\(id, _) -> identPrefix id) allIdsFns
    let envName  =     (identPrefix.snd) (infoMap Map.! self_id)
    let funNames = map (identPrefix.annFnIdent.fst) (Map.elems infoMap)
    globalVars <- gets ilmGlobals
    {- Given   letfun f = { ... f() .... }
               andfun g = { ... f() .... }
       neither f nor g should close over f itself, or any global vars.
    -}
    let transformedFn = makeEnvPassingExplicit (E_AnnFn fn) infoMap
    let freeNames = freeVars transformedFn `excluding`
                       (Set.union (Set.fromList $ envName : funNames ++ allIdNames) globalVars)
    let capturedVars = map (\n -> contextVar "closureOfAnnFn" ctx n) freeNames
    newproc <- closureConvertAnnFn transformedFn infoMap freeNames
    return $ trace ("capturedVars:" ++ show capturedVars ++ "\n\nallIdsFns: " ++ show allIdsFns) $
        (ILClosure (ilProcIdent newproc) capturedVars , newproc)
  where
    closureConvertAnnFn :: AnnExpr -> InfoMap -> [String] -> ILM ILProcDef
    closureConvertAnnFn (E_AnnFn f) info freeNames = do
        let envName = snd (info Map.! self_id)
        let uniqFreeVars = map (contextVar "closureConvertAnnFn" ctx) freeNames
        let envTypes = map avarType uniqFreeVars
        let envVar   = AnnVar (PtrTypeAST (TupleTypeAST envTypes)) envName
        -- If the body has x and y free, the closure converted body should be
        -- let x = env[0] in
        -- let y = env[1] in body
        -- TODO switch to case env of (x, y, ...) -> body end
        let withVarsFromEnv vars i = case vars of
                [] -> do closureConvert ctx (annFnBody f)
                (v:vs) -> do innerlet <- withVarsFromEnv vs (i + 1)
                             return $ (ILLetVal (avarIdent v)
                                                (ILSubscript (avarType v) envVar (litInt32 i))
                                                innerlet)
        newbody <- withVarsFromEnv uniqFreeVars 0
        ilmPutProc (closureConvertedProc (envVar:(annFnVars f)) f newbody)
    closureConvertAnnFn _ info freeNames = error "closureConvertAnnFn called on non-fn"

    litInt32 :: Int -> ILExpr
    litInt32 i = ILInt (NamedTypeAST "i32") $ getLiteralInt 32 i

typeIL :: ILExpr -> TypeAST
typeIL (ILBool _)          = fosBoolType
typeIL (ILInt t _)         = t
typeIL (ILTuple vs)        = TupleTypeAST [typeIL $ ILVar v | v <- vs]
typeIL (ILClosures n b e)  = typeIL e
typeIL (ILLetVal x b e)    = typeIL e
typeIL (ILCall t id expr)  = t
typeIL (ILIf t a b c)      = t
typeIL (ILUntil t a b)     = t
typeIL (ILAlloc v)         = RefType (typeIL $ ILVar v)
typeIL (ILDeref t _)       = t
typeIL (ILStore t _ _)     = t
typeIL (ILSubscript t _ _) = t
typeIL (ILCase t _ _ _)    = t
typeIL (ILVar (AnnVar t i)) = t
typeIL (ILTyApp overallType tm tyArgs) = overallType

instance Structured ILExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            ILBool         b    -> out $ "ILBool      " ++ (show b)
            ILCall    t b a     -> out $ "ILCall      " ++ " :: " ++ show t
            ILClosures ns cs e  -> out $ "ILClosures  " ++ show (map showClosurePair (zip ns cs))
            ILLetVal   x b e    -> out $ "ILLetVal    " ++ (show x) ++ " :: " ++ (show $ typeIL b) ++ " = ... in ... "
            ILIf      t  a b c  -> out $ "ILIf        " ++ " :: " ++ show t
            ILUntil   t  a b    -> out $ "ILUntil     " ++ " :: " ++ show t
            ILInt ty int        -> out $ "ILInt       " ++ (litIntText int) ++ " :: " ++ show ty
            ILAlloc v           -> out $ "ILAlloc     "
            ILDeref t a         -> out $ "ILDeref     "
            ILStore t a b       -> out $ "ILStore     "
            ILCase t _ _ _      -> out $ "ILCase      "
            ILSubscript  t a b  -> out $ "ILSubscript " ++ " :: " ++ show t
            ILTuple     es      -> out $ "ILTuple     (size " ++ (show $ length es) ++ ")"
            ILVar (AnnVar t i)  -> out $ "ILVar       " ++ show i ++ " :: " ++ show t
            ILTyApp t e argty   -> out $ "ILTyApp     [" ++ show argty ++ "] :: " ++ show t
        where
            showClosurePair :: (Ident, ILClosure) -> String
            showClosurePair (name, clo) = (show name) ++ " bound to " ++ (show clo)

    childrenOf e =
        case e of
            ILBool b                -> []
            ILInt t _               -> []
            ILUntil t a b           -> [a, b]
            ILTuple     vs          -> map ILVar vs
            ILCase _ e bs _dt       -> (ILVar e):(map snd bs)
            ILClosures bnds clos e  -> [e]
            ILLetVal x b e          -> [b, e]
            ILCall  t v vs          -> [ILVar v] ++ [ILVar v | v <- vs]
            ILIf    t v b c         -> [ILVar v, b, c]
            ILAlloc   v             -> [ILVar v]
            ILDeref t v             -> [ILVar v]
            ILStore t v w           -> [ILVar v, ILVar w]
            ILSubscript t a b       -> [ILVar a, b]
            ILVar (AnnVar t i)      -> []
            ILTyApp t e argty       -> [e]

patternBindings :: (Pattern, TypeAST) -> [ContextBinding]
patternBindings (p, ty) =
  case p of
    P_Bool     rng _ -> []
    P_Int      rng _ -> []
    P_Wildcard rng   -> []
    P_Variable rng id -> [TermVarBinding (identPrefix id) $
                                            AnnVar ty id]
    P_Tuple    rng pats ->
      case ty of
        TupleTypeAST tys ->
          concat $ map patternBindings (zip pats tys)
        otherwise -> (error $ "patternBindings failed on typechecked pattern!"
                                ++ "\np = " ++ show p ++ " ; ty = " ++ show ty)
