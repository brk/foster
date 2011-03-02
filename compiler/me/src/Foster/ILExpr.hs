-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

--import Debug.Trace(trace)
import Control.Monad.State
import Data.Set(Set)
import Data.Set as Set(fromList, toList, difference, insert)

import Foster.Base
import Foster.Context
import Foster.TypeAST
import Foster.ExprAST

data ILClosure = ILClosure { ilClosureProcIdent :: Ident
                           , ilClosureCaptures  :: [AnnVar] } deriving Show

data ILProgram = ILProgram [ILProcDef] -- ILExpr

data ILProcDef = ILProcDef { ilProcProto :: ILPrototype
                           , ilProcBody  :: ILExpr       } deriving Show
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
        | ILSubscript   TypeAST AnnVar ILExpr
        | ILIf          TypeAST AnnVar ILExpr ILExpr
        | ILCall        TypeAST AnnVar [AnnVar]
        | ILTyApp       TypeAST ILExpr TypeAST
        deriving (Show)


data ILPrototype = ILPrototype  { ilProtoReturnType :: TypeAST
                                , ilProtoIdent      :: Ident
                                , ilProtoVars       :: [AnnVar]
                                , ilProtoCallConv   :: String
                                } deriving (Eq, Show)

showProgramStructure :: ILProgram -> Output
showProgramStructure (ILProgram procdefs) =
    concat [showProcStructure p | p <- procdefs]

procVarDesc (AnnVar ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

showProcStructure (ILProcDef proto body) =
    out (show $ ilProtoIdent proto) ++ (out " // ")
        ++ (out $ show $ map procVarDesc (ilProtoVars proto))
        ++ (out " @@@ ") ++ (out $ ilProtoCallConv proto)
        ++ (out "\n") ++  showStructure body
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

closureConvertAndLift :: Context -> (ModuleAST AnnFn) -> ILProgram
closureConvertAndLift ctx m =
    let fns = moduleASTfunctions m in
    -- We lambda lift top level functions, since we know they don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let globalVars = (Set.fromList $ map (\(TermVarBinding s _) -> s) (contextBindings ctx)) in
    let procsILM = forM fns (\fn -> lambdaLift ctx fn []) in
    let newstate = execState procsILM (ILMState 0 globalVars []) in
    ILProgram $ (ilmProcDefs newstate)

prependAnnBinding (id, expr) ctx =
    let annvar = AnnVar (typeAST expr) id in
    prependContextBinding ctx (TermVarBinding (identPrefix id) annvar)


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

            AnnLetVar id a b       -> do let ctx' = prependAnnBinding (id, a) ctx
                                         a' <- closureConvert ctx' a
                                         b' <- closureConvert ctx' b
                                         return $ buildLet id a' b'

            AnnLetFuns ids fns e   -> do -- Make sure the functions can close over each other
                                         let ctx' = foldr prependAnnBinding ctx (zip ids (map E_AnnFn fns))
                                         combined <- mapM (closureOfAnnFn ctx') (zip ids fns)
                                         let (closures, _procdefs) = unzip combined
                                         e' <- g e
                                         return $ ILClosures ids closures e'

            AnnSubscript t a b     -> do [a', b'] <- mapM g [a, b]
                                         nestedLets [a'] (\[va] -> ILSubscript t va b')

            AnnTuple     es        -> do cs <- mapM g es
                                         nestedLets cs (\vs -> ILTuple vs)

            E_AnnTyApp t e argty   -> do e' <- g e
                                         return $ ILTyApp t e' argty

            E_AnnFn annFn          -> do
                clo_id <- ilmFresh "clo"
                (closure, newproc) <- closureOfAnnFn ctx (clo_id, annFn)
                let procty = procType newproc
                return $ (ILClosures [clo_id] [closure] (ILVar (AnnVar procty clo_id)))

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
                                    let procid = (ilProtoIdent (ilProcProto newproc))
                                    let procvar = (AnnVar (procType newproc) procid)
                                    nestedLets cargs (\vars -> ILCall t procvar (freevars ++ vars))
                    (E_AnnTyApp ot (E_AnnVar v) argty) -> do
                                    x <- ilmFresh "appty"
                                    let var = AnnVar ot x
                                    nlets <- nestedLets cargs (\vars -> ILCall t var vars)
                                    return $ buildLet x (ILTyApp ot (ILVar v) argty) nlets
                    _ -> error $ "AnnCall with non-var base of " ++ show b


closureConvertedProto :: [AnnVar] -> AnnPrototype -> ILPrototype
closureConvertedProto freeVars (AnnPrototype rt nm vars) =
                                (ILPrototype rt nm (freeVars++vars) "fastcc")

-- For example, if we have something like
--      let y = blah in ( (\x -> x + y) foobar )
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \y x -> x + y
--      let y = blah in p(y, foobar)
lambdaLift :: Context -> AnnFn -> [AnnVar] -> ILM ILProcDef
lambdaLift ctx f freeVars =
    let newproto = closureConvertedProto freeVars (annFnProto f) in
    let extctx =  prependContextBindings ctx (bindingsForILProto newproto) in
    -- Ensure the free vars in the body are bound in the ctx...
     do newbody <- closureConvert extctx (annFnBody f)
        ilmPutProc (ILProcDef newproto newbody)
    where
        bindingsForILProto p = [TermVarBinding (identPrefix i) v
                               | v@(AnnVar t i) <- (ilProtoVars p)]

procType proc = procTypeFromILProto (ilProcProto proc)

procTypeFromILProto proto =
    let retty = ilProtoReturnType proto in
    let argtys = TupleTypeAST (map avarType (ilProtoVars proto)) in
    if ilProtoCallConv proto == "fastcc"
        then FnTypeAST argtys retty (Just [])
        else FnTypeAST argtys retty Nothing

contextVar :: String -> Context -> String -> AnnVar
contextVar dbg (Context ctx) s =
    case termVarLookup s ctx of
            Just v -> v
            Nothing -> error $ "ILExpr: " ++ dbg ++ " free var not in context: " ++ s ++ "\n" ++ showctx (Context ctx)
    where showctx (Context bindings) =
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


excluding :: Ord a => [a] -> Set a -> [a]
excluding bs zs =  Set.toList $ Set.difference (Set.fromList bs) zs

closureOfAnnFn :: Context -> (Ident, AnnFn) -> ILM (ILClosure, ILProcDef)
closureOfAnnFn ctx (self_id, fn) = do
    globalVars <- gets ilmGlobals
    {- Given   letfun f = fn () { ... f() .... }
               andfun g = fn () { ... f() .... }
       we want g to close over the closure for f, but f itself
       ought to make a direct call to its proc, rather than closing over itself.
       So we exclude f from the list of closed-over variables for f's body,
       as well as excluding any variables which we happen to know are globals.
    -}
    let freeNames = freeVars (E_AnnFn fn) `excluding` (Set.insert (identPrefix self_id)
                                                      (Set.insert (fnNameA fn) globalVars))
    let capturedVars = map (\n -> contextVar "closureOfAnnFn" ctx n) freeNames
    newproc <- closureConvertAnnFn fn freeNames
    return $ (ILClosure (ilProtoIdent $ ilProcProto newproc) capturedVars , newproc)
  where
    closureConvertAnnFn :: AnnFn -> [String] -> ILM ILProcDef
    closureConvertAnnFn f freeNames = do
        envName <- ilmFresh ".env"
        let uniqFreeVars = map (contextVar "closureConvertAnnFn" ctx) freeNames
        let envTypes = map avarType uniqFreeVars
        let envVar   = AnnVar (PtrTypeAST (TupleTypeAST envTypes)) envName
        let newproto = closureConvertedProto [envVar] (annFnProto f)
        -- If the body has x and y free, the closure converted body should be
        -- let x = env[0] in
        -- let y = env[1] in body
        let withVarsFromEnv vars i = case vars of
                [] -> do body <- closureConvert ctx (annFnBody f)
                         let procVar = (AnnVar (procTypeFromILProto newproto) (ilProtoIdent newproto))
                         return $ buildLet self_id (ILTuple [procVar, envVar]) body
                (v:vs) -> do innerlet <- withVarsFromEnv vs (i + 1)
                             return $ (ILLetVal (avarIdent v)
                                                (ILSubscript (avarType v) envVar (litInt32 i))
                                                innerlet)
        newbody <- withVarsFromEnv uniqFreeVars 0
        ilmPutProc (ILProcDef newproto newbody)

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
typeIL (ILSubscript t _ _) = t
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
            ILInt ty int        -> out $ "ILInt       " ++ (litIntText int) ++ " :: " ++ show ty
            ILSubscript  t a b  -> out $ "ILSubscript " ++ " :: " ++ show t
            ILTuple     es      -> out $ "ILTuple     (size " ++ (show $ length es) ++ ")"
            ILVar (AnnVar t i)  -> out $ "ILVar       " ++ show i ++ " :: " ++ show t
            ILTyApp t e argty   -> out $ "ILTyApp     [" ++ show argty ++ "] :: " ++ show t
        where
            showClosurePair :: (Ident, ILClosure) -> String
            showClosurePair (name, clo) = (show name) ++ " capturing " ++ (show clo)

    childrenOf e =
        case e of
            ILBool b                -> []
            ILInt t _               -> []
            ILTuple     vs          -> map ILVar vs
            ILClosures bnds clos e  -> [e]
            ILLetVal x b e          -> [b, e]
            ILCall    t b vs        -> [ILVar b] ++ [ILVar v | v <- vs]
            ILIf      t  v b c      -> [ILVar v, b, c]
            ILSubscript t a b       -> [ILVar a, b]
            ILVar (AnnVar t i)      -> []
            ILTyApp t e argty       -> [e]

