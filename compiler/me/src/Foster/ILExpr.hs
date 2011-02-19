-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Data.Maybe(fromJust)
import Control.Monad(forM)
import Control.Monad.State
import Debug.Trace(trace)
import Data.Set(Set)
import Data.Set as Set(fromList, toList, difference, insert)

import Foster.Base
import Foster.Context
import Foster.TypeAST
import Foster.ExprAST

data ILClosure = ILClosure { ilClosureIdent :: Ident
                           , ilClosureFlatVars :: [Ident]     } deriving Show

data ILProgram = ILProgram [ILProcDef] -- ILExpr

data ILProcDef = ILProcDef { ilProcProto :: ILPrototype
                           , ilProcBody  :: ILExpr       } deriving Show
data ILExpr =
          ILBool        Bool
        | ILInt         TypeAST LiteralInt
        | ILTuple       [ILExpr]
        -- Procedures may be implicitly recursive,
        -- but we need to put a smidgen of effort into
        -- codegen-ing closures so they can be mutually recursive.
        | ILClosures    TypeAST [Ident] [ILClosure] ILExpr
        | ILLetVal      TypeAST AnnVar ILExpr ILExpr
        | ILVar         AnnVar
        | ILSubscript   { ilSubscriptType :: TypeAST
                        , ilSubscriptBase  :: AnnVar
                        , ilSubscriptIndex :: ILExpr  }
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
    let procs' = forM fns (\fn -> lambdaLift ctx fn []) in
    let newstate = execState procs' (ILMState 0 globalVars []) in
    ILProgram $ (ilmProcDefs newstate)

excluding :: Ord a => [a] -> Set a -> [a]
excluding bs zs =  Set.toList $ Set.difference (Set.fromList bs) zs

closureConvert :: Context -> AnnExpr -> ILM ILExpr
closureConvert ctx expr =
        let g = closureConvert ctx in
        case expr of
            AnnBool         b                    -> return $ ILBool b
            AnnCompiles c msg                    -> return $ ILBool (c == CS_WouldCompile)
            AnnInt t   i                         -> return $ ILInt t i
            E_AnnVar      v                      -> return $ ILVar v

            AnnIf      t  a b c                  -> do x <- ilmFresh ".ife"
                                                       a' <- g a
                                                       b' <- g b
                                                       c' <- g c
                                                       let v = AnnVar (typeIL a') x
                                                       return $ buildLet x a' (ILIf t v b' c')

            AnnSeq      a b                      -> do lhs <- ilmFresh ".seq"
                                                       a' <- g a
                                                       b' <- g b
                                                       return $ buildLet lhs a' b'

            AnnSubscript t a b                   -> do a' <- g a
                                                       b' <- g b
                                                       nestedLets [a'] (\[va] -> ILSubscript t va b')

            AnnTuple     es b                    -> do cs <- sequence $ map g es
                                                       return $ ILTuple cs
            E_AnnTyApp t e argty                 -> do e' <- g e
                                                       return $ ILTyApp t e' argty

            E_AnnFn annFn -> do
                clo <- ilmFresh "clo"
                (ILMState _ globalVars _) <- get
                let freeNames = freeVars expr `excluding` (Set.insert (fnNameA annFn) globalVars)
                -- let env = tuple of free variables
                -- rewrite body, replacing mentions of free variables with lookups in env
                newproc <- closureConvertAnnFn ctx annFn freeNames
                let procty = procType newproc
                return $ (ILClosures procty
                            [clo] [ILClosure (ilProtoIdent $ ilProcProto newproc)
                                                (map (\n -> avarIdent (contextVar ctx n)) freeNames)
                            ] (ILVar (AnnVar procty clo)))
            -- b(a)
            AnnCall  r t b a -> do
                ILTuple cargs <- g a
                case b of
                    (E_AnnVar v) -> do nestedLets cargs (\vars -> (ILCall t v vars))
                    (E_AnnFn f) -> do -- If we're calling a function directly,
                                     -- we know we can perform lambda lifting
                                     -- on it, by adding args for its free variables.
                                    (ILMState _ globalVars _) <- get
                                    let freeNames = (map identPrefix $ freeIdentsA b) `excluding` globalVars
                                    let freevars = map (contextVar ctx) freeNames
                                    newproc <- lambdaLift ctx f freevars
                                    let procid = (ilProtoIdent (ilProcProto newproc))
                                    let procvar = (AnnVar (procType newproc) procid)
                                    nestedLets cargs (\vars -> ILCall t procvar (freevars ++ vars))
                    _ -> error $ "AnnCall with non-var base of " ++ show b


-- For example, if we have something like
--      let y = blah in ( (\x -> x + y) foobar )
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \y x -> x + y
--      let y = blah in p(y, foobar)
lambdaLift :: Context -> AnnFn -> [AnnVar] -> ILM ILProcDef
lambdaLift ctx f freevars =
    let newproto = case (annFnProto f) of
                    (AnnPrototype rt nm vars) ->
                        (ILPrototype rt nm (freevars ++ vars) "fastcc") in
    let extctx =  prependContextBindings ctx (bindingsForILProto newproto) in
    do
        newbody <- closureConvert extctx (annFnBody f)
        ilmPutProc (ILProcDef newproto newbody)

bindingsForILProto p = [TermVarBinding (identPrefix i) v | v@(AnnVar t i) <- (ilProtoVars p)]

uniqifyAll :: [String] -> ILM [Ident]
uniqifyAll ss = sequence $ map ilmFresh ss

procType proc = procTypeFromILProto (ilProcProto proc)

procTypeFromILProto proto =
    let retty = ilProtoReturnType proto in
    let argtys = TupleTypeAST (map avarType (ilProtoVars proto)) in
    if ilProtoCallConv proto == "fastcc"
        then FnTypeAST argtys retty (Just [])
        else FnTypeAST argtys retty Nothing


contextVar (Context ctx) s =
    case termVarLookup s ctx of
            Just v -> v
            Nothing -> error $ "free var not in context: " ++ s

buildLet :: Ident -> ILExpr -> ILExpr -> ILExpr
buildLet ident bound inexpr =
  case bound of
    (ILLetVal t' x' e' c') ->
      -- let i = (let x' = e' in c') in inexpr
      -- ==>
      -- let x' = e' in (let i = c' in inexpr)
      ILLetVal t' x' e' (buildLet ident c' inexpr)
    otherwise ->
      ILLetVal (typeIL inexpr) (AnnVar (typeIL bound) ident) bound inexpr

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
      --
      otherwise -> do
        x        <- ilmFresh ".x"
        let vx = AnnVar (typeIL e) x
        innerlet <- nestedLets' es (vx:vars) k
        return $ buildLet x e innerlet

closureConvertAnnFn :: Context -> AnnFn -> [String] -> ILM ILProcDef
closureConvertAnnFn ctx f freevars = do
    envName <- ilmFresh ".env"
    uniqIdents <- uniqifyAll freevars
    let uniqFreeVars = map ((contextVar ctx).identPrefix) uniqIdents
    let envTypes = map avarType uniqFreeVars
    let envVar = AnnVar (PtrTypeAST (TupleTypeAST envTypes)) envName
    let newproto = case (annFnProto f) of
                    (AnnPrototype rt nm vars) ->
                        (ILPrototype rt nm (envVar:vars) "fastcc")
    let nestedLets vars i = case vars of
            [] -> closureConvert ctx (annFnBody f)
            -- Does this loop need to augment the context?
            (v:vs) -> do { innerlet <- nestedLets vs (i + 1)
                         ; return $ (ILLetVal (typeIL innerlet)
                                             v
                                             (ILSubscript (avarType v)
                                                          envVar
                                                          (litInt32 i))
                                             innerlet)
                        }
    newbody <- nestedLets uniqFreeVars 0
    ilmPutProc (ILProcDef newproto newbody)

litInt32 :: Int -> ILExpr
litInt32 i = ILInt (NamedTypeAST "i32") $ getLiteralInt i

typeIL :: ILExpr -> TypeAST
typeIL (ILBool _)          = fosBoolType
typeIL (ILInt t _)         = t
typeIL (ILTuple es)        = TupleTypeAST [typeIL e | e <- es]
typeIL (ILClosures t n b e) = t
typeIL (ILLetVal t x a b)  = t
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
            ILClosures t n b e  -> out $ "ILClosures  " ++ show n
            ILLetVal t x a b    -> out $ "ILLetVal    " ++ (show $ avarIdent x) ++ " :: " ++ (show $ avarType x) ++ " = ... in ... "
            ILIf      t  a b c  -> out $ "ILIf        " ++ " :: " ++ show t
            ILInt ty int        -> out $ "ILInt       " ++ (litIntText int) ++ " :: " ++ show ty
            ILSubscript  t a b  -> out $ "ILSubscript " ++ " :: " ++ show t
            ILTuple     es      -> out $ "ILTuple     (size " ++ (show $ length es) ++ ")"
            ILVar (AnnVar t i)  -> out $ "ILVar       " ++ show i ++ " :: " ++ show t
            ILTyApp t e argty   -> out $ "ILTyApp     [" ++ show argty ++ "] :: " ++ show t
    childrenOf e =
        case e of
            ILBool         b                    -> []
            ILInt t _                           -> []
            ILTuple     es                      -> es
            ILClosures t bnds clos e            -> [e]
            --ILLetVal t x a i@(ILLetVal _ _ _ _) -> a : childrenOf i
            ILLetVal t x a b                    -> [a, b]
            ILCall    t b vs                    -> [ILVar b] ++ [ILVar v | v <- vs]
            ILIf      t  v b c                  -> [ILVar v, b, c]
            ILSubscript t a b                   -> [ILVar a, b]
            ILVar (AnnVar t i)                  -> []
            ILTyApp t e argty                   -> [e]

