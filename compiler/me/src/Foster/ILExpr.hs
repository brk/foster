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
        | ILClosures    TypeAST [(Ident, ILClosure)] ILExpr
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
    ilmUniq :: Uniq
}

type ILM a = State ILMState a

ilmFresh :: String -> ILM Ident
ilmFresh s = do old <- get
                put (old { ilmUniq = (ilmUniq old) + 1 })
                return (Ident s (ilmUniq old))


closureConvertAndLift :: Context -> (ModuleAST AnnFn) -> ILProgram
closureConvertAndLift ctx m =
    let fns = moduleASTfunctions m in
    -- We lambda lift top level functions, since we know they don't have any "real" free vars.
    -- Lambda lifting wiil closure convert nested functions.
    let globalVars = (Set.fromList $ map (\(TermVarBinding s _) -> s) (contextBindings ctx)) in
    let procs' = forM fns (\fn -> lambdaLift globalVars ctx fn []) in
    let procs = evalState procs' (ILMState 0) in
    ILProgram (concat procs)

excluding :: Ord a => [a] -> Set a -> [a]
excluding bs zs =  Set.toList $ Set.difference (Set.fromList bs) zs

closureConvert :: KnownVars -> Context -> AnnExpr -> ILM (ILExpr, [ILProcDef])
closureConvert globalVars ctx expr =
        let g = closureConvert globalVars ctx in
        case expr of
            AnnBool         b                    -> return $ (ILBool b, [])
            AnnCompiles c msg                    -> return $ (ILBool (c == CS_WouldCompile), [])
            AnnInt t   i                         -> return $ (ILInt t i, [])
            E_AnnVar      v                      -> return $ (ILVar v,   [])

            AnnIf      t  a b c                  -> do x <- ilmFresh ".ife"
                                                       (ca, pa) <- g a
                                                       (cb, pb) <- g b
                                                       (cc, pc) <- g c
                                                       let v = AnnVar (typeIL ca) x
                                                       return $ (buildLet x ca (ILIf t v cb cc) , pa++pb++pc)

            AnnSeq      a b                      -> do lhs <- ilmFresh ".seq"
                                                       (ca, pa) <- g a
                                                       (cb, pb) <- g b
                                                       return $ (buildLet lhs ca cb, pa++pb)

            AnnSubscript t a b                   -> do (ca, pa) <- g a
                                                       (cb, pb) <- g b
                                                       nlets <- nestedLets [ca] (\[va] -> ILSubscript t va cb)
                                                       return (nlets, pa++pb)
            AnnTuple     es b                    -> do gs <- sequence $ map g es
                                                       let (cs, ps) = unzip gs
                                                       return $ (ILTuple cs, concat ps)
            E_AnnTyApp t e argty                 -> do (ce, pe) <- g e
                                                       return $ (ILTyApp t ce argty, pe)

            E_AnnFn annFn -> do
                clo <- ilmFresh "clo"
                let freeNames = freeVars expr `excluding` (Set.insert (fnNameA annFn) globalVars)
                -- let env = tuple of free variables
                -- rewrite body, replacing mentions of free variables with lookups in env
                (newproc:newprocs) <- closureConvertAnnFn globalVars ctx annFn freeNames
                let procty = procType newproc
                return (ILClosures procty [
                                (clo, ILClosure (ilProtoIdent $ ilProcProto newproc)
                                                (map (\n -> avarIdent (contextVar ctx n)) freeNames))
                            ]
                            (ILVar (AnnVar procty clo))
                       , newproc:newprocs)
            -- b(a)
            AnnCall  r t b a -> do
                (ILTuple cargs, pargs)  <- g a
                case b of
                    (E_AnnVar v) -> do --return $ (ILAppClosure (avarIdent v) (ILTuple cargs), pargs)
                                    nlets <- nestedLets cargs (\vars -> (ILCall t v vars))
                                    return $ (nlets, pargs)
                    (E_AnnFn f) -> do -- If we're calling a function directly,
                                     -- we know we can perform lambda lifting
                                     -- on it, by adding args for its free variables.
                                    let freeNames = (map identPrefix $ freeIdentsA b) `excluding` globalVars
                                    let freevars = map (contextVar ctx) freeNames
                                    (newproc:newprocs) <- lambdaLift globalVars ctx f freevars
                                    let procid = (ilProtoIdent (ilProcProto newproc))
                                    let procvar = (AnnVar (procType newproc) procid)
                                    nlets <- nestedLets cargs (\vars -> ILCall t procvar (freevars ++ vars))
                                    return $ (nlets, newproc:(newprocs++pargs))
                    _ -> error $ "AnnCall with non-var base of " ++ show b


-- For example, if we have something like
--      let y = blah in ( (\x -> x + y) foobar )
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \y x -> x + y
--      let y = blah in p(y, foobar)
lambdaLift :: KnownVars -> Context -> AnnFn -> [AnnVar] -> ILM [ILProcDef]
lambdaLift globalVars ctx f freevars =
    let newproto = trace ("lambda lifting " ++ (show $ fnNameA f)) $
                    case (annFnProto f) of
                    (AnnPrototype rt nm vars) ->
                        (ILPrototype rt nm (freevars ++ vars) "fastcc") in
    let extctx =  prependContextBindings ctx (bindingsForILProto newproto) in
    do
        (newbody, newprocs) <- closureConvert globalVars extctx (annFnBody f)
        return $ (ILProcDef newproto newbody):newprocs

uniqifyAll :: [String] -> ILM [Ident]
uniqifyAll ss = sequence $ map ilmFresh ss

litInt32 :: Int -> ILExpr
litInt32 i = ILInt (NamedTypeAST "i32") $ getLiteralInt i

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

bindingsForILProto p = [TermVarBinding (identPrefix i) v | v@(AnnVar t i) <- (ilProtoVars p)]

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

closureConvertAnnFn :: KnownVars -> Context -> AnnFn -> [String] -> ILM [ILProcDef]
closureConvertAnnFn globalVars ctx f freevars = do
    envName <- ilmFresh ".env"
    uniqIdents <- uniqifyAll freevars
    let uniqFreeVars =  trace ("closure converting " ++ (show $ fnNameA f)) $  map ((contextVar ctx).identPrefix) uniqIdents
    let envTypes = map avarType uniqFreeVars
    let envVar = AnnVar (PtrTypeAST (TupleTypeAST envTypes)) envName
    let newproto = case (annFnProto f) of
                    (AnnPrototype rt nm vars) ->
                        (ILPrototype rt nm (envVar:vars) "fastcc")
    let nestedLets vars i = case vars of
            [] -> closureConvert globalVars ctx (annFnBody f)
            -- Does this loop need to augment the context?
            (v:vs) -> do { (innerlet, newprocs) <- nestedLets vs (i + 1)
                        ; return $ ((ILLetVal (typeIL innerlet)
                                             v
                                             (ILSubscript (avarType v)
                                                          envVar
                                                          (litInt32 i))
                                             innerlet)
                                    , newprocs)
                        }
    (newbody, newprocs) <- nestedLets uniqFreeVars 0
    return $ (ILProcDef newproto newbody):newprocs


typeIL :: ILExpr -> TypeAST
typeIL (ILBool _)          = fosBoolType
typeIL (ILInt t _)         = t
typeIL (ILTuple es)        = TupleTypeAST [typeIL e | e <- es]
typeIL (ILClosures t closures expr) = t
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
            ILClosures t bnds e -> out $ "ILClosures  " ++ show (map (\(id,clo) -> id) bnds)
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
            ILClosures t clzs e                 -> [e]
            --ILLetVal t x a i@(ILLetVal _ _ _ _) -> a : childrenOf i
            ILLetVal t x a b                    -> [a, b]
            ILCall    t b vs                    -> [ILVar b] ++ [ILVar v | v <- vs]
            ILIf      t  v b c                  -> [ILVar v, b, c]
            ILSubscript t a b                   -> [ILVar a, b]
            ILVar (AnnVar t i)                  -> []
            ILTyApp t e argty                   -> [e]

