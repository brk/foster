-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.LLExpr where

import Data.Maybe(fromJust)
import Control.Monad(forM)
import Debug.Trace(trace)
import Data.Set(Set)
import Data.Set as Set(fromList, toList, difference, insert)

{-
import Data.Int
import Data.Set as Set(fromList, toList, difference)
import Data.Sequence as Seq

import Data.List(replicate)
import qualified Data.Text as T
-}

import Foster.Base
import Foster.Context
import Foster.TypeAST
import Foster.ExprAST

data LLClosure = LLClosure { llClosureIdent :: Ident
                           , llClosureFlatVars :: [Ident]     } deriving Show

data LLProgram = LLProgram [LLProcDef] -- LLExpr

data LLProcDef = LLProcDef { llProcProto :: LLPrototype
                           , llProcBody  :: LLExpr       } deriving Show
data LLExpr =
          LLBool        Bool
        | LLInt         TypeAST LiteralInt
        | LLTuple       [LLExpr]
        -- Procedures may be implicitly recursive,
        -- but we need to put a smidgen of effort into
        -- codegen-ing closures so they can be mutually recursive.
        | LLClosures    TypeAST [(Ident, LLClosure)] LLExpr
        | LLLetVal      TypeAST AnnVar LLExpr LLExpr
        | LLVar         AnnVar
        | LLSubscript   { llSubscriptType :: TypeAST
                        , llSubscriptBase  :: AnnVar
                        , llSubscriptIndex :: LLExpr  }
        | LLSeq         LLExpr LLExpr
        | LLIf          TypeAST LLExpr LLExpr LLExpr
--        | LLAppDirect   Ident LLExpr
--        | LLAppClosure  Ident LLExpr
        | LLCall        TypeAST AnnVar [AnnVar]
        | LLTyApp       TypeAST LLExpr TypeAST
        deriving (Show)


data LLPrototype = LLPrototype  { llProtoReturnType :: TypeAST
                                , llProtoIdent      :: Ident
                                , llProtoVars       :: [AnnVar]
                                , llProtoCallConv   :: String
                                } deriving (Eq, Show)

instance Expr LLExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            LLBool         b    -> out $ "LLBool      " ++ (show b)
            LLCall    t b a     -> out $ "LLCall      " ++ " :: " ++ show t
            LLClosures t bnds e -> out $ "LLClosures  " ++ show (map (\(id,clo) -> id) bnds)
            LLLetVal t x a b    -> out $ "LLLetVal    " ++ show x ++ " = ... in ... "
            LLIf      t  a b c  -> out $ "LLIf        " ++ " :: " ++ show t
            LLInt ty int        -> out $ "LLInt       " ++ (litIntText int) ++ " :: " ++ show ty
            LLSeq          a b  -> out $ "LLSeq       " ++ " :: " ++ show (typeLL b)
            LLSubscript  t a b  -> out $ "LLSubscript " ++ " :: " ++ show t
            LLTuple     es      -> out $ "LLTuple     (size " ++ (show $ length es) ++ ")"
            LLVar (AnnVar t i)  -> out $ "LLVar       " ++ show i ++ " :: " ++ show t
            LLTyApp t e argty   -> out $ "LLTyApp     [" ++ show argty ++ "] :: " ++ show t
    childrenOf e =
        case e of
            LLBool         b                    -> []
            LLInt t _                           -> []
            LLTuple     es                      -> es
            LLClosures t clzs e                 -> [e]
            LLLetVal t x a b                    -> [a, b]
            LLCall    t b vs                    -> [LLVar b] ++ [LLVar v | v <- vs]
            LLIf      t  a b c                  -> [a, b, c]
            LLSeq      a b                      -> unbuildSeqsLL e
            LLSubscript t a b                   -> [LLVar a, b]
            LLVar (AnnVar t i)                  -> []
            LLTyApp t e argty                   -> [e]
    freeVars e = error "freeVars llexpr not yet done."

showProgramStructure :: LLProgram -> Output
showProgramStructure (LLProgram procdefs) =
    concat [showProcStructure p | p <- procdefs]

procVarDesc (AnnVar ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

showProcStructure (LLProcDef proto body) =
    out (show $ llProtoIdent proto) ++ (out " // ")
        ++ (out $ show $ map procVarDesc (llProtoVars proto))
        ++ (out " @@@ ") ++ (out $ llProtoCallConv proto)
        ++ (out "\n") ++  showStructure body
      ++ out "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    {- annProtoReturnType :: TypeAST
                                    , annProtoIdent      :: Ident
                                    , annProtoVars       :: [AnnVar]
    -}

typeLL :: LLExpr -> TypeAST
typeLL (LLBool _)          = fosBoolType
typeLL (LLInt t _)         = t
typeLL (LLTuple es)        = TupleTypeAST [typeLL e | e <- es]
typeLL (LLClosures t closures expr) = t
typeLL (LLLetVal t x a b)  = t
typeLL (LLCall t id expr)  = t
typeLL (LLIf t a b c)      = t
typeLL (LLSeq a b)         = typeLL b
typeLL (LLSubscript t _ _) = t
typeLL (LLVar (AnnVar t i)) = t
typeLL (LLTyApp overallType tm tyArgs) = overallType

closureConvertAndLift :: Context -> (ModuleAST AnnFn) -> Tc LLProgram
closureConvertAndLift ctx mod = do
    let fns = moduleASTfunctions mod
    -- We lambda lift top level functions, since we know they don't have any "real" free vars.
    -- Lambda lifting will closure convert nested functions.
    let globalVars = (Set.fromList $ map (\(TermVarBinding s _) -> s) (contextBindings ctx))
    procs <- forM fns (\fn -> lambdaLift globalVars ctx fn [])

    return $ LLProgram (concat procs)

type KnownVars = Set String

excluding :: Ord a => [a] -> Set a -> [a]
excluding bs zs =  Set.toList $ Set.difference (Set.fromList bs) zs

closureConvert :: KnownVars -> Context -> AnnExpr -> Tc (LLExpr, [LLProcDef])
closureConvert globalVars ctx expr =
        let g = closureConvert globalVars ctx in
        case expr of
            AnnBool         b                    -> return $ (LLBool b, [])
            AnnCompiles   c                      -> return $ (LLBool (c == CS_WouldCompile), [])
            AnnIf      t  a b c                  -> do (ca, pa) <- g a
                                                       (cb, pb) <- g b
                                                       (cc, pc) <- g c
                                                       return $ (LLIf t ca cb cc, pa++pb++pc)
            AnnInt t   i                        ->  return $ (LLInt t i, [])
            AnnSeq      a b                      -> do (ca, pa) <- g a
                                                       (cb, pb) <- g b
                                                       return $ (LLSeq ca cb, pa++pb)
            AnnSubscript t a b                   -> do (ca, pa) <- g a
                                                       (cb, pb) <- g b
                                                       nlets <- nestedLets [ca] (\[va] -> LLSubscript t va cb)
                                                       return (nlets, pa++pb)
            AnnTuple     es b                    -> do gs <- sequence $ map g es
                                                       let (cs, ps) = unzip gs
                                                       return $ (LLTuple cs, concat ps)
            E_AnnTyApp t e argty                 -> do (ce, pe) <- g e
                                                       return $ (LLTyApp t ce argty, pe)
            E_AnnVar      v                      -> return $ (LLVar v, [])

            E_AnnFn annFn -> do
                clo <- uniqify "clo"
                let freeNames = freeVars expr `excluding` (Set.insert (fnNameA annFn) globalVars)
                -- let env = tuple of free variables
                -- rewrite body, replacing mentions of free variables with lookups in env
                (newproc:newprocs) <- closureConvertAnnFn globalVars ctx annFn freeNames
                let procty = procType newproc
                return (LLClosures procty [
                                (clo, LLClosure (llProtoIdent $ llProcProto newproc)
                                                (map (\n -> avarIdent (contextVar ctx n)) freeNames))
                            ]
                            (LLVar (AnnVar procty clo))
                       , newproc:newprocs)
            -- b(a)
            AnnCall  r t b a -> do
                (LLTuple cargs, pargs)  <- g a
                case b of
                    (E_AnnVar v) -> do --return $ (LLAppClosure (avarIdent v) (LLTuple cargs), pargs)
                                    nlets <- nestedLets cargs (\vars -> (LLCall t v vars))
                                    return $ (nlets, pargs)
                    (E_AnnFn f) -> do -- If we're calling a function directly,
                                     -- we know we can perform lambda lifting
                                     -- on it, by adding args for its free variables.
                                    let freeNames = (map identPrefix $ freeIdentsA b) `excluding` globalVars
                                    let freevars = map (contextVar ctx) freeNames
                                    (newproc:newprocs) <- lambdaLift globalVars ctx f freevars
                                    let procid = (llProtoIdent (llProcProto newproc))
                                    let procvar = (AnnVar (procType newproc) procid)
                                    nlets <- nestedLets cargs (\vars -> LLCall t procvar (freevars ++ vars))
                                    return $ (nlets, newproc:(newprocs++pargs))
                    _ -> error $ "AnnCall with non-var base of " ++ show b


-- For example, if we have something like
--      let y = blah in ( (\x -> x + y) foobar )
-- then, because the lambda is directly called,
-- we can rewrite the lambda to a closed proc:
--      letproc p = \y x -> x + y
--      let y = blah in p(y, foobar)
lambdaLift :: KnownVars -> Context -> AnnFn -> [AnnVar] -> Tc [LLProcDef]
lambdaLift globalVars ctx f freevars =
    let newproto = trace ("lambda lifting " ++ (show $ fnNameA f)) $
                    case (annFnProto f) of
                    (AnnPrototype rt nm vars) ->
                        (LLPrototype rt nm (freevars ++ vars) "fastcc") in
    let extctx =  prependContextBindings ctx (bindingsForLLProto newproto) in
    do
        (newbody, newprocs) <- closureConvert globalVars extctx (annFnBody f)
        return $ (LLProcDef newproto newbody):newprocs


uniqify :: String -> Tc Ident
uniqify s = do
    u <- newTcUniq
    return (Ident s u)

uniqifyAll :: [String] -> Tc [Ident]
uniqifyAll ss = sequence $ map uniqify ss

litInt32 :: Int -> LLExpr
litInt32 i = LLInt (NamedTypeAST "i32") $ LiteralInt 32 (show i) (show i) 10

procType proc = procTypeFromLLProto (llProcProto proc)

procTypeFromLLProto proto =
    let retty = llProtoReturnType proto in
    let argtys = TupleTypeAST (map avarType (llProtoVars proto)) in
    if llProtoCallConv proto == "fastcc"
        then FnTypeAST argtys retty (Just [])
        else FnTypeAST argtys retty Nothing


contextVar (Context ctx) s =
    case termVarLookup s ctx of
            Just v -> v
            Nothing -> error $ "free var not in context: " ++ s

bindingsForLLProto p = [TermVarBinding (identPrefix i) v | v@(AnnVar t i) <- (llProtoVars p)]

-- | If we have a call like    base(foo, bar, blah)
-- | we want to transform it so that the args are all variables:
-- | let x1 = foo in
-- |  let x2 = bar in
-- |   let x3 = blah in
-- |     base(x1,x2,x3)
nestedLets :: [LLExpr] -> ([AnnVar] -> LLExpr) -> Tc LLExpr
nestedLets exprs g = nestedLets' exprs [] g

nestedLets' :: [LLExpr] -> [AnnVar] -> ([AnnVar] -> LLExpr) -> Tc LLExpr
nestedLets' []     vars g = return $ g (reverse vars)
nestedLets' (e:es) vars g =
    case e of
      -- No point in doing  let var1 = var2 in e...
      (LLVar v) -> nestedLets' es (v:vars) g
      --
      otherwise -> do
        x        <- uniqify ".x"
        let vx = AnnVar (typeLL e) x
        innerlet <- nestedLets' es (vx:vars) g
        return $ (LLLetVal (typeLL innerlet)
                  vx e innerlet)

closureConvertAnnFn :: KnownVars -> Context -> AnnFn -> [String] -> Tc [LLProcDef]
closureConvertAnnFn globalVars ctx f freevars = do
    envName <- uniqify ".env"
    uniqIdents <- uniqifyAll freevars
    let uniqFreeVars =  trace ("closure converting " ++ (show $ fnNameA f)) $  map ((contextVar ctx).identPrefix) uniqIdents
    let envTypes = map avarType uniqFreeVars
    let envVar = AnnVar (PtrTypeAST (TupleTypeAST envTypes)) envName
    let newproto = case (annFnProto f) of
                    (AnnPrototype rt nm vars) ->
                        (LLPrototype rt nm (envVar:vars) "fastcc")
    let nestedLets vars i = case vars of
            [] -> closureConvert globalVars ctx (annFnBody f)
            -- Does this loop need to augment the context?
            (v:vs) -> do { (innerlet, newprocs) <- nestedLets vs (i + 1)
                        ; return $ ((LLLetVal (typeLL innerlet)
                                             v
                                             (LLSubscript (avarType v)
                                                          envVar
                                                          (litInt32 i))
                                             innerlet)
                                    , newprocs)
                        }
    (newbody, newprocs) <- nestedLets uniqFreeVars 0
    return $ (LLProcDef newproto newbody):newprocs


unbuildSeqsLL :: LLExpr -> [LLExpr]
unbuildSeqsLL (LLSeq a b) = a : unbuildSeqsLL b
unbuildSeqsLL expr = [expr]
