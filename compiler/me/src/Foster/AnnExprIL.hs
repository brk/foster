-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL where

import Foster.Base
import Foster.Context
import Foster.ExprAST
import Foster.TypeIL
import Foster.TypeAST(TypeAST(TupleTypeAST))

{-
  AnnExprIL defines a copy of AnnExpr, annotated
  with TypeIL instead of TypeAST. This lets us
  structurally enforce the restriction that unification
  variables must be eliminated for type checking
  to succeed.
-}

data AIExpr=
          AIBool       Bool
        | AIInt        TypeIL LiteralInt
        | AITuple      [AIExpr]
        | E_AIFn       AIFn
        | AICall       ESourceRange TypeIL AIExpr [AIExpr]
        | AICallPrim   ESourceRange TypeIL ILPrim [AIExpr]
        | AIIf         TypeIL AIExpr AIExpr AIExpr
        | AIUntil      TypeIL AIExpr AIExpr
        | AILetVar     Ident AIExpr AIExpr
        | AILetFuns    [Ident] [AIFn] AIExpr
        | AIAllocArray TypeIL AIExpr
        | AIAlloc      AIExpr
        | AIDeref      TypeIL AIExpr
        | AIStore      TypeIL AIExpr AIExpr
        | AISubscript  TypeIL AIExpr AIExpr
        | E_AIVar       (TypedId TypeIL)
        | E_AITyApp { aiTyAppOverallType :: TypeIL
                    , aiTyAppExpr        :: AIExpr
                    , aiTyAppArgTypes    :: TypeIL }
        | AICase    TypeIL AIExpr [(Pattern, AIExpr)]
        deriving (Show)

data AIFn = AiFn { aiFnType  :: TypeIL
                 , aiFnIdent :: Ident
                 , aiFnVars  :: [TypedId TypeIL]
                 , aiFnBody  :: AIExpr
                 , aiFnRange :: ESourceRange
                 } deriving (Show)

aiFnName f = identPrefix (aiFnIdent f)

ail :: Context TypeIL -> AnnExpr -> Tc AIExpr
ail ctx ae =
    let q = ail ctx in
    case ae of
        AnnBool      b             -> return $ AIBool         b
        AnnCompiles (CompilesResult ooe) -> do
                oox <- tcIntrospect (tcInject ooe q)
                return $ AIBool (isOK oox)
        AnnIf      t  a b c        -> do ti <- ilOf t
                                         [x,y,z] <- mapM q [a,b,c]
                                         return $ AIIf    ti x y z
        AnnUntil   t  a b          -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIUntil ti x y
        AnnInt     t int           -> do ti <- ilOf t
                                         return $ AIInt ti int
        AnnLetVar id  a b          -> do [x,y]   <- mapM q [a,b]
                                         return $ AILetVar id x y
        AnnLetFuns ids fns e       -> do fnsi <- mapM (aiFnOf ctx) fns
                                         ei <- q e
                                         return $ AILetFuns ids fnsi ei
        AnnAlloc        a          -> do [x] <- mapM q [a]
                                         return $ AIAlloc x
        AnnDeref      t a          -> do ti <- ilOf t
                                         [x] <- mapM q [a]
                                         return $ AIDeref     ti x
        AnnStore      t a b        -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIStore     ti x y
        AnnSubscript  t a b        -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AISubscript ti x y
        AnnTuple es                -> do aies <- mapM (ail ctx) es
                                         return $ AITuple aies
        AnnCase t e bs             -> do ti <- ilOf t
                                         ei <- q e
                                         bsi <- mapM (\(p,e) -> do a <- q e
                                                                   return (p, a)) bs
                                         return $ AICase ti ei bsi
        AnnPrimitive v -> tcFails [out $ "Primitives must be called directly!"
                                      ++ "\n\tFound non-call use of " ++ show v]
        AnnCall r t b args -> do
            ti <- ilOf t
            argsi <- mapM q args
            case b of
                AnnPrimitive (TypedId pty id) -> do
                   pti <- ilOf pty
                   return $ AICallPrim r ti (ILNamedPrim (TypedId pti id)) argsi

                E_AnnTyApp ot (AnnPrimitive (TypedId _ (Ident "allocDArray" _))) argty -> do
                    let [arraySize] = argsi
                    aty <- ilOf argty
                    return $ AIAllocArray aty arraySize

                E_AnnTyApp ot (AnnPrimitive (TypedId vty id@(Ident primName _))) appty ->
                   case (coroPrimFor primName, appty) of
                     (Just coroPrim, TupleTypeAST [argty, retty]) -> do
                       [aty, rty] <- mapM ilOf [argty, retty]
                       return $ AICallPrim r ti (ILCoroPrim coroPrim aty rty) argsi
                     otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       [vti, oti, appti] <- mapM ilOf [vty, ot, appty]
                       let primVar = TypedId vti id
                       let call = AICallPrim r ti (ILNamedPrim primVar) argsi
                       let primName = identPrefix id
                       x <- tcFresh $ "appty_" ++ primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar primVar) appti) call
                _ -> do bi <- q b
                        return $ AICall r ti bi argsi

        E_AnnVar (TypedId t v)     -> do ti <- ilOf t
                                         return $ E_AIVar (TypedId ti v)
        E_AnnFn annFn              -> do aif <- aiFnOf ctx annFn
                                         return $ E_AIFn aif
        E_AnnTyApp t e argty       -> do ti <- ilOf t
                                         at <- ilOf argty
                                         ae <- q e
                                         return $ E_AITyApp ti ae at

coroPrimFor "coro_create" = Just $ CoroCreate
coroPrimFor "coro_invoke" = Just $ CoroInvoke
coroPrimFor "coro_yield"  = Just $ CoroYield
coroPrimFor _ = Nothing

aiFnOf :: Context TypeIL -> AnnFn -> Tc AIFn
aiFnOf ctx f = do
 ft <- ilOf (annFnType f)
 fnVars <- mapM (\(TypedId t i) -> do ty <- ilOf t
                                      return $ TypedId ty i) (annFnVars f)
 body <- ail ctx (annFnBody f)
 return $ AiFn { aiFnType  = ft
               , aiFnIdent = annFnIdent f
               , aiFnVars  = fnVars
               , aiFnBody  = body
               , aiFnRange = (annFnRange f)
               }

instance AExpr AIExpr where
    freeIdents e = case e of
        E_AIVar v     -> [tidIdent v]
        AILetVar id a b     -> freeIdents a ++ (freeIdents b `butnot` [id])
        AICase _t e patbnds -> freeIdents e ++ (concatMap patBindingFreeIds patbnds)
        -- Note that all free idents of the bound expr are free in letvar,
        -- but letfuns removes the bound name from that set!
        AILetFuns ids fns e ->
                           concatMap boundvars (zip ids fns) ++ (freeIdents e `butnot` ids) where
                                     boundvars (id, fn) = freeIdents (E_AIFn fn) `butnot` [id]
        E_AIFn f       -> let bodyvars =  freeIdents (aiFnBody f) in
                          let boundvars = map tidIdent (aiFnVars f) in
                          bodyvars `butnot` boundvars
        _               -> concatMap freeIdents (childrenOf e)

instance Expr AIExpr where
    freeVars e = map identPrefix (freeIdents e)

instance Structured AIExpr where
    textOf e width = error "textOf AIExpr not yet defined"
    childrenOf e =
        case e of
            AIBool         b      -> []
            AICall  r t b args    -> b:args
            AICallPrim r t b args ->   args
            AIIf      t  a b c    -> [a, b, c]
            AIUntil   t  a b      -> [a, b]
            AIInt t _             -> []
            AILetVar _ a b        -> [a, b]
            AILetFuns ids fns e   -> (map E_AIFn fns) ++ [e]
            AIAllocArray t a      -> [a]
            AIAlloc        a      -> [a]
            AIDeref      t a      -> [a]
            AIStore      t a b    -> [a, b]
            AISubscript t a b     -> [a, b]
            AITuple     es        -> es
            AICase t e bs         -> e:(map snd bs)
            E_AIVar      v        -> []
            E_AIFn f              -> [aiFnBody f]
            E_AITyApp t a argty   -> [a]

