-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL (AIExpr(..), fnOf) where

import Data.Map as Map(lookup)

import Foster.Base
import Foster.Context
import Foster.AnnExpr
import Foster.TypeIL
import Foster.TypeAST(gFosterPrimOpsTable, TypeAST(TupleTypeAST))

import qualified Data.Text as T

-- AnnExprIL defines a copy of AnnExpr, annotated with TypeIL
-- instead of TypeAST. This lets us structurally enforce the
-- restriction that unification variables must be eliminated
-- for type checking to succeed.
-- We also force all functions to be let-bound, not anonymous.

data AIExpr=
        -- Literals
          AIBool       Bool
        | AIInt        TypeIL LiteralInt
        | AITuple      [AIExpr]
        -- Control flow
        | AIIf         TypeIL AIExpr AIExpr AIExpr
        | AIUntil      TypeIL AIExpr AIExpr
        -- Creation of bindings
        | AICase       TypeIL AIExpr [(Pattern, AIExpr)]
        | AILetVar     Ident AIExpr AIExpr
        | AILetFuns    [Ident] [Fn AIExpr TypeIL] AIExpr
        -- Use of bindings
        | E_AIVar      (TypedId TypeIL)
        | E_AIPrim     ILPrim
        | AICall       TypeIL AIExpr [AIExpr]
        -- Mutable ref cells
        | AIAlloc      AIExpr
        | AIDeref      AIExpr
        | AIStore      AIExpr AIExpr
        -- Array operations
        | AIAllocArray TypeIL AIExpr
        | AIArrayRead  TypeIL AIExpr AIExpr
        | AIArrayPoke  TypeIL AIExpr AIExpr AIExpr
        -- Terms indexed by types
        | E_AITyApp { aiTyAppOverallType :: TypeIL
                    , aiTyAppExpr        :: AIExpr
                    , aiTyAppArgTypes    :: TypeIL }
        deriving (Show)

ail :: AnnExpr -> Tc AIExpr
ail ae =
    let q = ail in
    case ae of
        AnnBool _rng b             -> return $ AIBool         b
        AnnCompiles _rng (CompilesResult ooe) -> do
                oox <- tcIntrospect (tcInject q ooe)
                return $ AIBool (isOK oox)
        AnnIf _rng  t  a b c       -> do ti <- ilOf t
                                         [x,y,z] <- mapM q [a,b,c]
                                         return $ AIIf    ti x y z
        AnnUntil _rng t  a b       -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIUntil ti x y
        AnnInt _rng t int          -> do ti <- ilOf t
                                         return $ AIInt ti int
        -- For anonymous function literals
        E_AnnFn annFn       -> do fn_id <- tcFresh "lit_fn"
                                  aiFn <- fnOf annFn
                                  let (TypedId t _) = fnVar aiFn
                                  let fnvar = E_AIVar $ (TypedId t fn_id)
                                  return $ AILetFuns [fn_id] [aiFn] fnvar
        -- For bound function literals
        AnnLetVar _rng id (E_AnnFn annFn) b -> do
                                  aiFn <- fnOf annFn
                                  b' <- q b
                                  return $ AILetFuns [id] [aiFn] b'
        AnnLetVar _rng id  a b     -> do [x,y]   <- mapM q [a,b]
                                         return $ AILetVar id x y
        AnnLetFuns _rng ids fns e  -> do fnsi <- mapM fnOf fns
                                         ei <- q e
                                         return $ AILetFuns ids fnsi ei
        AnnAlloc _rng   a          -> do [x] <- mapM q [a]
                                         return $ AIAlloc x
        AnnDeref _rng _t a         -> do [x] <- mapM q [a]
                                         return $ AIDeref x
        AnnStore _rng   a b        -> do [x,y]   <- mapM q [a,b]
                                         return $ AIStore x y
        AnnArrayRead _rng t a b    -> do ti <- ilOf t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIArrayRead ti x y
        AnnArrayPoke _rng t a b c  -> do ti <- ilOf t
                                         [x,y,z]   <- mapM q [a,b,c]
                                         return $ AIArrayPoke ti x y z
        AnnTuple {}                -> do aies <- mapM q (childrenOf ae)
                                         return $ AITuple aies
        AnnCase _rng t e bs        -> do ti <- ilOf t
                                         ei <- q e
                                         bsi <- mapM (\(p,e) -> do a <- q e
                                                                   return (p, a)) bs
                                         return $ AICase ti ei bsi
        AnnPrimitive _rng v -> tcFails [out $ "Primitives must be called directly!"
                                          ++ "\n\tFound non-call use of " ++ show v]
        AnnCall _range t b (E_AnnTuple _rng args) -> do
            ti <- ilOf t
            argsi <- mapM q args
            case b of
                AnnPrimitive _rng (TypedId pty id) -> do
                   pti <- ilOf pty
                   return $ AICall ti (E_AIPrim $ ilPrimFor pti id) argsi

                E_AnnTyApp _ _ot (AnnPrimitive _rng (TypedId _ (GlobalSymbol gs))) argty
                        | gs == T.pack "allocDArray" -> do
                    let [arraySize] = argsi
                    aty <- ilOf argty
                    return $ AIAllocArray aty arraySize

                E_AnnTyApp _ ot (AnnPrimitive _rng (TypedId vty id)) appty ->
                   let primName = identPrefix id in
                   case (coroPrimFor primName, appty) of
                     (Just coroPrim, TupleTypeAST [argty, retty]) -> do
                       [aty, rty] <- mapM ilOf [argty, retty]
                       return $ AICall ti (E_AIPrim $ ILCoroPrim coroPrim aty rty) argsi
                     _otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       [vti, oti, appti] <- mapM ilOf [vty, ot, appty]
                       let primVar = TypedId vti id
                       let call = AICall ti (E_AIPrim $ ILNamedPrim primVar) argsi
                       let primName = identPrefix id
                       x <- tcFreshT $ "appty_" `prependedTo` primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar primVar) appti) call

                _otherwise -> do bi <- q b
                                 return $ AICall ti bi argsi

        E_AnnVar _rng v -> do vv <- aiVar v
                              return $ E_AIVar vv

        E_AnnTyApp _rng t e argty  -> do ti <- ilOf t
                                         at <- ilOf argty
                                         ae <- q e
                                         return $ E_AITyApp ti ae at

coroPrimFor s | s == T.pack "coro_create" = Just $ CoroCreate
coroPrimFor s | s == T.pack "coro_invoke" = Just $ CoroInvoke
coroPrimFor s | s == T.pack "coro_yield"  = Just $ CoroYield
coroPrimFor _ = Nothing

ilPrimFor ti id =
  case Map.lookup (T.unpack $ identPrefix id) gFosterPrimOpsTable of
        Just (_ty, op) -> op
        Nothing        -> ILNamedPrim (TypedId ti id)

aiVar (TypedId t i) = do ty <- ilOf t
                         return $ TypedId ty i

fnOf :: AnnFn -> Tc (Fn AIExpr TypeIL)
fnOf f = do
    ft <- ilOf (annFnType f)
    fnVars <- mapM aiVar (annFnVars f)
    fnFreeVars <- mapM aiVar (annFnFreeVars f)
    body <- ail (annFnBody f)
    return $ Fn { fnVar   = TypedId ft (annFnIdent f)
                , fnVars  = fnVars
                , fnBody  = body
                , fnRange = (annFnRange f)
                , fnFreeVars = fnFreeVars
                }

