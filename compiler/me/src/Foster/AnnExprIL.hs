-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL (AIExpr(..), fnOf) where

import Data.Map as Map(lookup)

import Foster.Base
import Foster.Kind
import Foster.Context
import Foster.AnnExpr
import Foster.TypeIL
import Foster.TypeAST(gFosterPrimOpsTable, TypeAST(TupleTypeAST))
import Foster.Output(out)

import qualified Data.Text as T

import Control.Monad(when)

-- AnnExprIL defines a copy of AnnExpr, annotated with TypeIL
-- instead of TypeAST. This lets us structurally enforce the
-- restriction that unification variables must be eliminated
-- for type checking to succeed.
-- We also force all functions to be let-bound, not anonymous.

data AIExpr=
        -- Literals
          AIBool       Bool
        | AIString     T.Text
        | AIInt        TypeIL LiteralInt
        | AITuple      [AIExpr]
        -- Control flow
        | AIIf         TypeIL AIExpr AIExpr AIExpr
        | AIUntil      TypeIL AIExpr AIExpr
        -- Creation of bindings
        | AICase       TypeIL AIExpr [PatternBinding AIExpr TypeIL]
        | AILetVar     Ident AIExpr AIExpr
        | AILetFuns    [Ident] [Fn AIExpr TypeIL] AIExpr
        -- Use of bindings
        | E_AIVar      (TypedId TypeIL)
        | E_AIPrim     ILPrim
        | AICall       TypeIL AIExpr [AIExpr]
        -- Mutable ref cells
        | AIAlloc      AIExpr AllocMemRegion
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

ail :: Context ty -> AnnExpr TypeAST -> Tc AIExpr
ail ctx ae =
    let q  = ail  ctx in
    let qt = ilOf ctx in
    let qp = ilOfPat ctx in
    case ae of
        AnnCompiles _rng (CompilesResult ooe) -> do
                oox <- tcIntrospect (tcInject q ooe)
                return $ AIBool (isOK oox)
        AnnBool   _rng b       -> do return $ AIBool b
        AnnString _rng s       -> do return $ AIString s
        AnnInt    _rng t int   -> do ti <- qt t
                                     return $ AIInt ti int
        AnnIf   _rng  t  a b c -> do ti <- qt t
                                     [x,y,z] <- mapM q [a,b,c]
                                     return $ AIIf    ti x y z
        AnnUntil _rng t  a b   -> do ti <- qt t
                                     [x,y]   <- mapM q [a,b]
                                     return $ AIUntil ti x y
        -- For anonymous function literals
        E_AnnFn annFn        -> do fn_id <- tcFresh "lit_fn"
                                   aiFn <- fnOf ctx annFn
                                   let (TypedId t _) = fnVar aiFn
                                   let fnvar = E_AIVar $ (TypedId t fn_id)
                                   return $ AILetFuns [fn_id] [aiFn] fnvar
        -- For bound function literals
        AnnLetVar _rng id (E_AnnFn annFn) b -> do
                                  aiFn <- fnOf ctx annFn
                                  b' <- q b
                                  return $ AILetFuns [id] [aiFn] b'
        AnnLetVar _rng id  a b     -> do [x,y]   <- mapM q [a,b]
                                         return $ AILetVar id x y
        AnnLetFuns _rng ids fns e  -> do fnsi <- mapM (fnOf ctx) fns
                                         ei <- q e
                                         return $ AILetFuns ids fnsi ei
        AnnAlloc _rng   a          -> do [x] <- mapM q [a]
                                         return $ AIAlloc x MemRegionGlobalHeap
        AnnDeref _rng _t a         -> do [x] <- mapM q [a]
                                         return $ AIDeref x
        AnnStore _rng   a b        -> do [x,y]   <- mapM q [a,b]
                                         return $ AIStore x y
        AnnArrayRead _rng t a b    -> do ti <- qt t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIArrayRead ti x y
        AnnArrayPoke _rng t a b c  -> do ti <- qt t
                                         [x,y,z]   <- mapM q [a,b,c]
                                         return $ AIArrayPoke ti x y z
        AnnTuple {}                -> do aies <- mapM q (childrenOf ae)
                                         return $ AITuple aies
        AnnCase _rng t e bs        -> do ti <- qt t
                                         ei <- q e
                                         bsi <- mapM (\((p, vs),e) -> do
                                                     p' <- qp p
                                                     e' <- q e
                                                     vs' <- mapM (aiVar ctx) vs
                                                     return ((p', vs'), e')) bs
                                         return $ AICase ti ei bsi
        AnnPrimitive _rng v -> tcFails [out $ "Primitives must be called directly!"
                                          ++ "\n\tFound non-call use of " ++ show v]
        AnnCall _range t b (E_AnnTuple _rng args) -> do
            ti <- qt t
            argsi <- mapM q args
            case b of
                AnnPrimitive _rng (TypedId pty id) -> do
                   pti <- qt pty
                   return $ AICall ti (E_AIPrim $ ilPrimFor pti id) argsi

                E_AnnTyApp _ _ot (AnnPrimitive _rng (TypedId _ (GlobalSymbol gs))) argty
                        | gs == T.pack "allocDArray" -> do
                    let [arraySize] = argsi
                    aty <- qt argty
                    return $ AIAllocArray aty arraySize

                E_AnnTyApp _ ot (AnnPrimitive _rng (TypedId vty id)) appty ->
                   let primName = identPrefix id in
                   case (coroPrimFor primName, appty) of
                     (Just coroPrim, TupleTypeAST [argty, retty]) -> do
                       [aty, rty] <- mapM qt [argty, retty]
                       return $ AICall ti (E_AIPrim $ CoroPrim coroPrim aty rty) argsi
                     _otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       [vti, oti, appti] <- mapM qt [vty, ot, appty]
                       let primVar = TypedId vti id
                       call <- return $ AICall ti (E_AIPrim $ NamedPrim primVar) argsi
                       let primName = identPrefix id
                       x <- tcFreshT $ "appty_" `prependedTo` primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar primVar) appti) call

                _otherwise -> do bi <- q b
                                 return $ AICall ti bi argsi

        E_AnnVar _rng v -> do vv <- aiVar ctx v
                              return $ E_AIVar vv

        E_AnnTyApp rng t e argty  -> do
                ti <- qt t
                at <- qt argty
                ae <- q e

                origExprType <- qt (typeAST e)
                let ktvs = tyvarBindersOf origExprType
                mapM_ (kindCheckSubsumption rng) (zip ktvs (listize at))

                return $ E_AITyApp ti ae at

listize (TupleTypeIL tys) = tys
listize ty                = [ty]

kindCheckSubsumption :: SourceRange -> ((TyVar, Kind), TypeIL) -> Tc ()
kindCheckSubsumption rng ((tv, kind), ty) = do
  if kindOfTypeIL ty `subkindOf` kind
    then return ()
    else tcFails [out $ "Kind mismatch:" ++ highlightFirstLine rng
       ++ "Cannot instantiate type variable " ++ show tv ++ " of kind " ++ show kind
       ++ "\nwith type " ++ show ty ++ " of kind " ++ show (kindOfTypeIL ty)]

coroPrimFor s | s == T.pack "coro_create" = Just $ CoroCreate
coroPrimFor s | s == T.pack "coro_invoke" = Just $ CoroInvoke
coroPrimFor s | s == T.pack "coro_yield"  = Just $ CoroYield
coroPrimFor _ = Nothing

ilPrimFor ti id =
  case Map.lookup (T.unpack $ identPrefix id) gFosterPrimOpsTable of
        Just (_ty, op) -> op
        Nothing        -> NamedPrim (TypedId ti id)

containsUnboxedPolymorphism :: TypeIL -> Bool
containsUnboxedPolymorphism (ForAllIL ktvs rho) =
  any isUnboxedKind ktvs || containsUnboxedPolymorphism rho
    where isUnboxedKind (_, kind) = kind == KindAnySizeType

containsUnboxedPolymorphism ty = any containsUnboxedPolymorphism $ childrenOf ty

tyvarBindersOf (ForAllIL ktvs _) = ktvs
tyvarBindersOf _                 = []

fnOf :: Context ty -> Fn (AnnExpr TypeAST) TypeAST -> Tc (Fn AIExpr TypeIL)
fnOf ctx f = do
    var <- aiVar ctx (fnVar f)
    let ft = tidType var
    -- Ensure that the types resulting from function calls don't make
    -- dubious claims of supporting unboxed polymorphism.
    when (containsUnboxedPolymorphism (fnReturnType ft)) $
       tcFails [out $ "Returning an unboxed-polymorphic value from "
                   ++ show (fnIdent f) ++ "? Inconceivable!"
               ,out $ "Try using boxed polymorphism instead."]

    let extctx = extendTyCtx ctx (tyvarBindersOf ft)
    vars     <- mapM (aiVar extctx) (fnVars f)
    freeVars <- mapM (aiVar extctx) (fnFreeVars f)
    body     <- ail extctx (fnBody f)
    return $ Fn { fnVar   = var
                , fnVars  = vars
                , fnBody  = body
                , fnRange = fnRange f
                , fnFreeVars = freeVars
                }

