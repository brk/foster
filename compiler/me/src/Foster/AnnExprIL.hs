-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL (AIExpr(..), fnOf) where

import Foster.Base
import Foster.Kind
import Foster.Context
import Foster.AnnExpr
import Foster.TypeIL
import Foster.TypeAST(TypeAST)

import Text.PrettyPrint.ANSI.Leijen
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
        | AIFloat      TypeIL LiteralFloat
        | AITuple      [AIExpr] SourceRange
        | AIKillProcess TypeIL T.Text
        -- Control flow
        | AIIf         TypeIL AIExpr AIExpr AIExpr
        | AIUntil      TypeIL AIExpr AIExpr SourceRange
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
        | AIArrayRead  TypeIL (ArrayIndex AIExpr)
        | AIArrayPoke  TypeIL (ArrayIndex AIExpr) AIExpr
        -- Terms indexed by types
        | E_AITyApp { aiTyAppOverallType :: TypeIL
                    , aiTyAppExpr        :: AIExpr
                    , aiTyAppArgTypes    :: [TypeIL] }

ail :: Context ty -> AnnExpr TypeAST -> Tc AIExpr
ail ctx ae =
    let q  = ail  ctx in
    let qt = ilOf ctx in
    let qp = ilOfPat ctx in
    case ae of
        AnnCompiles _rng _ty (CompilesResult ooe) -> do
                oox <- tcIntrospect (tcInject q ooe)
                return $ AIBool (isOK oox)
        AnnKillProcess _rng t m -> do ti <- qt t
                                      return $ AIKillProcess ti m
        AnnBool   _rng _ b     -> do return $ AIBool b
        AnnString _rng _ s     -> do return $ AIString s
        AnnInt    _rng t int   -> do ti <- qt t
                                     return $ AIInt ti int
        AnnFloat _rng t flt    -> do ti <- qt t
                                     return $ AIFloat ti flt
        AnnIf   _rng  t  a b c -> do ti <- qt t
                                     [x,y,z] <- mapM q [a,b,c]
                                     return $ AIIf    ti x y z
        AnnUntil rng  t  a b   -> do ti <- qt t
                                     [x,y]   <- mapM q [a,b]
                                     return $ AIUntil ti x y (annotRange rng)
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
        AnnAlloc _rng _t a rgn     -> do [x] <- mapM q [a]
                                         return $ AIAlloc x rgn
        AnnDeref _rng _t a         -> do [x] <- mapM q [a]
                                         return $ AIDeref x
        AnnStore _rng _t a b       -> do [x,y]   <- mapM q [a,b]
                                         return $ AIStore x y
        AnnAllocArray _rng _ e aty -> do ta <- qt aty
                                         x <- q e
                                         return $ AIAllocArray ta x
        AnnArrayRead _rng t (ArrayIndex a b rng s) -> do
                                         ti <- qt t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIArrayRead ti (ArrayIndex x y rng s)
        AnnArrayPoke _rng t (ArrayIndex a b rng s) c -> do
                                         ti <- qt t
                                         [x,y,z]   <- mapM q [a,b,c]
                                         return $ AIArrayPoke ti (ArrayIndex x y rng s) z
        AnnTuple rng _ exprs       -> do aies <- mapM q exprs
                                         return $ AITuple aies (annotRange rng)
        AnnCase _rng t e bs        -> do ti <- qt t
                                         ei <- q e
                                         bsi <- mapM (\((p, vs),e) -> do
                                                     p' <- qp p
                                                     e' <- q e
                                                     vs' <- mapM (aiVar ctx) vs
                                                     return ((p', vs'), e')) bs
                                         return $ AICase ti ei bsi

        E_AnnVar _rng v -> aiVar ctx v >>= return . E_AIVar

        AnnPrimitive _rng _ p -> tcFails [string ("Primitives must be called directly!"
                                         ++ "\n\tFound non-call use of ") <> pretty p]
        AnnCall _range t b args -> do
            ti <- qt t
            argsi <- mapM q args
            case b of
                -- Calls to primitives are OK; other uses of primitives
                -- will be flagged as errors in `ail`.
                AnnPrimitive _rng _ prim -> do
                   prim' <- ilPrim ctx prim
                   return $ AICall ti (E_AIPrim prim') argsi

                -- Now that we can see type applications,
                -- we can build coroutine primitive nodes.
                E_AnnTyApp _ ot (AnnPrimitive _rng _ prim@(NamedPrim tid)) apptys ->
                   let primName = identPrefix (tidIdent tid) in
                   case (coroPrimFor primName, apptys) of
                     (Just coroPrim, [argty, retty]) -> do
                       [aty, rty] <- mapM qt [argty, retty]
                       return $ AICall ti (E_AIPrim $ CoroPrim coroPrim aty rty) argsi
                     _otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       apptysi <- mapM qt apptys
                       prim' <- ilPrim ctx prim
                       tid' <- aiVar ctx tid
                       oti <- qt ot
                       x <- tcFreshT $ "appty_" `prependedTo` primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar tid') apptysi)
                                          $ AICall ti (E_AIPrim prim') argsi

                _else -> do bi <- q b
                            return $ AICall ti bi argsi

        E_AnnTyApp rng t e raw_argtys  -> do
                ti     <- qt t
                argtys <- mapM qt raw_argtys
                ae     <- q e

                origExprType <- qt (typeOf e)
                let ktvs = tyvarBindersOf origExprType
                mapM_ (kindCheckSubsumption (annotRange rng)) (zip ktvs argtys)

                return $ E_AITyApp ti ae argtys

kindCheckSubsumption :: SourceRange -> ((TyVar, Kind), TypeIL) -> Tc ()
kindCheckSubsumption rng ((tv, kind), ty) = do
  if kindOfTypeIL ty `subkindOf` kind
    then return ()
    else tcFails [text $ "Kind mismatch:" ++ highlightFirstLine rng
       ++ "Cannot instantiate type variable " ++ show tv ++ " of kind " ++ show kind
       ++ "\nwith type " ++ show ty ++ " of kind " ++ show (kindOfTypeIL ty)]

coroPrimFor s | s == T.pack "coro_create" = Just $ CoroCreate
coroPrimFor s | s == T.pack "coro_invoke" = Just $ CoroInvoke
coroPrimFor s | s == T.pack "coro_yield"  = Just $ CoroYield
coroPrimFor _ = Nothing

ilPrim :: Context ty -> FosterPrim TypeAST -> Tc (FosterPrim TypeIL)
ilPrim ctx prim =
  case prim of
    NamedPrim tid     -> do tid' <- aiVar ctx tid
                            return $ NamedPrim tid'
    PrimOp    nm ty   -> do ty' <- ilOf ctx ty
                            return $ PrimOp nm ty'
    PrimIntTrunc i1 i2 ->   return $ PrimIntTrunc i1 i2
    CoroPrim {} -> error $ "Shouldn't yet have constructed CoroPrim!"

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
       tcFails [text $ "Returning an unboxed-polymorphic value from "
                    ++ show (fnIdent f) ++ "? Inconceivable!"
               ,text $ "Try using boxed polymorphism instead."]

    let extctx = extendTyCtx ctx (tyvarBindersOf ft)
    vars     <- mapM (aiVar extctx) (fnVars f)
    body     <- ail extctx (fnBody f)
    return $ Fn { fnVar   = var
                , fnVars  = vars
                , fnBody  = body
                , fnIsRec = fnIsRec f
                , fnAnnot = fnAnnot f
                }

