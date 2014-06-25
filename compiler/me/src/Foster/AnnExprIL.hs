-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL (AIExpr(..), fnOf, collectIntConstraints) where

import Foster.Base
import Foster.Kind
import Foster.Context
import Foster.AnnExpr
import Foster.TypeIL
import Foster.TypeAST(TypeAST, TypeAST'(PrimIntAST, MetaTyVar))

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T

import Control.Monad(when)

-- Changes between AnnExpr and AnnExprIL:
-- * Type annotation changes from TypeAST to TypeIL, which
--   primarily means we've eliminated all unification variables.
-- * Per above, we recognize calls to coroutine primitives w/ type parameters.
-- * Lambdas are forced to be let/rec-bound.
-- * __COMPILES__ expressions are translated to the appropriate bool constant.

data AIExpr =
        -- Literals
          AILiteral    TypeIL Literal
        | AITuple      [AIExpr] SourceRange
        | AIKillProcess TypeIL T.Text
        -- Control flow
        | AIIf         TypeIL AIExpr AIExpr AIExpr
        -- Creation of bindings
        | AICase       TypeIL AIExpr [CaseArm Pattern AIExpr TypeIL]
        | AILetVar     Ident AIExpr AIExpr
        | AILetRec     [Ident] [AIExpr] AIExpr
        | AILetFuns    [Ident] [Fn () AIExpr TypeIL] AIExpr
        -- Use of bindings
        | E_AIVar      (TypedId TypeIL)
        | AICallPrim   TypeIL ILPrim [AIExpr]
        | AICall       TypeIL AIExpr [AIExpr]
        | AIAppCtor    TypeIL CtorId [AIExpr]
        -- Mutable ref cells
        | AIAlloc      AIExpr AllocMemRegion
        | AIDeref      AIExpr
        | AIStore      AIExpr AIExpr
        -- Array operations
        | AIAllocArray TypeIL AIExpr
        | AIArrayRead  TypeIL (ArrayIndex AIExpr)
        | AIArrayPoke  TypeIL (ArrayIndex AIExpr) AIExpr
        | AIArrayLit   TypeIL AIExpr [Either Literal AIExpr]
        -- Terms indexed by types
        | E_AITyApp { aiTyAppOverallType :: TypeIL
                    , aiTyAppExpr        :: AIExpr
                    , aiTyAppArgTypes    :: [TypeIL] }

collectIntConstraints :: AnnExpr TypeAST -> Tc ()
collectIntConstraints ae =
    case ae of
        AnnCompiles _ _ty (CompilesResult ooe) -> do
                _ <- tcIntrospect (tcInject collectIntConstraints ooe)
                return ()
        AnnLiteral _ ty (LitInt int) -> do
          -- We can't directly mutate the meta type variable for int literals,
          -- because of code like       print_i8 ({ 1234 } !)   where the
          -- constraint that the literal fit an i8 cannot be discarded.
          -- So we collect all the constraints in a pre-pass, and then fix up
          -- un-constrained meta ty vars, while leaving constrained ones alone.
          ty' <- shallowZonk ty
          case ty' of
            MetaTyVar m -> do
                    tcUpdateIntConstraint m (litIntMinBits int)
            _ -> do return ()

        _ -> mapM_ collectIntConstraints (childrenOf ae)

ail :: Context ty -> AnnExpr TypeAST -> Tc AIExpr
ail ctx ae =
    let q  = ail  ctx in
    let qt = ilOf ctx in
    let qp = ilOfPat ctx in
    case ae of
        AnnCompiles _rng _ty (CompilesResult ooe) -> do
                oox <- tcIntrospect (tcInject q ooe)
                return $ AILiteral boolTypeIL (LitBool (isOK oox))
        AnnKillProcess _rng t m -> do ti <- qt t
                                      return $ AIKillProcess ti m
        AnnLiteral annot ty (LitInt int) -> do ailInt (rangeOf annot) int ty
                                               ti <- qt ty
                                               return $ AILiteral ti (LitInt int)
        AnnLiteral _rng ty lit -> do ti <- qt ty
                                     return $ AILiteral ti lit
        AnnIf   _rng  t  a b c -> do ti <- qt t
                                     [x,y,z] <- mapM q [a,b,c]
                                     return $ AIIf    ti x y z
        -- For anonymous function literals
        E_AnnFn annFn        -> do fn_id <- tcFresh $ "lit_fn." ++ sourceLineStart (rangeOf annFn) ++ "..."
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
        AnnLetRec _rng ids exprs e -> do (e' : exprs' ) <- mapM q (e:exprs)
                                         return $ AILetRec ids exprs' e'
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
        -- In order for GC root placement to work properly, all allocations
        -- must be explicit in the IR; primitives cannot perform a GC op
        -- before they use all their args, because if they did, the args
        -- would be stale. Thus we make the array allocation explicit here.
        AnnArrayLit  _rng t exprs  -> do ti <- qt t
                                         let (ArrayTypeIL ati) = ti
                                         ais <- mapRightM q exprs
                                         let arr = AIAllocArray ati (AILiteral i64 litint)
                                         return $ AIArrayLit ti arr ais where {
          n = length exprs
        ; i64 = PrimIntIL I64
        ; litint = LitInt (LiteralInt (fromIntegral n) 32 (show n) 10)
        }
        AnnArrayRead _rng t (ArrayIndex a b rng s) -> do
                                         ti <- qt t
                                         [x,y]   <- mapM q [a,b]
                                         return $ AIArrayRead ti (ArrayIndex x y rng s)
        AnnArrayPoke _rng t (ArrayIndex a b rng s) c -> do
                                         ti <- qt t
                                         [x,y,z] <- mapM q [a,b,c]
                                         return $ AIArrayPoke ti (ArrayIndex x y rng s) z
        AnnTuple rng _ exprs       -> do aies <- mapM q exprs
                                         return $ AITuple aies (rangeOf rng)
        AnnCase _rng t e arms      -> do ti <- qt t
                                         ei <- q e
                                         bsi <- mapM (\(CaseArm p e guard bindings rng) -> do
                                                     p' <- qp p
                                                     e' <- q e
                                                     guard' <- liftMaybe q guard
                                                     bindings' <- mapM (aiVar ctx) bindings
                                                     return (CaseArm p' e' guard' bindings' rng)) arms
                                         return $ AICase ti ei bsi

        E_AnnVar     _rng (v,_)   -> do v' <- aiVar ctx v
                                        return $ E_AIVar v'

        AnnPrimitive _rng _ p -> tcFails [string ("Primitives must be called directly!"
                                         ++ "\n\tFound non-call use of ") <> pretty p]

        AnnAppCtor _rng t cid args -> do ti <- qt t
                                         argsi <- mapM q args
                                         return $ AIAppCtor ti cid argsi

        AnnCall _range t b args -> do
            ti <- qt t
            argsi <- mapM q args
            case b of
                -- Calls to primitives are OK; other uses of primitives
                -- will be flagged as errors in `ail`.
                AnnPrimitive _rng _ prim -> do
                   prim' <- ilPrim ctx prim
                   return $ AICallPrim ti prim' argsi

                -- Now that we can see type applications,
                -- we can build coroutine primitive nodes.
                E_AnnTyApp _ ot (AnnPrimitive _rng _ prim@(NamedPrim tid)) apptys ->
                   let primName = identPrefix (tidIdent tid) in
                   case (coroPrimFor primName, apptys) of
                     (Just coroPrim, [argty, retty]) -> do
                       [aty, rty] <- mapM qt [argty, retty]
                       return $ AICallPrim ti (CoroPrim coroPrim aty rty) argsi
                     _otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       apptysi <- mapM qt apptys
                       prim' <- ilPrim ctx prim
                       tid' <- aiVar ctx tid
                       oti <- qt ot
                       x <- tcFreshT $ "appty_" `prependedTo` primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar tid') apptysi)
                                          $ AICallPrim ti prim' argsi

                _else -> do bi <- q b
                            return $ AICall ti bi argsi

        E_AnnTyApp rng t e raw_argtys  -> do
                ti     <- qt t
                argtys <- mapM qt raw_argtys
                ae     <- q e

                origExprType <- qt (typeOf e)
                let ktvs = tyvarBindersOf origExprType
                mapM_ (kindCheckSubsumption (rangeOf rng)) (zip ktvs argtys)

                return $ E_AITyApp ti ae argtys

sanityCheckIntLiteralNotOversized rng isb int =
    sanityCheck (intSizeOf isb >= litIntMinBits int) $
       "Int constraint violated; context-imposed exact size (in bits) was " ++ show (intSizeOf isb)
        ++ "\n                              but the literal intrinsically needs " ++ show (litIntMinBits int)
        ++ highlightFirstLine rng

ailInt rng int ty = do
  -- 1. We need to make sure that the types eventually given to an int
  --    are large enough to hold it.
  -- 2. For ints with an un-unified meta type variable,
  --    such as from silly code like (let x = 0; in () end),
  --    we should update the int's meta type variable
  --    with the smallest type that accomodates the int.
  case ty of
    PrimIntAST isb -> do
      sanityCheckIntLiteralNotOversized rng isb int

    MetaTyVar m -> do
      mty <- readTcMeta m
      case mty of
        Just t -> do ailInt rng int t
        Nothing -> do tcFails [text "Int literal should have had type inferred for it!"]

    _ -> do tcFails [text "Unable to assign integer literal the type" <+> pretty ty
                  ,string (highlightFirstLine rng)]

kindCheckSubsumption :: SourceRange -> ((TyVar, Kind), TypeIL) -> Tc ()
kindCheckSubsumption rng ((tv, kind), ty) = do
  if kindOf ty `subkindOf` kind
    then return ()
    else tcFails [text $ "Kind mismatch:" ++ highlightFirstLine rng
       ++ "Cannot instantiate type variable " ++ show tv ++ " of kind " ++ show kind
       ++ "\nwith type " ++ show ty ++ " of kind " ++ show (kindOf ty)]

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

fnOf :: Context ty -> Fn r (AnnExpr TypeAST) TypeAST -> Tc (Fn r AIExpr TypeIL)
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

