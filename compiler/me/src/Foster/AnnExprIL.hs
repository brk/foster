-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExprIL (AIExpr(..), TypeIL(..), AIVar, boolTypeIL, stringTypeIL,
                         fnOf, collectIntConstraints, ilOf) where

import Foster.Base
import Foster.Kind
import Foster.Context
import Foster.AnnExpr
import Foster.TypeTC
import Foster.Output(OutputOr(..))

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T

import Data.UnionFind.IO(descriptor)
import Control.Monad(when, liftM)

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
        | AICallPrim   SourceRange TypeIL (FosterPrim TypeIL) [AIExpr]
        | AICall       TypeIL AIExpr [AIExpr]
        | AIAppCtor    TypeIL CtorId [AIExpr]
        -- Mutable ref cells
        | AIAlloc      AIExpr AllocMemRegion
        | AIDeref      AIExpr
        | AIStore      AIExpr AIExpr
        -- Array operations
        | AIAllocArray TypeIL AIExpr AllocMemRegion
        | AIArrayRead  TypeIL (ArrayIndex AIExpr)
        | AIArrayPoke  TypeIL (ArrayIndex AIExpr) AIExpr
        | AIArrayLit   TypeIL AIExpr [Either Literal AIExpr]
        -- Terms indexed by types
        | E_AITyApp { aiTyAppOverallType :: TypeIL
                    , aiTyAppExpr        :: AIExpr
                    , aiTyAppArgTypes    :: [TypeIL] }
        -- Others
        | AICompiles   TypeIL AIExpr

instance TypedWith AIExpr TypeIL where
  typeOf ai = case ai of
     AILiteral  t _     -> t
     AITuple  exprs _rng -> TupleTypeIL $ map typeOf exprs
     -- E_AIFn annFn         -> fnType annFn
     AICall {- _rng -} t _ _    -> t
     AICallPrim _ t _ _ -> t
     AIAppCtor {- _rng -} t _ _ -> t
     AICompiles {- _rng -} t _     -> t
     AIKillProcess {- _rng -} t _  -> t
     AIIf {- _rng -} t _ _ _    -> t
     AILetVar {- _rng -} _ _ b  -> typeOf b
     AILetRec {- _rng -} _ _ b  -> typeOf b
     AILetFuns {- _rng -} _ _ e -> typeOf e
     AIAlloc {- _rng -} e _   -> typeOf e
     AIDeref {- _rng -} e     -> unPtr $ typeOf e
     AIStore {- _rng -} e _   -> typeOf e
     AIArrayLit   {- _rng -} t _ _ -> t
     AIArrayRead  {- _rng -} t _   -> t
     AIArrayPoke  {- _rng -} t _ _ -> t
     AIAllocArray {- _rng -} t _ _ -> t
     AICase {- _rng -} t _ _    -> t
     E_AIVar {- _rng -} tid -> tidType tid
     -- AIPrimitive _rng t _ -> t
     E_AITyApp {} -> aiTyAppOverallType ai

unPtr (PtrTypeIL t) = t
unPtr (RefinedTypeIL v e args) = RefinedTypeIL (fmap unPtr v) e args
unPtr _ = error $ "Non-ref-type passed to unPtr in AnnExprIL.hs"

collectIntConstraints :: AnnExpr TypeTC -> Tc ()
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
            MetaTyVarTC m -> do
                    tcUpdateIntConstraint m (litIntMinBits int)
            _ -> do return ()

        _ -> mapM_ collectIntConstraints (childrenOf ae)

ail :: Context ty -> AnnExpr TypeTC -> Tc AIExpr
ail ctx ae =
    let q  = ail  ctx in
    let qt = ilOf ctx in
    let qp = ilOfPat ctx in
    case ae of
        AnnCompiles _rng _ty (CompilesResult ooe) -> do
                oox <- tcIntrospect (tcInject q ooe)
                case oox of
                  OK expr ->
                       return $ AICompiles boolTypeIL expr
                  Errors _ -> do
                       return $ AILiteral  boolTypeIL (LitBool False)

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
                                         return $ AIAllocArray ta x MemRegionGlobalHeap
        -- In order for GC root placement to work properly, all allocations
        -- must be explicit in the IR; primitives cannot perform a GC op
        -- before they use all their args, because if they did, the args
        -- would be stale. Thus we make the array allocation explicit here.
        AnnArrayLit  _rng t exprs  -> do ti <- qt t
                                         ais <- mapRightM q exprs
                                         let isLiteral (Left _) = True
                                             isLiteral _        = False

                                             amr = if all isLiteral exprs then MemRegionGlobalData
                                                                          else MemRegionGlobalHeap
                                             (ArrayTypeIL ati) = ti
                                             arr = AIAllocArray ati (AILiteral i64 litint) amr
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

        AnnCall annot t b args -> do
            ti <- qt t
            argsi <- mapM q args
            case b of
                -- Calls to primitives are OK; other uses of primitives
                -- will be flagged as errors in `ail`.
                AnnPrimitive _rng _ prim -> do
                   prim' <- ilPrim ctx prim
                   return $ AICallPrim (rangeOf annot) ti prim' argsi

                -- Now that we can see type applications,
                -- we can build coroutine primitive nodes.
                E_AnnTyApp _ ot (AnnPrimitive _rng _ prim@(NamedPrim tid)) apptys ->
                   let primName = identPrefix (tidIdent tid) in
                   case (coroPrimFor primName, apptys) of
                     (Just coroPrim, [argty, retty]) -> do
                       [aty, rty] <- mapM qt [argty, retty]
                       return $ AICallPrim (rangeOf annot) ti (CoroPrim coroPrim aty rty) argsi
                     _otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       apptysi <- mapM qt apptys
                       prim' <- ilPrim ctx prim
                       tid' <- aiVar ctx tid
                       oti <- qt ot
                       x <- tcFreshT $ "appty_" `prependedTo` primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar tid') apptysi)
                                          $ AICallPrim (rangeOf annot) ti prim' argsi

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

unUnified :: Unifiable v -> v -> Tc v
unUnified uni defaultValue =
  case uni of
    UniConst x -> return x
    UniVar (_u,v) -> do
        mbx <- tcLift $ descriptor v
        case mbx of
          Just x -> return x
          Nothing -> return defaultValue

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
    PrimIntTC isb -> do
      sanityCheckIntLiteralNotOversized rng isb int

    MetaTyVarTC m -> do
      mty <- readTcMeta m
      case mty of
        Just t -> do ailInt rng int t
        Nothing -> do tcFails [text "Int literal should have had type inferred for it!"]

    RefinedTypeTC v _ _ -> ailInt rng int (tidType v)

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

ilPrim :: Context ty -> FosterPrim TypeTC -> Tc (FosterPrim TypeIL)
ilPrim ctx prim =
  case prim of
    NamedPrim tid     -> do tid' <- aiVar ctx tid
                            return $ NamedPrim tid'
    PrimOp    nm ty   -> do ty' <- ilOf ctx ty
                            return $ PrimOp nm ty'
    PrimIntTrunc i1 i2 ->   return $ PrimIntTrunc i1 i2
    PrimInlineAsm ty s c x -> do ty' <- ilOf ctx ty
                                 return $ PrimInlineAsm ty' s c x
    CoroPrim {} -> error $ "Shouldn't yet have constructed CoroPrim!"

containsUnboxedPolymorphism :: TypeIL -> Bool
containsUnboxedPolymorphism (ForAllIL ktvs rho) =
  any isUnboxedKind ktvs || containsUnboxedPolymorphism rho
    where isUnboxedKind (_, kind) = kind == KindAnySizeType

containsUnboxedPolymorphism ty = any containsUnboxedPolymorphism $ childrenOf ty

tyvarBindersOf (ForAllIL ktvs _) = ktvs
tyvarBindersOf _                 = []

fnOf :: Context ty -> Fn r (AnnExpr TypeTC) TypeTC -> Tc (Fn r AIExpr TypeIL)
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

ilOf :: Context t -> TypeTC -> Tc TypeIL
ilOf ctx typ = do
  let q = ilOf ctx
  case typ of
     TyConAppTC  dtname tys -> do
                                     iltys <- mapM q tys
                                     return $ TyConAppIL dtname iltys
     PrimIntTC  size    -> do return $ PrimIntIL size
     PrimFloat64TC      -> do return $ PrimFloat64IL
     TupleTypeTC  types -> do tys <- mapM q types
                              return $ TupleTypeIL tys
     FnTypeTC  ss t cc cs -> do (y:xs) <- mapM q (t:ss)
                                -- Un-unified placeholders occur for loops,
                                -- where there are no external constraints on
                                -- the loop's calling convention or representation.
                                -- So, give reasonable default values here.
                                cc' <- unUnified cc FastCC
                                cs' <- unUnified cs FT_Func
                                return $ FnTypeIL xs y cc' cs'
     RefinedTypeTC v e __args -> do v' <- aiVar ctx v
                                    e' <- ail ctx e
                                    return $ RefinedTypeIL v' e' __args
     CoroTypeTC  s t     -> do [x,y] <- mapM q [s,t]
                               return $ CoroTypeIL x y
     RefTypeTC  ty       -> do liftM PtrTypeIL (q ty)
     ArrayTypeTC   ty    -> do liftM ArrayTypeIL (q ty)
     ForAllTC  ktvs rho  -> do t <- (ilOf $ extendTyCtx ctx ktvs) rho
                               return $ ForAllIL ktvs t
     TyVarTC  tv@(SkolemTyVar _ _ k) -> return $ TyVarIL tv k
     TyVarTC  tv@(BoundTyVar _) ->
        case Prelude.lookup tv (contextTypeBindings ctx) of
          Nothing -> return $ TyVarIL tv KindAnySizeType -- tcFails [text "Unable to find kind of type variable " <> pretty typ]
          Just k  -> return $ TyVarIL tv k
     MetaTyVarTC m -> do
        mty <- readTcMeta m
        case mty of
          Nothing -> if False -- TODO this is dangerous, can violate type correctness
                      then return $ TupleTypeIL []
                      else tcFails [text $ "Found un-unified unification variable "
                                ++ show (mtvUniq m) ++ "(" ++ mtvDesc m ++ ")!"]
          Just t  -> let t' = shallowStripRefinedTypeTC t in
                     -- TODO: strip refinements deeply
                     if show t == show t'
                       then q t'
                       else error $ "meta ty var : " ++ show t ++ " =====> " ++ show t'

aiVar ctx (TypedId t i) = do ty <- ilOf ctx t
                             return $ TypedId ty i


-----------------------------------------------------------------------

ilOfPatAtom :: Context t -> PatternAtom TypeTC -> Tc (PatternAtom TypeIL)
ilOfPatAtom ctx atom = case atom of
    P_Wildcard  rng ty           -> do ty' <- ilOf ctx ty
                                       return $ P_Wildcard  rng ty'
    P_Variable  rng tid          -> do tid' <- aiVar ctx tid
                                       return $ P_Variable rng tid'
    P_Bool      rng ty bval      -> do ty' <- ilOf ctx ty
                                       return $ P_Bool rng ty' bval
    P_Int       rng ty ival      -> do ty' <- ilOf ctx ty
                                       return $ P_Int  rng ty' ival

ilOfPat :: Context t -> Pattern TypeTC -> Tc (Pattern TypeIL)
ilOfPat ctx pat = case pat of
    P_Atom      atom -> return . P_Atom =<< (ilOfPatAtom ctx atom)
    P_Ctor      rng ty pats ctor -> do pats' <- mapM (ilOfPat ctx) pats
                                       ty' <- ilOf ctx ty
                                       ctor' <- ilOfCtorInfo ctx ctor
                                       return $ P_Ctor rng ty' pats' ctor'
    P_Tuple     rng ty pats      -> do pats' <- mapM (ilOfPat ctx) pats
                                       ty' <- ilOf ctx ty
                                       return $ P_Tuple rng ty' pats'

ilOfCtorInfo :: Context t -> CtorInfo TypeTC -> Tc (CtorInfo TypeIL)
ilOfCtorInfo ctx (CtorInfo id dc) = do
  dc' <- ilOfDataCtor ctx dc
  return $ CtorInfo id dc'

ilOfDataCtor :: Context t -> DataCtor TypeTC -> Tc (DataCtor TypeIL)
ilOfDataCtor ctx (DataCtor nm tyformals tys range) = do
  let extctx = extendTyCtx ctx (map convertTyFormal tyformals)
  tys' <- mapM (ilOf extctx) tys
  return $ DataCtor nm tyformals tys' range




type RhoIL = TypeIL
data TypeIL =
           PrimIntIL       IntSizeBits
         | PrimFloat64IL
         | TyConAppIL      DataTypeName [TypeIL]
         | TupleTypeIL     [TypeIL]
         | FnTypeIL        { fnTypeILDomain :: [TypeIL]
                           , fnTypeILRange  :: TypeIL
                           , fnTypeILCallConv :: CallConv
                           , fnTypeILProcOrFunc :: ProcOrFunc }
         | CoroTypeIL      TypeIL  TypeIL
         | ForAllIL        [(TyVar, Kind)] RhoIL
         | TyVarIL           TyVar  Kind
         | ArrayTypeIL     TypeIL
         | PtrTypeIL       TypeIL
         | RefinedTypeIL   (TypedId TypeIL) AIExpr [Ident]

type AIVar = TypedId TypeIL

boolTypeIL = PrimIntIL I1
stringTypeIL = TyConAppIL "Text" []

fnReturnType f@(FnTypeIL {}) = fnTypeILRange f
fnReturnType (ForAllIL _ f@(FnTypeIL {})) = fnTypeILRange f
fnReturnType other = error $
    "Unexpected non-function type in fnReturnType: " ++ show other

instance Show TypeIL where
    show x = case x of
        TyConAppIL nam types -> "(TyConAppIL " ++ nam
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntIL size       -> "(PrimIntIL " ++ show size ++ ")"
        PrimFloat64IL        -> "(PrimFloat64IL)"
        TupleTypeIL types    -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeIL   s t cc cs -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeIL s t       -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllIL ktvs rho    -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarIL     tv kind  -> show tv ++ ":" ++ show kind
        ArrayTypeIL ty       -> "(Array " ++ show ty ++ ")"
        PtrTypeIL   ty       -> "(Ptr " ++ show ty ++ ")"
        RefinedTypeIL v _ _  -> "(Refined " ++ show (tidType v) ++ ")"

instance Structured TypeIL where
    textOf e _width =
        case e of
            TyConAppIL nam _types -> text $ "TyConAppIL " ++ nam
            PrimIntIL     size    -> text $ "PrimIntIL " ++ show size
            PrimFloat64IL         -> text $ "PrimFloat64IL"
            TupleTypeIL   {}      -> text $ "TupleTypeIL"
            FnTypeIL      {}      -> text $ "FnTypeIL"
            CoroTypeIL    {}      -> text $ "CoroTypeIL"
            ForAllIL ktvs _rho    -> text $ "ForAllIL " ++ show ktvs
            TyVarIL       {}      -> text $ "TyVarIL "
            ArrayTypeIL   {}      -> text $ "ArrayTypeIL"
            PtrTypeIL     {}      -> text $ "PtrTypeIL"
            RefinedTypeIL {}      -> text $ "RefinedTypeIL"

    childrenOf e =
        case e of
            TyConAppIL _nam types  -> types
            PrimIntIL       {}     -> []
            PrimFloat64IL          -> []
            TupleTypeIL     types  -> types
            FnTypeIL  ss t _cc _cs -> ss++[t]
            CoroTypeIL s t         -> [s,t]
            ForAllIL  _ktvs rho    -> [rho]
            TyVarIL        _tv _   -> []
            ArrayTypeIL     ty     -> [ty]
            PtrTypeIL       ty     -> [ty]
            RefinedTypeIL   v  _ _ -> [tidType v]

instance Kinded TypeIL where
  kindOf x = case x of
    PrimIntIL   {}       -> KindAnySizeType
    PrimFloat64IL        -> KindAnySizeType
    TyVarIL   _ kind     -> kind
    TyConAppIL  {}       -> KindPointerSized
    TupleTypeIL {}       -> KindPointerSized
    FnTypeIL    {}       -> KindPointerSized
    CoroTypeIL  {}       -> KindPointerSized
    ForAllIL _ktvs rho   -> kindOf rho
    ArrayTypeIL {}       -> KindPointerSized
    PtrTypeIL   {}       -> KindPointerSized
    RefinedTypeIL v _ _  -> kindOf (tidType v)
