{-# LANGUAGE StandaloneDeriving, BangPatterns, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNExpr (kNormalizeModule, KNExpr, KNMono, FnMono,
                      KNExpr'(..), TailQ(..), typeKN, kNormalize,
                      KNCompilesResult(..),
                      knLoopHeaders, knSinkBlocks, knInline, knSize,
                      renderKN, renderKNM, renderKNF, renderKNFM,
                      handleCoercionsAndConstraints,
                      collectIntConstraints) where

import Prelude hiding ((<$>))

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Map(Map)
import Data.List(foldl' , isPrefixOf, isInfixOf)
import Data.Maybe(maybeToList, isJust)
import Data.Int

import Foster.MonoType
import Foster.Base
import Foster.KNUtil
import Foster.Config
import Foster.Context
import Foster.Output(OutputOr(..))
import Foster.MainCtorHelpers(withDataTypeCtors)
import Foster.Kind
import Foster.TypeTC
import Foster.AnnExpr
import Foster.Infer(parSubstTcTy)

import Text.PrettyPrint.ANSI.Leijen
import Debug.Trace(trace)

import qualified Data.Graph.Inductive.Graph            as Graph
import qualified Data.Graph.Inductive.Query.DFS        as Graph
import qualified Data.Graph.Inductive.PatriciaTree     as Graph
import qualified Data.Graph.Inductive.Query.Dominators as Graph

import Control.Monad.State(gets, liftIO, evalStateT, execStateT, StateT,
                           execState, State,
                           liftM, liftM2, get, put, lift)
import Control.Monad.Except(ExceptT, runExceptT, throwError, catchError)
import Data.IORef(IORef, newIORef, readIORef, writeIORef)

import Data.Maybe (fromMaybe)
import Data.UnionFind.IO(descriptor)

type KN = Tc

knFresh :: String -> KN Ident
--knFresh s = ccFreshId (T.pack s)
knFresh = tcFresh
--knFreshId = tcFreshT

ccFresh s = ccFreshId (T.pack s)

--------------------------------------------------------------------

type KNState = (Context TypeTC, Map String [DataType TypeTC], Map String (DataType TypeIL))
-- convertDT needs st to call tcToIL
-- kNormalCtors uses contextBindings and nullCtorBindings of Context TypeTC
--      but needs st to call tcToIL
-- kNormalize needs DataType TypeIL for lookupCtor, which is called for every
--      constructor application.
-- tcToIL uses DataType TypeTC for dtUnboxedRepr

--------------------------------------------------------------------

kNormalizeModule :: (ModuleIL (AnnExpr TypeTC) TypeTC)
                 -> Context TypeTC ->
                Tc (ModuleIL KNExpr TypeIL)
kNormalizeModule m ctx = do
    let st0 = (ctx, contextDataTypes ctx, error "convertDT wanted a TypeIL...")
    dts'   <- mapM (convertDT st0) (moduleILdataTypes m)
    prims' <- mapM (convertDT st0) (moduleILprimTypes m)
    let allDataTypes = prims' ++ dts'
    let dtypeMap = Map.fromList [(typeFormalName (dataTypeName dt), dt) | dt <- allDataTypes]
    let st = (ctx, contextDataTypes ctx, dtypeMap)
    decls' <- mapM (\(s,t) -> do t' <- tcToIL st t ; return (s, t')) (moduleILdecls m)
    body' <- do { ctors <- sequence $ concatMap (kNormalCtors st) allDataTypes
                ; body  <- kNormalize st (moduleILbody m)
                ; return $ wrapFns ctors body
                }
    return $ ModuleIL body' decls' dts' prims' (moduleILsourceLines m)
      where
        wrapFns :: [FnExprIL] -> KNExpr -> KNExpr
        wrapFns fs e = foldr (\f body -> KNLetFuns [fnIdent f] [f] body) e fs

qVar :: KNState -> TypedId TypeTC -> KN (TypedId TypeIL)
qVar st (TypedId t id) = do
  t' <- tcToIL st t
  return $ TypedId t' id

kNormalizeFn :: KNState -> Fn () (AnnExpr TypeTC) TypeTC -> KN (FnExprIL)
kNormalizeFn st fn = do
    v <- qVar st (fnVar fn)
    vs <- mapM (qVar st) (fnVars fn)
    body <- kNormalize st (fnBody fn)
    checkForUnboxedPolymorphism fn (tidType v)
    return $ Fn v vs body (fnIsRec fn) (fnAnnot fn)

checkForUnboxedPolymorphism fn ft = do
    -- Ensure that the types resulting from function calls don't make
    -- dubious claims of supporting unboxed polymorphism.
    when (containsUnboxedPolymorphism (fnReturnType ft)) $
       tcFails [text $ "Returning an unboxed-polymorphic value from "
                    ++ show (fnIdent fn) ++ "? Inconceivable!"
               ,text $ "Try using boxed polymorphism instead."]

containsUnboxedPolymorphism :: TypeIL -> Bool
containsUnboxedPolymorphism (ForAllIL ktvs rho) =
  any isUnboxedKind ktvs || containsUnboxedPolymorphism rho
    where isUnboxedKind (_, kind) = kind == KindAnySizeType

containsUnboxedPolymorphism ty = any containsUnboxedPolymorphism $ childrenOf ty

fnReturnType f@(FnTypeIL {}) = fnTypeILRange f
fnReturnType (ForAllIL _ f@(FnTypeIL {})) = fnTypeILRange f
fnReturnType other = error $
    "Unexpected non-function type in fnReturnType: " ++ show other
-- ||||||||||||||||||||||| K-Normalization ||||||||||||||||||||||{{{

kNormalize :: KNState -> AnnExpr TypeTC -> KN KNExpr
kNormalize st expr =
  case expr of
      AnnLiteral annot ty (LitInt int) -> do ailInt (rangeOf annot) int ty
                                             ti <- qt ty
                                             return $ KNLiteral ti (LitInt int)
      AnnLiteral _rng ty lit  -> do ty' <- qt ty ; return $ KNLiteral ty' lit
      E_AnnVar   _rng (v,_)   -> do v'  <- qv v  ; return $ KNVar v'
      AnnKillProcess _rng t m -> do t'  <- qt t  ; return $ KNKillProcess t' m

      AnnTuple annot _ kind es -> do nestedLets (map go es) (\vs ->
                                      KNTuple (TupleTypeIL kind (map tidType vs)) vs (rangeOf annot))
      AnnAlloc _rng _t a amr  -> do nestedLets [go a] (\[x] -> KNAlloc (PtrTypeIL $ tidType x) x amr)
      AnnDeref _rng _t   a    -> do nestedLets [go a] (\[x] -> KNDeref (pointedToTypeOfVar x) x)
      AnnStore _rnt _t a b  -> do nestedLets [go a, go b] (\[x,y] -> KNStore unitTypeIL x y)

      E_AnnTyApp  rng t e raw_argtys -> do
        ti     <- qt t
        argtys <- mapM qt raw_argtys

        origExprType <- qt (typeOf e)

        let ktvs = tyvarBindersOf origExprType
        mapM_ (kindCheckSubsumption (rangeOf rng))
              (zip3 ktvs raw_argtys (map kindOf argtys))

        nestedLets [go e] (\[x] -> KNTyApp ti x argtys)

      AnnAllocArray _rng _ a aty mb_amr zi -> do
            t <- qt aty
            let amr = case mb_amr of
                        Just amr -> amr
                        Nothing  -> MemRegionGlobalHeap
            nestedLets [go a] (\[x] -> KNAllocArray (ArrayTypeIL t) x amr zi)

      AnnArrayRead _rng t (ArrayIndex a b rng s) -> do
              checkArrayIndexer b
              t' <- qt t
              nestedLets (map go [a, b])
                               (\[x, y] -> KNArrayRead t' (ArrayIndex x y rng s))
      AnnArrayPoke _rng _t (ArrayIndex a b rng s) c -> do
              checkArrayIndexer b
              nestedLets (map go [a,b,c])
                               (\[x,y,z] -> KNArrayPoke unitTypeIL (ArrayIndex x y rng s) z)

      -- In order for GC root placement to work properly, all allocations
      -- must be explicit in the IR; primitives cannot perform a GC op
      -- before they use all their args, because if they did, the args
      -- would be stale. Thus we make the array allocation explicit here.
      AnnArrayLit _rng t exprs -> do
        ti <- qt t
        let n = length exprs
            i32 = PrimIntTC I32
            litint = LitInt (LiteralInt (fromIntegral n) 32 (show n) 10)
            arr = AnnAllocArray _rng (error "hmm") (AnnLiteral _rng i32 litint) ati (Just amr) NoZeroInit
            (ArrayTypeTC ati) = t
            isLiteral (Left _) = True
            isLiteral _        = False
            amr = if all isLiteral exprs then MemRegionGlobalData
                                         else MemRegionGlobalHeap
        nestedLetsDo [go arr] (\[arr'] -> do
                letsForArrayValues exprs go
                    (\vals' -> return $ KNArrayLit ti arr' vals'))

      -- For anonymous function literals
      E_AnnFn annFn -> do fn_id <- tcFresh $ show (tidIdent (fnVar annFn))
                          knFn <- kNormalizeFn st annFn
                          let t = tidType (fnVar knFn)
                          let fnvar = KNVar (TypedId t fn_id)
                          return $ KNLetFuns [fn_id] [knFn] fnvar

      -- For bound function literals
      AnnLetVar _rng id (E_AnnFn annFn) b -> do
                          knFn <- kNormalizeFn st annFn
                          b' <- go b
                          return $ KNLetFuns [id] [knFn] b'

      AnnLetFuns _rng ids fns a   -> do
                                knFns <- mapM (kNormalizeFn st) fns
                                liftM (KNLetFuns ids knFns) (go a)

      AnnLetVar _rng id a b -> do liftM2 (buildLet id) (go a) (go b)
      AnnLetRec _rng ids exprs e  -> do
                    -- Unlike with LetVal, we can't float out the
                    -- inner bindings, because they're presuambly
                    -- defined in terms of the ids being bound.
                    exprs' <- mapM go exprs
                    e'     <- go e
                    return $ KNLetRec ids exprs' e'
      AnnCase _rng t e arms -> do t' <- qt t
                                  e' <- go e
                                  nestedLetsDo [return e'] (\[v] -> compileCaseArms arms t' v)
      AnnIf _rng t  a b c   -> do t' <- qt t
                                  a' <- go a
                                  [b', c' ] <- mapM go [b, c]
                                  nestedLets [return a'] (\[v] -> KNIf t' v b' c')

      AnnCall annot t b args -> do
            ti <- qt t
            case b of
                -- Calls to primitives are OK; other uses of primitives
                -- will be flagged as errors.
                AnnPrimitive _rng _ prim -> do
                   prim' <- ilPrim prim
                   nestedLets (map go args) (\vars -> KNCallPrim (rangeOf annot) ti prim' vars)

                -- Now that we can see type applications,
                -- we can build coroutine primitive nodes.
                E_AnnTyApp _ _ot (AnnPrimitive _rng _ (NamedPrim tid)) apptys ->
                   let primName = identPrefix (tidIdent tid) in
                   case (coroPrimFor primName, apptys) of
                     (Just CoroCreate, [argty, retty, _fxty]) -> do
                       [aty, rty] <- mapM qt [argty, retty]
                       nestedLets (map go args) (\vars -> KNCallPrim (rangeOf annot) ti (CoroPrim CoroCreate aty rty) vars)

                     (Just coroPrim, (argty:retty:_fxty_or_null)) -> do
                       [aty, rty] <- mapM qt [argty, retty]
                       nestedLets (map go args) (\vars -> KNCallPrim (rangeOf annot) ti (CoroPrim coroPrim aty rty) vars)

                     _otherwise -> do
                       -- v[types](args) ~~>> let <fresh> = v[types] in <fresh>(args)
                       error "tyapp of non-coro primitive..."
                       {-
                       apptysi <- mapM qt apptys
                       prim' <- ilPrim st prim
                       tid' <- aiVar st tid
                       oti <- qt ot
                       x <- tcFreshT $ "appty_" `prependedTo` primName
                       return $ AILetVar x (E_AITyApp oti (E_AIVar tid') apptysi)
                                          $ AICallPrim (rangeOf annot) ti prim' argsi
                                          -}

                _else -> do knCall ti b args

      AnnAppCtor _ t c es -> do let repr = lookupCtorRepr (lookupCtor c)
                                t'  <- qt t
                                nestedLets (map go es) (\vs -> KNAppCtor  t' (c, repr) vs)

      AnnCompiles _rng _ty (CompilesResult ooe) -> do
        oox <- tcIntrospect (tcInject go ooe)
        case oox of
          OK expr  -> do r <- tcLift $ newIORef True
                         return $ KNCompiles (KNCompilesResult r) boolTypeIL expr
          Errors _ -> do return $ KNLiteral boolTypeIL (LitBool False)


      AnnPrimitive annot _ p -> tcFails [text "Primitives must be called directly!"
                                        ,text "\tFound non-call use of " <> pretty p
                                        ,prettySourceRangeInfo (rangeOf annot)
                                        ,highlightFirstLineDoc (rangeOf annot)]

  where
        go = kNormalize st
        qt = tcToIL st
        qv (TypedId t i) = do t' <- qt t ; return (TypedId t' i)

        knCall t (E_AnnVar _ (v,_)) es = do
                           v' <- qv v
                           nestedLets (     map go es) (\    vars  -> KNCall t v' vars)
        knCall t b es = do nestedLets (go b:map go es) (\(vb:vars) -> KNCall t vb vars)

        -- We currently perform the following source-to-source transformation
        -- on the result of a normalized pattern match:
        --  * Guard splitting:
        --      Every arm with a guard is split into its own pattern match.
        --      The body of the arm turns into
        --          if guard then body else continue-matching !
        --      where continue-matching ! is a lambda containing the
        --      translation of the remaining arms.
        compileCaseArms :: [CaseArm Pattern (AnnExpr TypeTC) TypeTC]
                        -> TypeIL
                        -> TypedId TypeIL
                        -> KN KNExpr
        compileCaseArms arms t v = do
          let gtp ::    (CaseArm Pattern (AnnExpr TypeTC) TypeTC)
                  -> KN (CaseArm PatternRepr KNExpr TypeIL)
              gtp (CaseArm p e g b r) = do
                p' <- qp p
                e' <- kNormalize st e
                g' <- liftMaybe (kNormalize st) g
                b' <- mapM qv b
                return (CaseArm p' e' g' b' r)
          arms' <- mapM gtp arms

          let go (arm:arms) | isGuarded arm = go' [arm] arms
              go allArms = uncurry go' (span (not . isGuarded) allArms)
              -- Compile maximal chunks of un-guarded arms

              go' clump arms = do
                  kid <- knFresh "kont"
                  let kty = FnTypeIL [] t FastCC FT_Proc
                  let kontOf body = Fn {
                          fnVar      = TypedId kty (GlobalSymbol (T.pack $ show kid))
                        , fnVars     = []
                        , fnBody     = body
                        , fnIsRec    = ()
                        , fnAnnot    = annotForRange (MissingSourceRange $ "kont")
                        }
                  body <- if null arms
                              then return $ KNKillProcess t (T.pack $ "guarded pattern match failed")
                              else go arms
                  let kont = kontOf body
                  let callkont = KNCall t (TypedId kty kid) []
                  clump' <- case clump of
                              -- Single arm with guard?
                              [CaseArm p e (Just g' ) b r] -> do
                                  e' <- nestedLets [return g'] (\[gv] ->
                                                  KNIf boolTypeIL gv e callkont)
                                  return [CaseArm p e' Nothing b r]
                              -- Otherwise, one or more arms without guards.
                              _ -> return clump
                  let msr   = MissingSourceRange "guardwild"
                  let pwild = PR_Atom $ P_Wildcard msr (tidType v)
                  return $ KNLetFuns [kid] [kont]
                          (KNCase t v (clump' ++ [CaseArm pwild callkont Nothing [] msr]))
          if anyCaseArmIsGuarded arms
            then go arms'
            else return $ KNCase t v arms'

        isGuarded arm = isJust (caseArmGuard arm)

        anyCaseArmIsGuarded [] = False
        anyCaseArmIsGuarded (arm:arms) = isGuarded arm || anyCaseArmIsGuarded arms

        lookupCtor :: CtorId -> DataCtor TypeIL
        lookupCtor cid =
            let (_, _, dtypeMap) = st in
            case Map.lookup (ctorTypeName cid) dtypeMap of
               Just dt -> let
                            [ctor] = filter (\ctor -> dataCtorName ctor == T.pack (ctorCtorName cid))
                                            (dataTypeCtors dt) in
                          ctor
               Nothing -> error $ "lookupCtor failed for " ++ show cid

        lookupCtorRepr :: Show ty => DataCtor ty -> CtorRepr
        lookupCtorRepr ctor = unDataCtorRepr "lookupCtorRepr" ctor

        qpa :: PatternAtom TypeTC -> KN (PatternAtom TypeIL)
        qpa p =
          case p of
            P_Wildcard rng ty -> liftM (P_Wildcard rng) (qt ty)
            P_Variable rng v  -> liftM (P_Variable rng) (qv v)
            P_Bool rng ty b   -> liftM (\t -> P_Bool rng t b)   (qt ty)
            P_Int  rng ty lit -> liftM (\t -> P_Int  rng t lit) (qt ty)

        qp :: Pattern TypeTC -> KN (PatternRepr TypeIL)
        qp p =
          case p of
            P_Atom a            -> liftM PR_Atom (qpa a)
            P_Tuple rng ty pats -> do pats' <- mapM qp pats
                                      ty'   <- qt ty
                                      return $ PR_Tuple rng ty' pats'
            P_Or    rng ty pats -> do pats' <- mapM qp pats
                                      ty'   <- qt ty
                                      return $ PR_Or rng ty' pats'
            P_Ctor  rng ty pats (CtorInfo cid _dc) -> do
                        pats' <- mapM qp pats
                        ty'   <- qt ty
                        let patTys = map typeOf pats'
                        let cinfo' = LLCtorInfo cid (lookupCtorRepr (lookupCtor cid)) patTys
                        return $ PR_Ctor rng ty' pats' cinfo'

        coroPrimFor s | s == T.pack "coro_create" = Just $ CoroCreate
        coroPrimFor s | s == T.pack "coro_invoke" = Just $ CoroInvoke
        coroPrimFor s | s == T.pack "coro_yield"  = Just $ CoroYield
        coroPrimFor _ = Nothing

        ilPrim :: FosterPrim TypeTC -> KN (FosterPrim TypeIL)
        ilPrim prim =
          case prim of
            NamedPrim tid     -> do tid' <- qv tid
                                    return $ NamedPrim tid'
            PrimOp    nm ty   -> do ty' <- qt ty
                                    return $ PrimOp nm ty'
            PrimIntTrunc i1 i2 ->   return $ PrimIntTrunc i1 i2
            PrimInlineAsm ty s c x -> do ty' <- qt ty
                                         return $ PrimInlineAsm ty' s c x
            CoroPrim {} -> error $ "Shouldn't yet have constructed CoroPrim!"

unUnified :: Unifiable v -> Tc (Maybe v)
unUnified uni =
  case uni of
    UniConst x -> return (Just x)
    UniVar (_u,v) -> do
        tcLift $ descriptor v

unUnifiedWithDefault uni d = do unUnified uni >>= return . fromMaybe d

tcToIL :: KNState -> TypeTC -> KN TypeIL
tcToIL st typ = do
  let q = tcToIL st
  case typ of
     TyConTC nm -> return $ TyConIL nm
     TyAppTC (TyConTC "Float64") [] -> return $ TyAppIL (TyConIL "Float64") []
     TyAppTC (TyConTC dtname) tys -> do
         let (_, dtypeMapX, _) = st
         case Map.lookup dtname dtypeMapX of
           Just [dt] -> case dtUnboxedRepr dt of
             Nothing -> do iltys <- mapM q tys
                           return $ TyAppIL (TyConIL dtname) iltys
             Just rr -> do q $ rr tys
           Just dts | length dts > 1
             -> tcFails [text "Multiple definitions for data type" <+> text dtname]
           _ -> tcFails [text "Unable to find data type" <+> text dtname
                        ,text "contextDataTypes ="
                        ,pretty (map fst $ Map.toList dtypeMapX)
                ]
     TyAppTC _ _ -> error $ "tcToIL saw TyApp of non-TyCon"
     PrimIntTC  size    -> do return $ PrimIntIL size
     TupleTypeTC ukind types -> do tys <- mapM q types
                                   kind <- unUnifiedWithDefault ukind KindPointerSized
                                   return $ TupleTypeIL kind tys
     FnTypeTC  ss t _fx cc cs -> do
        (y:xs) <- mapM q (t:ss)
        -- Un-unified placeholders occur for loops,
        -- where there are no external constraints on
        -- the loop's calling convention or representation.
        -- So, give reasonable default values here.
        cc' <- unUnifiedWithDefault cc FastCC
        cs' <- unUnifiedWithDefault cs FT_Func
        return $ FnTypeIL xs y cc' cs'
     RefinedTypeTC v e __args -> do v' <- qVar st v
                                    e' <- kNormalize st e
                                    return $ RefinedTypeIL v' e' __args
     CoroTypeTC  s t _fx -> do [x,y] <- mapM q [s,t]
                               return $ CoroTypeIL x y
     RefTypeTC  ty       -> do liftM PtrTypeIL (q ty)
     ArrayTypeTC   ty    -> do liftM ArrayTypeIL (q ty)
     ForAllTC  ktvs rho  -> do t <- q rho
                               return $ ForAllIL ktvs t
     TyVarTC  tv@(SkolemTyVar _ _ k) _mbk -> return $ TyVarIL tv k
     TyVarTC  tv@(BoundTyVar _ _sr)  uniK -> do
        k <- unUnifiedWithDefault uniK KindAnySizeType
        return $ TyVarIL tv k
     MetaTyVarTC m -> do
        mty <- readTcMeta m
        case mty of
          Nothing -> if mtvIsEffect m
                       then return (TyAppIL (TyConIL "effect.Empty") [])
                       else tcFails [text $ "Found un-unified unification variable "
                                ++ show (mtvUniq m) ++ "(" ++ mtvDesc m ++ ")!"]
          Just t  -> let t' = shallowStripRefinedTypeTC t in
                     -- TODO: strip refinements deeply
                     if show t == show t'
                       then q t'
                       else error $ "meta ty var : " ++ show t ++ " =====> " ++ show t'


-- For datatypes which have been annotated as being unboxed (and are eligible
-- to be so represented), we want to convert from a "data type name reference"
-- to "directly unboxed tuple" representation, since the context which maps
-- names to datatypes will not persist through the rest of the compilation pipeline.
--
dtUnboxedRepr :: DataType TypeTC -> Maybe ([TypeTC] -> TypeTC)
dtUnboxedRepr dt =
  case dataTypeName dt of
    TypeFormal _ _ KindAnySizeType ->
      case dataTypeCtors dt of
        [ctor] -> Just $ \tys ->
                       TupleTypeTC (UniConst KindAnySizeType)
                          (map (substTypeTC tys (dataCtorDTTyF ctor))
                               (dataCtorTypes ctor))
        _ -> Nothing
    TypeFormal _ _ _otherKinds -> Nothing
 where
    substTypeTC :: [TypeTC] -> [TypeFormal] -> TypeTC -> TypeTC
    substTypeTC tys formals = parSubstTcTy mapping
      where mapping = [(BoundTyVar nm rng, ty)
                      | (ty, TypeFormal nm rng _kind) <- zip tys formals]


-- Wrinkle: need to extend the context used for checking ctors!
convertDT :: KNState -> DataType TypeTC -> KN (DataType TypeIL)
convertDT st (DataType dtName tyformals ctors range) = do
  -- f :: TypeTC -> Tc TypeIL
  let f = tcToIL st
  cts <- mapM (convertDataCtor f) ctors

  optrep <- tcShouldUseOptimizedCtorReprs
  let dt = DataType dtName tyformals cts range
  let reprMap = Map.fromList $ optimizedCtorRepresesentations dt
  return $ dt { dataTypeCtors = withDataTypeCtors dt (getCtorRepr reprMap optrep) }
    where
      convertDataCtor f (DataCtor dataCtorName tyformals types repr range) = do
        tys <- mapM f types
        return $ DataCtor dataCtorName tyformals tys repr range

      getCtorRepr :: Map.Map CtorId CtorRepr -> Bool -> CtorId -> DataCtor TypeIL -> Int -> DataCtor TypeIL
      getCtorRepr _ _     _cid dc _n | Just _ <- dataCtorRepr dc = dc
      getCtorRepr _ False _cid dc  n = dc { dataCtorRepr = Just (CR_Default n) }
      getCtorRepr m True   cid dc  n = case Map.lookup cid m of
                                         Just repr -> dc { dataCtorRepr = Just repr }
                                         Nothing   -> dc { dataCtorRepr = Just (CR_Default n) }

      optimizedCtorRepresesentations :: Kinded t => DataType t -> [(CtorId, CtorRepr)]
      optimizedCtorRepresesentations dtype =
        let ctors = withDataTypeCtors dtype (\cid ctor n -> (cid, ctor, n)) in
        case classifyCtors ctors (kindOf $ dataTypeName dtype) of
          SingleCtorWrappingSameBoxityType cid KindAnySizeType ->
            -- The constructor needs no runtime representation, nor casts...
            [(cid, CR_TransparentU)]

          SingleCtorWrappingSameBoxityType cid _ ->
            -- The constructor needs no runtime representation...
            [(cid, CR_Transparent)]

          AtMostOneNonNullaryCtor [] nullaryCids ->
            [(cid, CR_Nullary n) | (cid, n) <- nullaryCids]

          AtMostOneNonNullaryCtor [nnCid] nullaryCids ->
            [(cid, CR_Tagged  n) | (cid, n) <- [nnCid]] ++
            [(cid, CR_Nullary n) | (cid, n) <- nullaryCids]

          AtMostOneNonNullaryCtor _nnCids _nullaryCids ->
            error $ "KNExpr.hs cannot yet handle multiple non-nullary ctors"

          OtherCtorSituation cidns ->
            [(cid, CR_Default n) | (cid, n) <- cidns]

      ctorWrapsOneValueOfKind ctor kind =
        case dataCtorTypes ctor of
          [ty] -> kindOf ty `subkindOf` kind
          _ -> False

      isNullaryCtor :: DataCtor ty -> Bool
      isNullaryCtor ctor = null (dataCtorTypes ctor)

      splitNullaryCtors :: [(CtorId, DataCtor ty, Int)] -> ( [CtorId], [CtorId] )
      splitNullaryCtors ctors =
        ( [cid | (cid, ctor, _) <- ctors, not (isNullaryCtor ctor)]
        , [cid | (cid, ctor, _) <- ctors,      isNullaryCtor ctor ] )

      classifyCtors :: Kinded ty => [(CtorId, DataCtor ty, Int)] -> Kind -> CtorVariety ty
      classifyCtors [(cid, ctor, _)] dtypeKind
                          | ctorWrapsOneValueOfKind ctor dtypeKind
                          = SingleCtorWrappingSameBoxityType cid dtypeKind
      classifyCtors ctors _ =
          case splitNullaryCtors ctors of
            -- The non-nullary ctor gets a small-int of zero (so it has "no tag"),
            -- and the nullary ctors get the remaining values.
            -- The representation can be in the low bits of the pointer.
            ([nonNullaryCtor], nullaryCtors) | length nullaryCtors <= 7 ->
                 AtMostOneNonNullaryCtor  [ (nonNullaryCtor, 0) ] (zip nullaryCtors [1..])

            ([],               nullaryCtors) | length nullaryCtors <= 8 ->
                 AtMostOneNonNullaryCtor  []                      (zip nullaryCtors [0..])

            _ -> OtherCtorSituation [(cid, n) | (cid, _, n) <- ctors]


data CtorVariety ty = SingleCtorWrappingSameBoxityType CtorId Kind
                    | AtMostOneNonNullaryCtor          [(CtorId, Int)] [(CtorId, Int)]
                    | OtherCtorSituation               [(CtorId, Int)]

data ArrayIndexResult = AIR_OK
                      | AIR_Trunc
                      | AIR_ZExt

checkArrayIndexer :: AnnExpr TypeTC -> KN ()
checkArrayIndexer b = do
  -- The actual conversion will be done later on, in the backend.
  -- See the second hunk of patch b0e56b93f614.
  _ <- check (typeOf b)
  return ()

  where check t =
          -- If unconstrained, fix to Int32.
          -- Otherwise, check how it should be converted to Int32/64.
          case t of
            MetaTyVarTC m -> do
              mb_t <- readTcMeta m
              case mb_t of
                Nothing -> do writeTcMeta m (PrimIntTC I32)
                              check         (PrimIntTC I32)
                Just tt -> check tt
            PrimIntTC I1     -> return $ AIR_ZExt
            PrimIntTC I8     -> return $ AIR_ZExt
            PrimIntTC I32    -> return $ AIR_OK
            PrimIntTC I64    -> return $ AIR_Trunc
            PrimIntTC IWd    -> return $ AIR_Trunc
            RefinedTypeTC v _ _ -> check (tidType v)
            _ -> tcFails [text "Array subscript had type"
                         ,pretty t
                         ,text "which was insufficiently integer-y."
                         ,prettyWithLineNumbers (rangeOf b)
                         ]

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
                    ,prettyWithLineNumbers rng]

sanityCheckIntLiteralNotOversized rng isb int =
    sanityCheck (intSizeOf isb >= litIntMinBits int) $
       "Int constraint violated; context-imposed exact size (in bits) was " ++ show (intSizeOf isb)
        ++ "\n                              but the literal intrinsically needs " ++ show (litIntMinBits int)
        ++ highlightFirstLine rng



-- This function runs after typechecking, and before the conversion to AIExpr.
-- The reason is that for code like::
--       a = prim mach-array-literal 0 0;
--       b = prim mach-array-literal True False;
--
--       expect_i1 True;
--       print_i1 b[a[0]];
-- Typechecking will record that a[0] has an int-ish type, but the specific
-- type will remain unconstrained. When converting to AIExpr we'll check that
-- there are no remaining unconstrained types, so we must fix the type between
-- typechecking and creating AIExpr. Thus, this function.
--
-- This has return type Tc (AnnExpr TypeTC) instead of Tc ()
-- because we want to signal failure when we see indexing with a bogus type.
-- In order for __COMPILES__ to work correct, that means we can't get away with
-- a simple traversal routine.
handleCoercionsAndConstraints :: AnnExpr TypeTC -> Tc (AnnExpr TypeTC)
handleCoercionsAndConstraints ae = do
    let q = handleCoercionsAndConstraints
    let qf f = do body' <- q (fnBody f)
                  return $ f { fnBody = body' }
    case ae of
        AnnArrayRead _rng t (ArrayIndex a b rng s) -> do
             checkArrayIndexer b
             [x,y]   <- mapM q [a,b]
             return $ AnnArrayRead _rng t (ArrayIndex x y rng s)
        AnnArrayPoke _rng t (ArrayIndex a b rng s) c -> do
             checkArrayIndexer b
             [x,y,z] <- mapM q [a,b,c]
             return $ AnnArrayPoke _rng t (ArrayIndex x y rng s) z

        AnnCompiles _rng _ty (CompilesResult ooe) -> do
            res <- tcIntrospect (tcInject q ooe)
            return $ AnnCompiles _rng _ty (CompilesResult res)

        AnnKillProcess {} -> return ae
        AnnLiteral     {} -> return ae
        E_AnnVar       {} -> return ae
        AnnPrimitive   {} -> return ae
        AnnIf   _rng  t  a b c -> do [x,y,z] <- mapM q [a,b,c]
                                     return $ AnnIf   _rng  t  x y z
        E_AnnFn annFn        -> do fn' <- qf annFn
                                   return $ E_AnnFn fn'
        AnnLetVar _rng id  a b     -> do [x,y]   <- mapM q [a,b]
                                         return $ AnnLetVar _rng id  x y
        AnnLetRec _rng ids exprs e -> do (e' : exprs' ) <- mapM q (e:exprs)
                                         return $ AnnLetRec _rng ids exprs' e'
        AnnLetFuns _rng ids fns e  -> do fnsi <- mapM qf fns
                                         ei <- q e
                                         return $ AnnLetFuns _rng ids fnsi ei
        AnnAlloc _rng _t a rgn     -> do [x] <- mapM q [a]
                                         return $ AnnAlloc _rng _t x rgn
        AnnDeref _rng _t a         -> do [x] <- mapM q [a]
                                         return $ AnnDeref _rng _t x
        AnnStore _rng _t a b       -> do [x,y]   <- mapM q [a,b]
                                         return $ AnnStore _rng _t  x y
        AnnAllocArray _rng _t e aty mb_amr zi -> do
                                         x <- q e
                                         return $ AnnAllocArray _rng _t x aty mb_amr zi
        AnnArrayLit  _rng t exprs -> do  ais <- mapRightM q exprs
                                         return $ AnnArrayLit  _rng t ais

        AnnTuple rng _t kind exprs -> do aies <- mapM q exprs
                                         return $ AnnTuple rng _t kind aies
        AnnCase _rng t e arms      -> do ei <- q e
                                         bsi <- mapM (\(CaseArm p e guard bindings rng) -> do
                                                     e' <- q e
                                                     guard' <- liftMaybe q guard
                                                     return (CaseArm p e' guard' bindings rng)) arms
                                         return $ AnnCase _rng t ei bsi
        AnnAppCtor _rng t cid args -> do argsi <- mapM q args
                                         return $ AnnAppCtor _rng t cid argsi
        AnnCall annot t b args -> do
            (bi:argsi) <- mapM q (b:args)
            return $ AnnCall annot t bi argsi

        E_AnnTyApp rng t e raw_argtys  -> do
                ae     <- q e
                return $ E_AnnTyApp rng t ae raw_argtys

tyvarBindersOf (ForAllIL ktvs _) = ktvs
tyvarBindersOf _                 = []

kindCheckSubsumption :: SourceRange -> ((TyVar, Kind), TypeTC, Kind) -> Tc ()
kindCheckSubsumption rng ((tv, tvkind), ty, tykind) = do
  if tykind `subkindOf` tvkind
    then return ()
    else tcFails [text $ "Kind mismatch:" ++ highlightFirstLine rng
       ++ "Cannot instantiate type variable " ++ show tv ++ " of kind " ++ show tvkind
       ++ "\nwith type " ++ show ty ++ " of kind " ++ show tykind]


collectIntConstraints :: AnnExpr TypeTC -> Tc ()
collectIntConstraints ae =
    case ae of
        AnnCompiles _ _ty (CompilesResult ooe) -> do
                -- This function should ignore code that failed to compile.
                _ <- tcIntrospect (tcInject collectIntConstraints ooe)
                return ()

        AnnCase _ _ scrut arms -> do
          collectIntConstraints scrut
          let handleArm (CaseArm pat body guard _binds _rng) = do
                applyPatternIntConstraints pat
                collectIntConstraints body
                mapMaybeM collectIntConstraints guard
                return ()
          mapM_ handleArm arms

        AnnLiteral _ ty (LitInt int) -> applyIntLiteralConstraint ty int

        _ -> mapM_ collectIntConstraints (childrenOf ae)

applyPatternIntConstraints pat = do
  case pat of
    P_Atom (P_Int _ ty int) -> applyIntLiteralConstraint ty int
    P_Atom _                -> return ()
    P_Ctor  _ _ pats _ -> mapM_ applyPatternIntConstraints pats
    P_Tuple _ _ pats   -> mapM_ applyPatternIntConstraints pats
    P_Or    _ _ pats   -> mapM_ applyPatternIntConstraints pats

applyIntLiteralConstraint ty int = do
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
-- }}}|||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||| Let-Flattening |||||||||||||||||||||||{{{
-- Because buildLet is applied bottom-to-top, we maintain the invariant
-- that the bound form in the result is never a binder itself.
buildLet :: Ident -> KNExpr' r t -> KNExpr' r t -> KNExpr' r t
buildLet ident bound inexpr =
  case bound of
    -- Convert  let i = (let x = e in c) in inexpr
    -- ==>      let x = e in (let i = c in inexpr)
    KNLetVal x e c ->   KNLetVal x e (buildLet ident c inexpr)

    -- Convert  let f = letfuns g = ... in g in <<f>>
    --     to   letfuns g = ... in let f = g in <<f>>
    KNLetFuns ids fns a -> KNLetFuns ids fns (buildLet ident a inexpr)

    -- Convert  let i = x in i
    --      to  x
    KNVar _ ->
      case inexpr of
        KNVar v | tidIdent v == ident -> bound
        _                             -> KNLetVal ident bound inexpr

    _ -> KNLetVal ident bound inexpr


-- | If we have a call like    base(foo, bar, blah)
-- | we want to transform it so that the args are all variables:
-- | let x1 = foo in
-- |  let x2 = bar in
-- |   let x3 = blah in
-- |     base(x1,x2,x3)
-- | The fresh variables will be accumulated and passed to a
-- | continuation which generates a LetVal expr using the variables.
nestedLetsDo :: [KN KNExpr] -> ([AIVar] -> KN KNExpr) -> KN KNExpr
nestedLetsDo exprActions g = do exprs <- sequence exprActions
                                nestedLets' exprs [] g
  where
    nestedLets' :: [KNExpr] -> [AIVar] -> ([AIVar] -> KN KNExpr) -> KN KNExpr
    nestedLets' []     vars k = k (reverse vars)
    nestedLets' (e:es) vars k =
        case e of
          -- No point in doing  let var1 = var2 in e...
          -- Instead, pass var2 to k instead of var1.
          (KNVar v) -> nestedLets' es (v:vars) k

          -- We also don't particularly want to do something like
          --    let var2 = (letfun var1 = {...} in var1) in e ...
          -- because it would be later flattened out to
          --    let var1 = fn in (let var2 = var1 in e...)
          (KNLetFuns ids fns (KNVar v)) -> do
            innerlet <- nestedLets' es (v:vars) k
            return $ KNLetFuns ids fns innerlet

          _otherwise -> do
            x        <- knFresh (tmpForExpr e)
            let v = TypedId (typeKN e) x
            innerlet <- nestedLets' es (v:vars) k
            return $ buildLet x e innerlet

-- Usually, we can get by with a pure continuation.
-- Note: Haskell's type system is insufficiently expressive here:
--       we can't express the constraint that len [KNExpr] == len [AIVar].
--       As a result, we get many spurious pattern match warnings.
nestedLets :: [KN KNExpr] -> ([AIVar] -> KNExpr) -> KN KNExpr
nestedLets exprActions g = nestedLetsDo exprActions (\vars -> return $ g vars)


letsForArrayValues :: [Either Literal (AnnExpr TypeTC)]
                   -> (AnnExpr TypeTC -> KN KNExpr)
                   -> ([Either Literal (TypedId TypeIL)] -> KN KNExpr)
                                                         -> KN KNExpr
letsForArrayValues vals normalize mkArray = do
                                kvals <- mapRightM normalize vals
                                nestedLets' kvals [] mkArray
  where
    nestedLets' :: [Either Literal KNExpr] -> [Either Literal AIVar] -> ([Either Literal AIVar] -> KN KNExpr) -> KN KNExpr
    nestedLets' []     vars k = k (reverse vars)
    nestedLets' (ei:es) vars k =
        case ei of
          -- No point in doing  let var1 = var2 in e...
          -- Instead, pass var2 to k instead of var1.
          Right (KNVar v) -> nestedLets' es (Right v:vars) k

          -- We also don't particularly want to do something like
          --    let var2 = (letfun var1 = {...} in var1) in e ...
          -- because it would be later flattened out to
          --    let var1 = fn in (let var2 = var1 in e...)
          Right (KNLetFuns ids fns (KNVar v)) -> do
            innerlet <- nestedLets' es (Right v:vars) k
            return $ KNLetFuns ids fns innerlet

          Right e -> do
            x        <- knFresh (tmpForExpr e)
            let v = TypedId (typeKN e) x
            innerlet <- nestedLets' es (Right v:vars) k
            return $ buildLet x e innerlet

          Left lit -> do
            nestedLets' es (Left lit:vars) k

-- Give constants distinct-looking binders from non-constants;
-- this is mostly to aid debugging of failing SMT scripts.
tmpForExpr (KNLiteral {}) = ".const"
tmpForExpr _              = ".x"
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||| Constructor Munging ||||||||||||||||||||{{{
-- Produces a list of (K-normalized) functions, eta-expansions of each ctor.
-- Specifically, given a data type T (A1::K1) ... (An::Kn) with
--   constructor C (T1::KT1) .. (Tn::KTn), we emit a procedure with type
--
-- forall (A1::K1) ... (An::Kn), T1 -> ... -> Tn -> T A1 ... An
--
-- For example, ``type case T2 of $T2C1 Int32``
-- produces a function ``T2C1 :: Int32 -> T2``,
-- while ``type case T3 (a:Boxed) of $T3C1 a``
-- produces T3C1 :: forall b:Boxed, b -> T3 b
--
kNormalCtors :: KNState -> DataType TypeIL -> [KN (FnExprIL)]
kNormalCtors st dtype =
        map (kNormalCtor dtype) (dataTypeCtors dtype)
  where
    kNormalCtor :: DataType TypeIL -> DataCtor TypeIL
                -> KN (FnExprIL)
    kNormalCtor _datatype (DataCtor _cname _tyformals _tys Nothing _range) = do
      error "Cannot wrap a data constructor with no representation information."
    kNormalCtor datatype (DataCtor cname _tyformals tys (Just repr) range) = do
      let dname = dataTypeName datatype
      let arity = Prelude.length tys
      let cid   = CtorId (typeFormalName dname) (T.unpack cname) arity
      let genFreshVarOfType t = do fresh <- knFresh ".autogen"
                                   return $ TypedId t fresh
      vars <- mapM genFreshVarOfType tys
      let ret tid = return
               Fn { fnVar   = tid
                  , fnVars  = vars
                  , fnBody  = KNAppCtor resty (cid, repr) vars
                  , fnIsRec = ()
                  , fnAnnot = annotForRange range
                  } where resty =
                            case tidType tid of
                                 FnTypeIL _ r _ _ -> r
                                 ForAllIL _ (FnTypeIL _ r _ _) -> r
                                 _ -> error $ "KNExpr.hs: kNormalCtor given non-function type!"
      let (ctx, _, _) = st
      case termVarLookup cname (contextBindings ctx) of
        Nothing -> case termVarLookup cname (nullCtorBindings ctx) of
          Nothing -> error $ "Unable to find binder for constructor " ++ show cname
          Just (TypedId ty id, _) -> do
                         ty' <- tcToIL st ty
                         -- This is rather ugly: nullary constructors,
                         -- unlike their non-nullary counterparts, don't have
                         -- function type, so we synthesize a fn type here.
                         ret (TypedId (thunk ty') id)
        Just (TypedId t id, _) -> do t' <- tcToIL st t
                                     ret (TypedId t' id)

    thunk (ForAllIL ktvs rho) = ForAllIL ktvs (thunk rho)
    thunk ty = FnTypeIL [] ty FastCC FT_Proc
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


-- |||||||||||||||||||||||||| Local Block Sinking |||||||||||||||{{{

-- This transformation re-locates functions according to their dominator tree.
--
-- Block sinking is needed for contification to work properly;
-- without it, a contifiable function would get contified into an outer scope,
-- which doesn't work (since functions eventually get lifted to toplevel).
--
-- Performing sinking after monomorphization allows each monomorphization
-- of a given function to be separately sunk.
--
--
-- The block-sinking transformation here is loosely based on the
-- presentation in the paper
--
--      Lambda-Dropping: Transforming Recursive Equations into
--      Programs with Block Structure
--
-- by Olivier Danvy and Ulrik P. Schultz.
--
-- http://www.brics.dk/RS/99/27/BRICS-RS-99-27.pdf

collectFunctions :: Fn r (KNExpr' r t) t -> [(Ident, Ident, Fn r (KNExpr' r t) t)]  -- (parent, binding, child)
collectFunctions knf = go [] (fnBody knf)
  where go xs e = case e of
          KNLiteral       {} -> xs
          KNTuple         {} -> xs
          KNKillProcess   {} -> xs
          KNVar           {} -> xs
          KNCallPrim      {} -> xs
          KNCall          {} -> xs
          KNAppCtor       {} -> xs
          KNAlloc         {} -> xs
          KNDeref         {} -> xs
          KNStore         {} -> xs
          KNAllocArray    {} -> xs
          KNArrayRead     {} -> xs
          KNArrayPoke     {} -> xs
          KNArrayLit      {} -> xs
          KNTyApp         {} -> xs
          KNCompiles _r _t e -> go xs e
          KNInlined _t0 _to _tn _old new -> go xs new
          KNNotInlined _ e -> go xs e
          KNIf            _ _ e1 e2   -> go (go xs e1) e2
          KNLetVal          _ e1 e2   -> go (go xs e1) e2
          KNCase       _ _ arms       -> let es = concatMap caseArmExprs arms in
                                       foldl' go xs es
          KNLetRec     _ es b       -> foldl' go xs (b:es)
          KNLetFuns    ids fns b ->
                 let entries = map (\(id, f) -> (fnIdent knf, id, f)) (zip ids fns) in
                 let ys      = concatMap collectFunctions fns in
                 xs ++ entries ++ go ys b

collectMentions :: Fn r (KNExpr' r t) t -> Set (Ident, Ident) -- (caller, callee)
collectMentions knf = go Set.empty (fnBody knf)
  where cc       = fnIdent knf
        uu xs vs = Set.union xs (Set.fromList [(cc, tidIdent v) | v <- vs])
        vv xs v  = Set.insert (cc, tidIdent v) xs
        go xs e = case e of
          KNLiteral     {} -> xs
          KNKillProcess {} -> xs
          KNAllocArray  {} -> xs -- next few cases can't be fn-valued due to type checking.
          KNArrayRead   {} -> xs
          KNArrayPoke   {} -> xs
          KNDeref       {} -> xs
          KNArrayLit _ _ litsvars -> uu xs [v | Right v <- litsvars]
          KNTuple       _ vs _ -> uu xs vs
          KNAppCtor     _ _ vs -> uu xs vs
          KNCallPrim  _ _ _ vs -> uu xs vs
          KNVar           v    -> vv xs v
          KNAlloc       _ v _  -> vv xs v
          KNTyApp       _ v _  -> vv xs v
          KNStore     _  v1 v2 -> vv (vv xs v1) v2
          KNCall        _ v vs -> vv (uu xs vs) v
          KNIf          _ v e1 e2   -> go (go (vv xs v) e1) e2
          KNLetVal      _   e1 e2   -> go (go xs e1) e2
          KNCase        _ v arms    -> let es = concatMap caseArmExprs arms in
                                       foldl' go (vv xs v) es
          KNLetRec     _ es b ->       foldl' go xs (b:es)
          KNLetFuns    _ fns b -> Set.union xs $ go (Set.unions $ map collectMentions fns) b
          KNCompiles _r _t e             -> go xs e
          KNInlined _t0 _to _tn _old new -> go xs new
          KNNotInlined _x e -> go xs e

rebuildFnWith rebuilder addBindingsFor f =
         let rebuiltBody = rebuildWith rebuilder (fnBody f) in
         f { fnBody = addBindingsFor f rebuiltBody }

rebuildWith rebuilder e = q e
  where
    q x = case x of
      KNVar         {} -> x
      KNLiteral     {} -> x
      KNTuple       {} -> x
      KNKillProcess {} -> x
      KNCallPrim    {} -> x
      KNCall        {} -> x
      KNAppCtor     {} -> x
      KNAlloc       {} -> x
      KNDeref       {} -> x
      KNStore       {} -> x
      KNAllocArray  {} -> x
      KNArrayRead   {} -> x
      KNArrayPoke   {} -> x
      KNArrayLit    {} -> x
      KNTyApp       {} -> x
      KNIf          ty v ethen eelse -> KNIf       ty v (q ethen) (q eelse)
      KNLetVal      id  e1   e2      -> KNLetVal   id   (q e1)    (q e2)
      KNLetRec      ids es   e       -> KNLetRec   ids (map q es) (q e)
      KNCase        ty v arms        -> KNCase     ty v (map (fmapCaseArm id q id) arms)
      KNLetFuns     ids fns e        -> mkLetFuns (rebuilder (zip ids fns)) (q e)
      KNCompiles _r _t e             -> KNCompiles _r _t (q e)
      KNInlined _t0 _to _tn _old new -> KNInlined _t0 _to _tn _old (q new)
      KNNotInlined x e -> KNNotInlined x (q e)

mkLetFuns []       e = e
mkLetFuns bindings e = KNLetFuns ids fns e where (ids, fns) = unzip bindings

mkLetRec []       b = b
mkLetRec bindings b = KNLetRec ids es b where (ids, es) = unzip bindings

mkLetVals []            e = e
mkLetVals ((id,b):rest) e = KNLetVal id b (mkLetVals rest e)

knSinkBlocks :: (Pretty t, Pretty r, Show t, Show r) => ModuleIL (KNExpr' r t) t -> Compiled (ModuleIL (KNExpr' r t) t)
knSinkBlocks m = do
  let rebuilder idsfns = [(id, localBlockSinking fn) | (id, fn) <- idsfns]
  return $ m { moduleILbody = rebuildWith rebuilder (moduleILbody m) }

localBlockSinking :: (Pretty t, Pretty r, Show t, Show r) => Fn r (KNExpr' r t) t -> Fn r (KNExpr' r t) t
localBlockSinking knf =
    let newfn = rebuildFn knf in
    let !nu = show (pretty $ fnBody newfn)
        !ol = show (pretty $ fnBody knf) in
    if nu == ol then
      newfn
      else
        trace ("localBlockSinking turned\n\n" ++ show (showStructure (fnBody knf))
              ++ "\n\ninto\n" ++ show (showStructure (fnBody newfn))
              ++ "\nallMentions: " ++ show allMentions
              ++ "\nparents: " ++ show parents
              ++ "\nbindings: " ++ show bindings
              ++ "\nchild_functions: " ++ show children
              ++ "\nfunctions: " ++ show (Set.toList functionsSet)
              ++ "\ncallGraph: " ++ show [(n2b x, n2b y) | (x,y) <- Graph.edges callGraph]
              ++ "\nrelocList: " ++ show [(id,tidIdent (fnVar fn), dom) | ((id,fn),dom) <- relocationTargetsList]
              ) newfn
 where
  rebuildFn   = rebuildFnWith rebuilder addBindingsFor
  functions   = collectFunctions knf
  allMentions = collectMentions knf
  (parents, bindings, child_functions) = unzip3 functions

  children = map fnIdent child_functions

  bindingToChildMap = Map.fromList (zip bindings children)
  functionsSet      = Set.fromList $ fnIdent knf : parents ++ children

  (block2node, node2block) = buildIsomorphism functionsSet
    where buildIsomorphism elemset =
                let elems = Set.toList elemset in
                (Map.fromList $ zip elems [0..]
                ,Map.fromList $ zip [0..] elems )
  --  (block2node, node2block) :: (Map Ident Node, Map Node Ident)

  b2n e = case Map.lookup e block2node of
                 Just r -> r
                 Nothing -> error $ "block2node failed for " ++ show e
  n2b e = case Map.lookup e node2block of
                 Just r -> r
                 Nothing -> error $ "node2block failed for " ++ show e

  root = b2n (fnIdent knf)

  -- Build the call graph based on call site info.
  callGraph :: Graph.UGr
  callGraph = Graph.mkGraph lnodes ledges
    where
      mentions = [(parent, child) | (parent, binding) <- Set.toList allMentions
                 , child <- maybeToList $ Map.lookup binding bindingToChildMap]

      mentionsL = [(b2n caller, b2n callee) | (caller, callee) <- mentions]

      lnodes = let (callers, callees) = unzip mentionsL in
               let nodes = Set.toList $ Set.fromList $ callers ++ callees in
                   (root, ()) : [(n, ()) | n <- nodes]

      ledges = [(caller, callee, ()) | (caller, callee) <- mentionsL]

  reachable = Set.fromList $ map n2b $ Graph.dfs [root] callGraph

  -- If a function is dominated by a node which is not its parent, relocate it.
  -- relocationTargetsList :: [(Fn (KNExpr' t) t, Ident)]
  relocationTargetsList = [((id, f), dom)
                          | f_id <- Set.toList functionsSet
                          ,parent <- maybeToList $ Map.lookup f_id parentMap
                          ,dom    <- maybeToList $ Map.lookup f_id doms
                          ,(id,f) <- maybeToList $ Map.lookup f_id fnForChildId
                          , dom /= parent]
     where
          parentMap = Map.fromList (zip children parents)

          fnForChildId = Map.fromList [(fnIdent f, (id, f))
                                      | (id, f) <- zip bindings child_functions]

          -- Compute dominators of each function.
          doms :: Map Ident (Ident {-dom-})
          doms = Map.fromList [(n2b node, n2b ndom)
                              | (node, ndom) <- Graph.iDom callGraph root]

  -- Remove original bindings, if they are being relocated elsewhere.
  rebuilder idsfns =
      [(id, rebuildFn fn)
      |(id, fn) <- idsfns,
       Set.notMember (fnIdent fn) shouldBeRelocated
        -- Discard unreachable functions.
        && Set.member (fnIdent fn) reachable]
    where
        shouldBeRelocated = Set.fromList $ map (\((_id, fn), _) -> fnIdent fn)
                                               relocationTargetsList

  -- Add new bindings for functions which should be relocated.
  addBindingsFor f body = mkLetFuns newfns body
        where
          newfns   = [(id, rebuildFn fn)
                     | ((id, fn), dom) <- relocationTargetsList
                     , dom == fnIdent f]
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Loop Headers |||||||||||||||||||||||{{{

-- Insert loop headers for recursive functions in the program.
--
-- For each recursive function, we'll look at all the (recursive)
-- tail calls it makes, and which arguments each call passes.
--
-- If there's a subset of arguments which are passed at every recursive
-- call, these arguments will be factored out of the loop header
-- and each recursive call.
--
-- Since the loop header is only called from tail position, it will
-- be contifiable by definition. (This is why we ignore non-tail recursive
-- calls -- because inserting a non-contifiable function wrapper would
-- change the allocation behavior of programs.) But note that we must count
-- any occurrences in nested functions as non-tail calls. After all, eta
-- expansion means that a non-tail usage can be turned into a nested tail call.
--
-- Adding loop headers has two benefits:
--   1) Passing fewer arguments as loop arguments avoids unnecessary copies.
--   2) When inlining is applied, inlining a function wrapped in a loop header
--      corresponds to specializing the recursive function to its arguments,
--      rather than merely unrolling the loop once.
--
-- See Andrew Appel's 1994 paper "Loop Headers in lambda-calculus or CPS"
-- for more examples: http://www.cs.princeton.edu/~appel/papers/460.pdf

type Hdr = StateT HdrState Compiled
data HdrState =   HdrState {
    headers :: LoopHeaders
  , census  :: LoopCensus
  , varmap  :: Map Ident Ident -- for tracking bitcasts...
}

-- Map each function's (outer) bound identifier to a fresh id,
-- fresh variables, and a flag indicating whether any tail calls to
-- the function were detected, since we only care about arguments
-- passed to tail calls.
type LoopHeader  = (OuterIdent, [TypedId MonoType], InnerIdent)
type LoopHeaders = Map Ident (LoopHeader, Bool)
type InnerIdent = Ident
type OuterIdent = Ident

-- Map each recursive fn identifier to the list of variables it is always
-- passed. This list starts as [Just x] for each formal x; if a recursive call
-- ever passes a different variable, we'll switch to Nothing for that entry.
type LoopCensus  = Map Ident [Maybe (TypedId MonoType)]

mergeInfo :: [TypedId MonoType] -> [Maybe (TypedId MonoType)] -> [Maybe (TypedId MonoType)]
mergeInfo ys xs = -- implicit: lists are the same length...
    let r = map resolve (zip xs ys) in
    --trace ("mergeInfo\n\t" ++ show (map (fmap tidIdent) xs) ++ "\n\t" ++ show (map tidIdent ys) ++ "\n\n==>\t" ++ show (map (fmap tidIdent) r)) $
      r
  where resolve (Nothing, _) = Nothing
        resolve (Just x,  y) = if x == y then Just x else Nothing

-- At each call site, we want to pass only the args which were not useless;
-- i.e. the ones for which the corresponding info was unknown (Nothing).
dropUselessArgs :: [Maybe (TypedId MonoType)] -> [TypedId MonoType] -> [TypedId MonoType]
dropUselessArgs xs ys = resolve (zip xs ys)
  where resolve [] = []
        resolve ((Just  _, _):xs) =    resolve xs
        resolve ((Nothing, x):xs) = x:(resolve xs)

-- The loop header should rename variables which are getting new bindings
-- in the loop, but keep unchanged the variables that are loop-invariant.
renameUsefulArgs :: [Maybe (TypedId MonoType)] -> [TypedId MonoType] -> [TypedId MonoType]
renameUsefulArgs xs ys = resolve (zip xs ys)
  where resolve [] = []
        resolve ((Just  y, _):xs) = y:(resolve xs)
        resolve ((Nothing, x):xs) = x:(resolve xs)

-- Map each recursive fn identifier to the var/s for its loop header, and a
-- list reflecting which of the original formals were recursively useless.
type LoopInfo = Map Ident (LoopHeader, [Maybe (TypedId MonoType)])

isAllNothing [] = True
isAllNothing (Nothing:xs) = isAllNothing xs
isAllNothing (_      :_ ) = False

computeInfo :: LoopCensus -> LoopHeaders -> LoopInfo
computeInfo census headers = Map.mapMaybeWithKey go census
  where go id mt = let Just (hdr, called) = Map.lookup id headers in
                   if isAllNothing mt || not called
                     then Nothing
                     else Just (hdr, mt)

ccFreshen :: Ident -> Compiled Ident
ccFreshen (Ident name _) = ccFreshId name
ccFreshen id@(GlobalSymbol  _) = error $ "KNExpr.hs: cannot freshen global " ++ show id
ccFreshenTid (TypedId t id) = do id' <- ccFreshen id
                                 return $ TypedId t id'

knLoopHeaderCensusFn activeids (id, fn) = do
  let vars = fnVars fn
  id'   <- lift $ ccFresh ("loop.hdr." ++ T.unpack (identPrefix (fnIdent fn)) ++ "_")
  id''  <- lift $ ccFresh ("loophdr." ++ T.unpack (identPrefix (fnIdent fn)) ++ "_")
  vars' <- lift $ mapM ccFreshenTid vars -- generate new vars for wrapper in advance
  st <- get
  put $ st { headers = Map.insert id ((id' , vars', id'' ), False) (headers st)
           , census  = Map.insert id (map Just vars)               (census st) }
  knLoopHeaderCensus YesTail activeids (fnBody fn)

knLoopHeaderCensus :: TailQ -> Set Ident -> KNMono -> Hdr ()
knLoopHeaderCensus tailq activeids expr = go' tailq expr where
  go        expr = go' tailq expr
  go' tailq expr = case expr of
    KNCase        _ _ patbinds -> do mapM_ go (concatMap caseArmExprs patbinds)
    KNIf          _ _ e1 e2    -> do go e1 ; go e2
    KNLetVal      id  e1 e2    -> do go' NotTail e1
                                     case e1 of
                                       (KNTyApp _ v _)
                                         -> addIdRemapping id (tidIdent v)
                                       (KNVar v)
                                         -> addIdRemapping id (tidIdent v)
                                       _ -> return ()
                                     go e2
    KNLetRec      _   es  b    -> do mapM_ (go' NotTail) es ; go b
    KNLetFuns     ids fns b | all isRec fns -> do
      mapM_ (knLoopHeaderCensusFn (Set.fromList ids)) (zip ids fns)
      -- Note: when we recur, activeids will not
      -- include the bound ids, so calls in the
      -- body will be (properly) ignored.
      go b
    KNLetFuns     _ _ b -> do go b
    KNCall _ v vs | tailq == YesTail -> do -- TODO only for tail calls...
      id <- lookupId (tidIdent v)
      if Set.member id activeids
        then do st <- get
                put $ st { census  = Map.adjust (mergeInfo vs) id (census st)
                         , headers = Map.adjust (\(hdr, _) -> (hdr, True)) id (headers st) }
        else return ()

    -- Silently handle other cases...
    -- One potential improvement: track variable renamings.
    _ -> return ()

isRec fn = case fnIsRec fn of YesRec -> True
                              NotRec -> False

isPure (KNVar   {}) = True
isPure (KNTyApp {}) = True
isPure _ = False

lookupId id = do
  st <- get
  return $ Map.findWithDefault id id (varmap st)

addIdRemapping id id' = do
  id'' <- lookupId id'
  st <- get
  put $ st { varmap = Map.insert id id'' (varmap st) }

knLoopHeaders ::          (ModuleIL KNMono MonoType)
              -> Compiled (ModuleIL KNMono MonoType)
knLoopHeaders m = do body' <- knLoopHeaders' (moduleILbody m)
                     return $ m { moduleILbody = body' }

knLoopHeaders' :: KNMono -> Compiled KNMono
knLoopHeaders' expr = do
    HdrState h c r <- execStateT (knLoopHeaderCensus YesTail Set.empty expr)
                                 (HdrState Map.empty Map.empty Map.empty)
    let info = computeInfo c h
    --liftIO $ putStrLn $ show info
    return $ qq info r YesTail expr
 where
  qq info r tailq expr =
   let qv id = Map.lookup (Map.findWithDefault id id r ) info in
   let q = qq info r in
   case expr of
    KNLiteral     {} -> expr
    KNVar         {} -> expr
    KNKillProcess {} -> expr
    KNTyApp       {} -> expr
    KNTuple       {} -> expr
    KNAllocArray  {} -> expr
    KNArrayRead   {} -> expr
    KNArrayPoke   {} -> expr
    KNArrayLit    {} -> expr
    KNAlloc       {} -> expr
    KNStore       {} -> expr
    KNDeref       {} -> expr
    KNCallPrim    {} -> expr
    KNAppCtor     {} -> expr
    KNCompiles r t e -> KNCompiles r t (q tailq e)
    KNInlined _t0 _to _tn _old new -> q tailq new
    KNNotInlined _x e -> q tailq e
    KNCase        ty v arms     -> KNCase ty v (map (fmapCaseArm id (q tailq) id) arms)
    KNIf          ty v e1 e2    -> KNIf     ty v (q tailq e1) (q tailq e2)
    KNLetVal      id   e1 e2    -> let e1' = q NotTail e1
                                       e2' = q tailq   e2
                                       knz = KNLiteral (PrimInt I1) (LitBool False)
                                   in if isPure e1' && not (id `elem` freeIdents e2')
                                       then KNLetVal id knz e2' -- see {note 1}
                                       else KNLetVal id e1' e2'
    KNLetRec      ids es  b     -> KNLetRec ids (map (q NotTail) es) (q tailq b)
    KNLetFuns     [id] [fn] b ->
        case qv id of
          Nothing -> KNLetFuns [id] [fn { fnBody = (q YesTail $ fnBody fn) }] (q tailq b)

          -- If we have a single recursive function (as detected earlier),
          -- we should wrap its body with a minimal loop,
          -- and replace recursive calls with calls to a loop header.
          --
          -- For example, replace (rec fold = { f => x => ... fold f z ... };
          --                         in b end)
          -- with
          --                      (fun fold = { f => x' =>
          --                         rec loop = { x => ... loop z ... };
          --                         in
          --                             loop x' end
          --                       }; in b end)
          Just ((id' , vs' , id'' ), mt ) -> -- vs' is the complete list of fresh args
            let v'  = TypedId (selectUsefulArgs id' mt (tidType (fnVar fn))) id' in
            let v'' = TypedId (selectUsefulArgs id' mt (tidType (fnVar fn))) id'' in
            -- The inner, recursive body
            let fn'' = Fn { fnVar   = v''
                          , fnVars  = dropUselessArgs mt (fnVars fn)
                          , fnBody  = (q YesTail $ fnBody fn)
                          , fnIsRec = YesRec
                          , fnAnnot = annotForRange (rangeOf fn)
                          } in
            -- TODO should we create another wrapper to maintain the invariant
            -- that the outermost fn bound to id is always non-recursive,
            -- for inlining purposes?
            let fn' = Fn { fnVar   = fnVar fn
                         , fnVars  = renameUsefulArgs mt vs'
                         , fnBody  = KNLetFuns [ id' ] [ fn'' ]
                                         (KNCall (typeKN (fnBody fn)) v' (dropUselessArgs mt vs' ))
                         , fnIsRec = computeIsFnRec fn' [id]
                         , fnAnnot = fnAnnot fn
                         } in
            KNLetFuns [id ] [ fn' ] (qq (Map.delete id info) r tailq b)

    KNLetFuns     ids fns b     ->
        -- If we have a nest of recursive functions,
        -- the replacements should only happen locally, not intra-function.
        -- (TODO)
        KNLetFuns ids (map (\fn -> fn { fnBody = q YesTail (fnBody fn) }) fns) (q tailq b)

    -- If we see a *tail* call to a recursive function, replace it with
    -- the appropriate pre-computed call to the corresponding loop header.
    KNCall ty v vs ->
      case (tailq, qv (tidIdent v)) of
        (YesTail, Just ((id, _, _), mt)) ->
             KNCall ty (TypedId (selectUsefulArgs id mt (tidType v)) id) (dropUselessArgs mt vs)
        _ -> expr

-- Drop formal param types from the function type if the corresponding
-- value arg isn't getting passed any more. @see dropUselessArgs
selectUsefulArgs :: Ident -> [Maybe (TypedId MonoType)] -> MonoType -> MonoType
selectUsefulArgs _id' mt (FnType args rt cc pf) = let args' = (concatMap resolve (zip mt args)) in
                                               FnType args' rt cc pf
                                              where resolve (Nothing, t) = [t]
                                                    resolve (Just  _, _) = []
selectUsefulArgs id' _ ty = error $ "KNExpr.hs wasn't expecting a non-function type for selectUsefulArgs["++show id' ++"], but got " ++ show ty

-- {note 1}::
-- The issue at play is that recursive polymorphic functions will recurse via
-- a type application. So if ``r`` is a recursive function binding, its
-- recursive calls will look like::
--      x = r:[...] ; ... ; x ...
--    id^   e1^      e2^
-- When we insert loop headers, ``q e2`` will replace the tail call of ``x``
-- with `` ; ... ; loop.hdr ...``. The issue then is that ``x`` is now dead,
-- and if we don't drop its binding, then ``r`` will be counted as recursive
-- even though it shouldn't be... which then impedes inlining opportunities
-- later on down the road. So for pure bindings, we check to see if they are
-- dead and should be dropped.

mkGlobalWithType ty (Ident t u) = TypedId ty (GlobalSymbol $ T.pack (T.unpack t ++ show u))
mkGlobalWithType _  (GlobalSymbol _) = error $ "KNExpr.hs: mkGlobal(WithType) of global!"

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- {{{||||||||||||||||||||||  Inlining  ||||||||||||||||||||||||||||

-- Implementation of inlining based on the paper
--              Fast and Effective Procedure Inlining
--      by Oscar Waddell and R. Kent Dybvig
-- http://www.cs.indiana.edu/~dyb/pubs/inlining.pdf
--
-- Notes/comments:
--
--  * Having bindings rather than mutable variables simplifies things a bit.
--
--  * Having explicit rather than implicit coercions removes the need for
--    value-versus-effect contexts.
--
--  * Our source IR is K-normal form, rather than arbitrarily-
--    nested ASTs. This means we don't have to worry about preserving
--    applicative-order of effects, nor about duplicating work when
--    inlining/copy-propagating constructor applications to discrimination
--    sites. We also eliminate the context parameter, since occurrences are
--    second class, thus arguments are flattened out by definition.
--
--  * The original motivation for the "demand-driven" aspect of their algorithm
--    (i.e. not looking at operands until required) was to wait until it was
--    known what context each operand should be eval'd in (Boolean/Value/...).
--    Because we have no contexts, it is better for us to eagerly rather than
--    lazily evaluate operands to calls. The main advantage of doing so is that
--    we can be more parsimonious about when to try folding a call or not.
--
--  * We conservatively track variable reference counts with mutable state.
--    We can have false positives (variable appears referenced but is not)
--    if an occurrence is residualized and then the inlining attempt is aborted.
--    If we implemented Kennedy's scheme for mutable occurrences in his CPS
--    form, we could make reference counts precise. We could also be fancy
--    about tracking reference counts as explicit pure state, but the compile-
--    time costs would probably outweigh the run-time benefits. As it is, we
--    can fall back on CFG optimization to remove truly dead bindings.
--
--  * Similarly, we can fall back to LLVM for inlining calls to top-level
--    procedures. However, LLVM won't do much about inlining/specializing
--    higher-order closures or data type constructor information.
--
--  * A very important pattern to inline is     iter x { E2 },
--    which ends up looking like    f = { E2 }; iter x f;
--    with f not referenced elsewhere.  Even if E2 is big enough
--    that we wouldn't usually inline it, given the body of iter,
--    if this is the only place f is used, we ought to inline it anyways.
--      (We rely on contification to Do The Right Thing when iter calls f once).
--    The paper mentions this optimization for a call of a use-once function,
--    but not a call of a many-use function being passed a use-once function.
--    In practice, this "budget donation" significantly reduces the variability
--    of inlining's run-time benefits due to choice of the size counter budget.
--
--  * I haven't yet implemented an effort counter. Thanks to types, I don't
--    think the source language contains omega-like pitfalls, and an effort
--    counter would merely mask non-linear inliner behavior.
--
--  * The paper mentions that the inner- and outer-pending flags can be used
--    to govern loop unrolling and peeling, which intuitively makes sense,
--    but my attempts so far have resulted in non-linear and/or non-terminating
--    behavior. (I think the answer has something to do with subtleties about
--    when residualized size costs are accounted for, and when new size counters
--    are spawned). For now, I don't unroll recursive functions at all.
--
--  * But that's not as bad as it sounds at first, because we insert loop
--    headers before running inlining (it seems simpler than their online
--    analysis for the same purpose). Thus we'll aggressively specialize
--    higher-order loops to their concrete function parameters, but not (yet)
--    do any loop unrolling.  Contification can handle some instances of
--    optimizations within recursive nests; it's not yet clear what sorts
--    of recursive nests are better served by inlining than contification.
--
--  * We do very limited constant folding for now, just enough to make sure
--    it works. The biggest limitation is we only support literals and nullary
--    constructors.
--
--  * One not-yet implemented trick is to incorporate more sophisticated
--    size thresholds, for example being more generous with calls involving
--    many parameters, in recognition that call site overhead varies thusly.
--
--  * We only need to fiddle with the outer-pending limit
--    on the *first* integration of a procedure. When we are
--    integrating a cached procedure, it's OK to integrate
--    another copy of that procedure.
--    This occurs in "manually unrolled" code like
--       hr = { ... k => ... k ... };   (( cached version ))
--       kk = { hr(1) ... ... };
--       hr(0) ... kk
--    When evaluating the hr(0) call, we'll attempt to inline the body
--    of hr with k bound to kk. Inlining will then attempt to inline kk,
--    which then looks at the hr(1) call. If we had set the outer-pending
--    flag when looking at hr(0), the hr(1) call would be needlessly
--    residualized instead of inlined.
--
--  * Census information is not kept consistent with inlining results.
--    In particular, if a leaf has a single call site, it will be inlined
--    without a size limit at every point the call site is inlined.


knInline :: Maybe Int -> Bool -> (ModuleIL SrcExpr MonoType)
                     -> Compiled (ModuleIL ResExpr MonoType)
knInline mbDefaultSizeLimit shouldDonate knmod = do
  uniq <- gets ccUniqRef
  sizectr <- newRef 0
  currlvl <- newRef 0
  effort  <- newRef 0
  --foldResultsRef <- newRef []
  let defaultSizeLimit = case mbDefaultSizeLimit of Nothing -> 42 * 2
                                                    Just  x -> x
  let e  = moduleILbody knmod
  let et = runExceptT (knInlineToplevel e (SrcEnv Map.empty Map.empty))
  stkRef <- newRef []
  cenRef <- newRef $ inCensus e
  let st = evalStateT et (InlineState uniq stkRef currlvl effort Map.empty sizectr NoLimit
                                      cenRef defaultSizeLimit shouldDonate)
  result <- liftIO st
  expended <- readRef effort
  stk <- readRef stkRef
  liftIO $ putDocLn  $ text "------------------------------------"
  liftIO $ putDocLn4 $ text "stkref was:" <$> pretty stk
  liftIO $ putDocLn4 $ text "census was:" <$> pretty (Map.toList $ inCensus e)
  --do foldResults <- readRef foldResultsRef
  --   liftIO $ putDocLn $ text "failed unfoldings :" <$> pretty [fr | fr <- reverse foldResults, foldResultFailed fr]
  --   liftIO $ putDocLn $ text "non-zero-cost unfoldings costs :" <$> pretty [fr | fr <- reverse foldResults, foldCost fr /= Just 0]
  --   liftIO $ putDocLn $ text "non-zero-cost unfoldings count :" <> pretty (length [fr | fr <- reverse foldResults, foldCost fr /= Just 0])
  --   liftIO $ putDocLn $ text "total count of attempted unfoldings was:" <> pretty (length foldResults)
  --do liftIO $ putDocLn $ text "non-zero-cost unfolding average cost: " <> pretty (expended `div` length [foldCost fr | fr <- reverse foldResults, foldCost fr /= Just 0])
  --   liftIO $ putDocLn $ text "average effort per unfold attempt: " <> pretty (expended `div` length foldResults)
  do liftIO $ putDocLn $ text "total number of callsites in src program: " <> pretty (countCallSites e)
     liftIO $ putDocLn $ text "total effort expended while inlining: " <> pretty expended
     liftIO $ putDocLn $ text "average effort per call site: " <> pretty (expended `div` countCallSites e)

  case result of
    Right (Rez expr') -> do
        liftIO $ putDocLn $ text "total number of inlining decision points in final program: " <> pretty (countInliningDecisionPoints expr')
        return $ knmod { moduleILbody = expr' }
    Left err -> do liftIO $ putStrLn $ show err
                   liftIO $ putStrLn $ "knInline failed, aborting whole deal!"
                   return $ knmod

-- {{{ Misc definitions...
type In          = ExceptT InlineError (StateT InlineState IO)
data InlineState = InlineState {
    inUniqRef  :: IORef Uniq
  , inCurrentPendings :: IORef [KNExpr' RecStatus MonoType]
  , inCurrentLevel :: IORef Int
  , inEffortTotal  :: IORef Int
  , inVarCount :: Map Ident (IORef Int)
  -- , inFoldResults :: IORef [FoldResult]
  , inSizeCntr :: IORef Int
  , inSizeLimit :: SizeLimit
  , inCallPassCensus :: IORef (Map Ident (Int, Int))
  , inDefaultSizeLimit :: Int
  , inShouldDonate :: Bool
}

data FoldResult = FoldFail FoldStatus SrcExpr (Maybe Int) -- cost
                | FoldInto (Rez ResExpr) Int SrcExpr Int -- size, cost

instance Pretty FoldResult where
    pretty (FoldFail    status expr cost) = pretty status <+> parens (pretty expr) <+> text "at cost" <+> pretty cost
    pretty (FoldInto _rez size expr cost) = pretty_status <+> parens (pretty expr) <+> text "at cost" <+> pretty cost
                                      where pretty_status = text "success, size=" <> pretty size

--foldCost :: FoldResult -> Maybe Int
--foldCost (FoldFail   _ _ mb_cost) = mb_cost
--foldCost (FoldInto _ _ _    cost) = Just cost
--
--foldResultFailed (FoldInto {}) = False
--foldResultFailed (FoldFail {}) = True

data InlineError = InlineErrorSize String
                 | InlineErrorEffort Doc deriving Show

shouldDEBUG = False

debugDocLn d =
  if shouldDEBUG then putDocLn d
                 else return ()

                 {-
putDocLn  d = liftIO $ putDoc $ d <> line
putDocLn4 d = liftIO $ putDoc $ d <> line
putDocLn5 d = liftIO $ putDoc $ d <> line
putDocLn3 _ = return ()
putDocLn6 _ = return ()
putDocLn7 d = liftIO $ putDoc $ d <> line
-}
{-
putDocLn  _d = liftIO $ putDoc $ _d <> line
putDocLn4 _d = liftIO $ putDoc $ _d <> line
putDocLn5 _d = liftIO $ putDoc $ _d <> line
putDocLn3 _d = liftIO $ putDoc $ _d <> line
putDocLn6 _d = liftIO $ putDoc $ _d <> line
putDocLn7 _d = liftIO $ putDoc $ _d <> line
-}

putDocLn  _d = liftIO $ putDoc $ _d <> line
--putDocLn  _ = return ()
putDocLn3 _ = return ()
putDocLn4 _ = return ()
putDocLn5 _ = return ()
putDocLn6 _ = return ()
putDocLn7 _ = return ()
--putDocLn7 _d = liftIO $ putDoc $ _d <> line

-- Runs a, then runs b (which may throw an error),
-- then (always) runs c (which should not throw an error),
-- and returns b's value, or the exception it threw.
-- Note that this is a different order than bracket_ !
inBracket_ :: String -> In a -> In b -> In c -> In b
inBracket_ msg a b c0 = do
  t0 <- knTotalEffort
  lvl <- knInLevel
  let c = do
            t1 <- knTotalEffort
            _ <- if ((t1 - t0) > 700 || msg == "visitF:nolimit:foster_nat_add_digits"
                    || msg == "withSizeCounter:visitF:nolimit:foster_nat_add_digits")
                    && (msg /= "withRaisedLevel")
                    && (msg /= "withSizeCounter:visitE:")
              then liftIO $ putStrLn $ "total effort in bracket call at lvl " ++ show lvl ++ " went from " ++ show t0 ++ " to " ++ show t1 ++ " aka + " ++ show (t1 - t0) ++ " ; " ++ msg
              else return ()
            c0
  a >> catchError (b >>= \v -> c >> return v)
                  (  \e -> c >> throwError e)

inBracket_' :: String -> In a -> In b -> (Bool -> In c) -> In b
inBracket_' msg a b c0 = do
  t0 <- knTotalEffort
  lvl <- knInLevel
  let c x
       = do
            t1 <- knTotalEffort
            _ <- if (t1 - t0) > 700 || msg == "visitF:nolimit:foster_nat_add_digits"
                    || msg == "withSizeCounter:visitF:nolimit:foster_nat_add_digits"
              then liftIO $ putStrLn $ "total effort in bracket' call at lvl " ++ show lvl ++ " went from " ++ show t0 ++ " to " ++ show t1 ++ " : + " ++ show (t1 - t0) ++ " ; " ++ msg
              else return ()
            c0 x
  a >> catchError (b >>= \v -> c False >> return v)
                  (  \e -> c True >> throwError e)

type SrcId = Ident
type ResId = Ident

freshenId :: SrcId -> In ResId
freshenId id = do id' <- freshenId' id
                  inNewVar id'
                  updateCensus id id'
                  return id'

freshenId' :: SrcId -> In ResId
freshenId' (GlobalSymbol name) = -- error $ "can't freshen global symbol " ++ (T.unpack name)
     do u <- newUniq
        return $ Ident name u

freshenId' (Ident name _) = do
        u  <- newUniq
        return $ Ident name u

freshenTid tid = do
        id <- freshenId (tidIdent tid)
        return $ TypedId (tidType tid) id

updateCensus id id' = do
  r <- gets inCallPassCensus
  m <- readRef r
  --liftIO $ putStrLn $ "!!!!!!!!!!! updating census " ++ show id ++ " ~~> " ++ show id' ++ "  ==  " ++ show (Map.lookup id m)
  case Map.lookup id m of
   Nothing -> return ()
   Just v  -> writeRef r (Map.insert id' v m)

-- resVar :: Env -> SrcVar -> In ResVar
resVar env v = do
        case lookupVarMb v env of
                   Just id -> do sawVar id
                                 return $ (TypedId (tidType v) id)
                   Nothing -> do return $ v

type SrcExpr = (KNExpr' RecStatus MonoType)
type ResExpr = (KNExpr' RecStatus MonoType)
data VisitStatus t = Unvisited | Visited !t !Int !Int -- size, timestamp
data SrcEnv = SrcEnv !(Map Ident VarOp)
                     !(Map Ident Ident)
type SrcFn = Fn RecStatus SrcExpr MonoType
type ResFn = Fn RecStatus ResExpr MonoType
data OuterPending = OP_Limit Int
data InnerPending = IP_Limit Int
data Opnd v = Opnd v SrcEnv (IORef (VisitStatus v)) (IORef OuterPending) (IORef InnerPending)
data VarOp = VO_E (Opnd               SrcExpr)
           | VO_F (Opnd (Fn RecStatus SrcExpr MonoType))
newtype Rez a = Rez a

opndOldValue (Opnd v _ _ _ _) = v
opndVisitStatus (Opnd _ _ vr _ _) = readRef vr

when True   action = do action
when False _action = return ()

residualizeCached :: a -> Int -> In (Rez a)
residualizeCached e size = do
                   bumpSize (size, Nothing)
                   return (Rez e)

residualize :: ResExpr -> In (Rez ResExpr)
residualize e = do bumpSize (knSizeHead e, Nothing)
                   return (Rez e)

rezM1 k a1    = do a1' <- a1 ;             residualize $ k a1'
rezM2 k a1 a2 = do a1' <- a1 ; a2' <- a2 ; residualize $ k a1' a2'

-- We don't track var flags here because we syntactically distinguish
-- assigned variables from pure ones, and we can use Hoopl-based liveness
-- later on to eliminate useless assignments and/or bindings.

instance Show VarOp where
  show (VO_E _) = "VO_E"
  show (VO_F (Opnd f _ _ _ _)) = "VO_F " ++ show (tidIdent $ fnVar f)

lookupVarMb :: TypedId MonoType -> SrcEnv -> Maybe Ident
lookupVarMb v (SrcEnv _ ii) = Map.lookup (tidIdent v) ii

-- src var
lookupVarOp :: SrcEnv -> TypedId MonoType -> Maybe VarOp
lookupVarOp env@(SrcEnv tv _) v =
  case lookupVarMb v env of
    Nothing -> -- Declarations for external functions won't
               -- have a known binding, obviously.
               Map.lookup (tidIdent v) tv
    Just vv ->
      case Map.lookup vv tv of
        Just op -> Just op
        Nothing -> error $ "KNExpr inlining (lookupVarOp) failed to look up var op " ++ show v ++ " ~~> " ++ show vv

-- residual var
lookupVarOp' :: SrcEnv -> TypedId MonoType -> VarOp
lookupVarOp' (SrcEnv tv _) vv =
  case Map.lookup (tidIdent vv) tv of
    Just op -> op
    Nothing -> error $ "KNExpr inlining (lookupVarOp') failed to look up var op " ++ show vv

extendEnv :: [Ident] -> [Ident] -> [VarOp] -> SrcEnv -> SrcEnv
extendEnv !ids !ids' !ops (SrcEnv io ii) =
        (SrcEnv (Map.union (Map.fromList $ zip ids' ops  ) io)
                (Map.union (Map.fromList $ zip ids  ids' ) ii))

readRef  r   = liftIO $ readIORef  r
writeRef r v = liftIO $ writeIORef r v
newRef     v = liftIO $ newIORef     v
newUniq = do uref <- gets inUniqRef
             liftIO $ modIORef' uref (+1) >> readIORef uref


opLimitMax = 1

mkOpRefs = do
  lexp <- newRef Unvisited
  oup  <- newRef (OP_Limit opLimitMax)
  inp  <- newRef (IP_Limit 1) -- TODO experiment with larger values here...
  return (lexp, oup, inp)

mkOpExpr _msg e env = do
  --putDocLn $ text "mkOpExpr " <> text msg
  (le, oup, inp) <- mkOpRefs
  return $ Opnd e env le oup inp

-- Apply a variable substitution in a pattern.
qp :: (TypedId ty -> In (TypedId ty)) -> (PatternRepr ty) -> In (PatternRepr ty)
qp subst pattern = do
 case pattern of
   PR_Atom           atom       -> liftM    PR_Atom                 (qpa subst  atom)
   PR_Tuple    rng t pats       -> liftM   (PR_Tuple    rng t) (mapM (qp subst) pats)
   PR_Or       rng t pats       -> liftM   (PR_Or       rng t) (mapM (qp subst) pats)
   PR_Ctor     rng t pats ctor  -> do p' <-                     mapM (qp subst) pats
                                      return $ PR_Ctor  rng t p' ctor

qpa :: (TypedId ty -> In (TypedId ty)) -> (PatternAtom ty) -> In (PatternAtom ty)
qpa subst pattern = do
 case pattern of
   P_Wildcard  {}         -> return pattern
   P_Bool      {}         -> return pattern
   P_Int       {}         -> return pattern
   P_Variable rng v       -> liftM (P_Variable rng) (subst v)

summarizeVarOp (VO_E o) = summarize o
summarizeVarOp (VO_F o) = summarize o

summarize (Opnd _ _ loc_fn loc_op loc_ip) = do
  lfn <- readRef loc_fn
  OP_Limit lop <- readRef loc_op
  IP_Limit lip <- readRef loc_ip
  !r <- gets inSizeCntr
  !l <- gets inSizeLimit
  !x <- readRef r
  return $ text "size=" <> pretty x <> text "; " <>
           text "op=" <> pretty lop <> text "; " <>
           text "ip=" <> pretty lip <> text "; " <>
           text "cf=" <> (case lfn of
                           Visited _ size _ -> text "Visited@" <> pretty size
                           _ -> text "Unvisited") <> text "; " <>
           text ("lim=" ++ show l) <> text "; "

-- If an arg hasn't been visited yet, we'll compute & use the overall
-- size of the original expr, which should overestimate the true size.
bestEffortOpSize (VO_E (Opnd e _ loc _ _)) = bestEffortOpSize_ loc e
bestEffortOpSize (VO_F (Opnd f _ loc _ _)) = bestEffortOpSize_ loc (fnBody f)

bestEffortOpSize_ loc e = do
  r <- readRef loc
  case r of
    Visited _ size _ -> return size
    _                -> return size where (_, size) = knSize e

maybeCachedOpSize (VO_E (Opnd _ _ loc _ _)) = do
  r <- readRef loc
  case r of
    Visited _ size _ -> return $ Just size
    _                -> return $ Nothing
maybeCachedOpSize (VO_F (Opnd _ _ loc _ _)) = do
  r <- readRef loc
  case r of
    Visited _ size _ -> return $ Just size
    _                -> return $ Nothing

{- {{{
data MbCachedEF = MCEF_0 | MCEF_E ResExpr | MCEF_F ResFn

maybeCachedEF (VO_E (Opnd _ _ loc _ _)) = do
  r <- readRef loc
  case r of
    Visited val _ _ -> return $ MCEF_E val
    _               -> return $ MCEF_0

maybeCachedEF   (VO_F (Opnd _ _ loc _ _)) = do
  r <- readRef loc
  case r of
    Visited val _ _ -> return $ MCEF_F val
    _               -> return $ MCEF_0
}}} -}

-- }}}

-- {{{ Size counters and size limits...
getSize :: In Int
getSize = do
  !r <- gets inSizeCntr
  !x <- readRef r
  return x

canBumpSizeBy :: Int -> In (Bool, Int, Maybe Int)
canBumpSizeBy d = do
  !x <- getSize
  let !v = x + d
  !lim <- gets inSizeLimit
  case lim of
    Limit (limit, _) -> return (v <= limit, x, Just limit)
    NoLimit          -> return (True, x, Nothing)

bumpSize :: (Int, Maybe (Ident, Ident)) -> In ()
bumpSize !(d, mb_ids) = do
  !r <- gets inSizeCntr
  !x <- readRef r
  let !v = x + d
  !lim <- gets inSizeLimit
  case lim of
    Limit (limit, src) | v > limit -> do
        inDebugStr $ "bumpSize failed; " ++ show x ++ " += " ++ show d ++ " >= " ++ show lim ++ " ;; " ++ show mb_ids
        throwError (InlineErrorSize $ "bumpSize failed : " ++ show x ++ " + " ++ show d ++ "; " ++ src ++ " ;; " ++ show mb_ids)
    _ -> writeRef r v

inDebugStr s = do
  lvl <- knInLevel
  --putDocLn $ indent (lvl * 2) (text s)
  liftIO $ putStrLn $ "@ lvl " ++ (show lvl) ++ ": " ++ s
{-
inDebug doc = do
  lvl <- knInLevel
  putDocLn $ indent (lvl * 2) doc
-}

knInLevel :: In Int
knInLevel = do
  st <- get
  let levelref = inCurrentLevel st
  readRef levelref

knBumpTotalEffort :: In ()
knBumpTotalEffort = do
  st <- get
  let ref = inEffortTotal st
  n <- readRef ref
  writeRef ref (n + 1)

knTotalEffort :: In Int
knTotalEffort = do
  st <- get
  let ref = inEffortTotal st
  readRef ref

withRaisedLevel :: In a -> In a
withRaisedLevel action = do
  st <- get
  let levelref = inCurrentLevel st
  old <- readRef levelref
  writeRef levelref (old + 1)
  result <- action
  writeRef levelref  old
  return result

withPendingFold :: KNExpr' RecStatus MonoType -> In a -> In a
withPendingFold pending action = do
  st <- get
  let stackref = inCurrentPendings st
  old <- readRef stackref
  writeRef stackref (pending:old)
  result <- action
  writeRef stackref old
  return result

--addSizeLimit :: SizeLimit -> Int -> SizeLimit
--addSizeLimit NoLimit _ = NoLimit
--addSizeLimit (Limit (i,s)) d = Limit (i + d,s)

-- Performs an action, insulating the accumulated size information
-- from the current counter, and returns the result with the computed size.
withSizeCounter :: String -> SizeCounter -> In a -> In (a, Int)
withSizeCounter msg (SizeCounter sz lim) action = do
  st <- get
  let oldszref = inSizeCntr  st
  let oldszlim = inSizeLimit st
  szref <- newRef sz
  v <- inBracket_ ("withSizeCounter:" ++ msg)
                  (put $ st { inSizeCntr = szref , inSizeLimit = lim })
                  action
                  (put $ st { inSizeCntr = oldszref, inSizeLimit = oldszlim })
  size <- readRef szref
  return (v, size - sz)

getLimitedSizeCounter :: Int -> String -> In SizeCounter
getLimitedSizeCounter lim src = do
  x <- getSize
  c <- gets inSizeLimit
  case c of Limit c' -> do return $ SizeCounter x (Limit c')
            NoLimit  -> do -- putDocLn $ text $ "getLimitedSizeCounter creating fresh counter"
                           return $ SizeCounter 0 (Limit (lim, src))

-- Use census-based information to compute an appropriate size counter
-- at each inlining site. Functions which are called once should always
-- be inlined at their known call site. If donation is enabled, the size
-- counter should grow proportionally to the sizes of the function's arguments.
computeSizeCounter :: TypedId MonoType -> Maybe (Int, Int)
                                      -> [Maybe (Int, Int)] -> [Int] -> In SizeCounter
computeSizeCounter _v vinfo arginfo argsizes = do
  if vinfo == Just (1, 0)
    then do -- If a function is called once, we can inline it without a size limit.
            putDocLn4 $ text $ "inlining " ++ show (tidIdent _v) ++ " with no size limit due to census"
            return (SizeCounter 0 NoLimit)
    else do
      shouldDonate <- gets inShouldDonate
      let donate =
             if shouldDonate
                  then sum [s | (Just (0, 1), s) <- zip arginfo argsizes]
                  else 0
      defaultSizeLimit <- gets inDefaultSizeLimit
      getLimitedSizeCounter (defaultSizeLimit + donate)
                            ("computeSizeCounter(+"++show donate++"):" ++ show (tidIdent _v))
-- }}}

-- {{{ Variable tracking
-- We really only care about functions, not arbitrary bindings (which are
-- often dead, for sequence-induced bindings). However, it's clearer to
-- just treat variables uniformly.
inNewVar :: ResId -> In ()
inNewVar id = do st <- get
                 r  <- newRef 0
                 put $ st { inVarCount = Map.insert id r (inVarCount st) }

sawVar id = do vcm <- gets inVarCount
               case Map.lookup id vcm of
                 Nothing -> error $ "sawVar had no count for " ++ show id
                 Just r -> do liftIO $ modIORef' r (+1)

getVarStatus id = do vcm <- gets inVarCount
                     case Map.lookup id vcm of
                       Nothing -> error $ "getVarStatus had no count for " ++ show id
                       Just r -> do v <- liftIO $ readIORef r
                                    return $ classifyVarCount v
data VarStatus = Dead | Once | Many deriving Show
classifyVarCount :: Int -> VarStatus
classifyVarCount x | x <= 0
                   = Dead
classifyVarCount 1 = Once
classifyVarCount _ = Many

notDead Dead = False
notDead _    = True

-- We need to force TextFragment to stay around because it will be
-- referenced by the standard library.
relevant occst id =
  let isRelevant = notDead occst || id == (GlobalSymbol $ T.pack "TextFragment")
  in --trace ("relevant " ++ show occst ++ " " ++ show id ++ " = " ++ show isRelevant) $
       isRelevant
-- }}}

-- {{{ Specialized version of knInline' which does not rename functions.
knInlineToplevel :: SrcExpr -> SrcEnv -> In (Rez ResExpr)
knInlineToplevel expr env = do
        go expr env
 where
  go expr env = do
   let q v = resVar env v
   knBumpTotalEffort
   case expr of
    KNLetFuns ids fns body -> do
        --liftIO $ putStrLn $ "saw toplevel fun bindings of " ++ show ids
        let ids' = ids -- Don't rename top-level functions!
        mapM_ inNewVar ids' -- but do give them occurrence counters

        refs <- mapM (\_ -> mkOpRefs) fns
        let ops  = map (\(f,(r1,r2,r3)) -> (Opnd f env' r1 r2 r3)) (zip fns refs)
            env' = extendEnv ids ids' (map VO_F ops) env

        Rez b' <- go body env'
        let doVisitFn (id, op) = do
                before <- knTotalEffort
                mbfn <- visitF "KNLetFuns"  op
                after <- knTotalEffort
                liftIO $ putStrLn $ "final visiting of toplevel fn " ++ show id ++ " cost " ++ show (after - before)
                return mbfn
        mb_fns <- mapM doVisitFn (zip ids ops)
        let pickFn (_ , Cached _ f _) = do return f
            pickFn (fn, Failed _)     = do return fn
        fns' <- mapM pickFn (zip fns mb_fns)
        occ_sts <- mapM getVarStatus ids'
        let irrel_ids = [(id, id') | (id, id' , occst) <- zip3 ids ids' occ_sts, not (relevant occst id' ) ]
        liftIO $ putDocLn3 $ text "toplevel dead ids: " <> pretty irrel_ids
        return $ Rez $ mkLetFuns [(id, fn) | (id, fn, occst)
                                 <- zip3 ids' fns' occ_sts
                                 , relevant occst id] b'

    KNCall ty v vs ->
        case lookupVarOp env v of
            Just (VO_F opf) -> do
                 _ <- visitF "KNCall" opf -- don't inline away main, just process it!
                 rezM2 (KNCall ty) (q v) (mapM q vs)
            _ -> error $ "knInlineToplevel couldn't find function to inline for main!"

    _ -> error $ "knInlineToplevel expected a series of KNLetFuns bindings! had " ++ show expr
-- }}}

knInline' :: SrcExpr -> SrcEnv -> In (Rez ResExpr)
knInline' expr env = do
  let qs _str v = do --liftIO $ putStrLn $ "resVar << " ++ str ++ "\t;\t" ++ show (tidIdent v)
                     resVar env v
  let q v = resVar env v
  let qav (Left lit) = return (Left lit)
      qav (Right v) = liftM Right (q v)
  knBumpTotalEffort
  withRaisedLevel $ case expr of
    KNCompiles _r _t e -> do Rez e' <- knInline' e env
                             return $ Rez $ KNCompiles _r _t e'
    KNInlined _t0 _to _tn _old new -> do Rez new' <- knInline' new env
                                         return $ Rez $ KNInlined _t0 _to _tn _old new'
    -- We must re-process un-inlined calls, for example because we have
    -- introduced bindings for variables which were unbound when this expression
    -- was first processed.
    KNNotInlined _x e -> do Rez e' <- knInline' e env
                            return $ Rez $ KNNotInlined _x e'
    KNLiteral     {} -> residualize expr
    KNKillProcess {} -> residualize expr
    KNArrayRead ty (ArrayIndex v1 v2 rng sg)    -> (mapM q [v1,v2   ]) >>= \[q1,q2]    -> residualize $ KNArrayRead ty (ArrayIndex q1 q2 rng sg)
    KNArrayPoke ty (ArrayIndex v1 v2 rng sg) v3 -> (mapM q [v1,v2,v3]) >>= \[q1,q2,q3] -> residualize $ KNArrayPoke ty (ArrayIndex q1 q2 rng sg) q3
    KNArrayLit  ty arr vals -> do vals' <- mapM qav vals
                                  arr' <- q arr
                                  residualize $ KNArrayLit ty arr' vals'
    KNAllocArray ty v amr zi -> (q v)       >>= \zv -> residualize $ KNAllocArray ty zv amr zi
    KNDeref      ty v      -> (q v)       >>= \zv -> residualize $ KNDeref      ty zv
    KNAlloc      ty v mem  -> (q v)       >>= \zv -> residualize $ KNAlloc      ty zv mem
    KNTyApp      ty v tys  -> (q v)       >>= \zv -> residualize $ KNTyApp      ty zv tys
    KNTuple      ty vs rng -> (mapM q vs) >>= \zv -> residualize $ KNTuple      ty zv rng
    KNStore      ty v1 v2  -> rezM2                         (KNStore      ty) (q v1) (q v2)

    KNVar v -> rezM1 KNVar (qs "KNVar" v)

    KNAppCtor     ty cid vs  -> rezM1 (KNAppCtor ty cid) (mapM q vs)

    KNIf          ty v e1 e2 -> do
        -- If something is known about v's value,
        -- select either e1 or e2 appropriately;
        -- otherwise, if e2 and e3 are both the same value,
        -- we can get rid of the if;
        -- otherwise, business as usual.
        mb_const <- extractConstExpr env v
        case mb_const of
          IsConstant _ (Lit _ (LitBool b)) -> knInline' (if b then e1 else e2) env
          _ -> do v'      <- q v
                  Rez e1' <- knInline' e1 env
                  Rez e2' <- knInline' e2 env
                  residualize $ KNIf ty v' e1' e2'

    KNCase        ty v patbinds -> do
        let inlineArm (CaseArm !pat !expr !guard !vars _rng) = do
                !ops <- mapM (\v -> mkOpExpr ("kncase:"++show (tidIdent v)) (KNVar v) env) vars
                let !ids  = map tidIdent vars
                !ids'  <- mapM freshenId ids
                let !env' = extendEnv ids ids' (map VO_E ops) env
                !pat'  <- qp   (resVar env' ) pat
                !vars' <- mapM (resVar env' ) vars
                Rez !expr' <- knInline' expr env'
                -- TODO handle guard?
                return (CaseArm pat' expr' guard vars' _rng)

        -- If something is known about v's value,
        -- select or discard the appropriate branches.
        -- TODO when are default branches inserted?
        mb_const <- extractConstExpr env v
        case mb_const of
          IsConstant v' c -> do
                   mr <- matchConstExpr v' c patbinds
                   case {-trace ("match result for \n\t" ++ show c ++ " is\n\t" ++ show mr)-} mr of
                      Right e -> knInline' e env
                      Left patbinds0 -> do v' <- q v
                                           !patbinds' <- mapM inlineArm patbinds0
                                           residualize $ KNCase ty v' patbinds'
          _ -> do v' <- q v
                  !patbinds' <- mapM inlineArm patbinds
                  residualize $ KNCase ty v' patbinds'

    KNLetVal id bound body -> do
        -- Be demand-driven: don't investigate bound (op) until
        -- either body finds it necessary or we need to reconstruct
        -- the let binding, whichever comes first.
        id' <- freshenId id
        op <- mkOpExpr ("knletval:"++show id) bound env
        (bound', size) <- visitE (id, op) -- TODO move this down?

        let env' = extendEnv [ id ] [ id' ] [ VO_E op ] env
        Rez body' <- knInline' body env'
        bumpSize (size, Just (id', id))
        -- TODO mkLetVal if id' is dead and bound' is pure?
        residualize $ KNLetVal id' bound' body'

    KNLetRec     ids es  b -> do
        --liftIO $ putStrLn $ "saw rec bindings of " ++ show ids
        ids' <- mapM freshenId ids
        refs <- mapM (\_ -> mkOpRefs) es
        let ops  = map (\(e,(r1,r2,r3)) -> (Opnd e env' r1 r2 r3)) (zip es refs)
            env' = extendEnv ids ids' (map VO_E ops) env
        Rez b'  <- knInline' b env'
        expsiz' <- mapM visitE (zip ids' ops)
        occ_sts <- mapM getVarStatus ids'
        let irrel_ids = [(id, id') | (id, id' , occst) <- zip3 ids ids' occ_sts, not (relevant occst id' ) ]
        liftIO $ putDocLn3 $ text "letrec dead ids: " <> pretty irrel_ids
        let (idses'', sizes) = unzip [((id, e'), size)
                                     | (id, (e', size), occst)
                                     <- zip3 ids' expsiz' occ_sts
                                     , notDead occst]
        mapM_ bumpSize (zip sizes (map Just $ zip ids' ids))
        residualize $ mkLetRec idses'' b'

    KNLetFuns    ids fns0 b -> do
        --liftIO $ putStrLn $ "saw fun bindings of " ++ show ids
        ids' <- mapM freshenId ids

        -- Rename the fnVar so we don't get duplicate procedure names.
        -- TODO would this be a good place to rename procedures to reflect scoping?
        let fns = map (\(f, id) -> f { fnVar = mkGlobalWithType (tidType $ fnVar f) id } )
                      (zip fns0 ids' )
        refs <- mapM (\_ -> mkOpRefs) fns

        let ops  = map (\(f,(r1,r2,r3)) -> (Opnd f env' r1 r2 r3)) (zip fns refs)
            env' = extendEnv ids ids' (map VO_F ops) env

        Rez b' <- knInline' b env'

        liftIO $ do
          putDocLn4 $ text "KNLetFuns " <> pretty ids
          putDocLn4 $ indent 8 $ text "inlined"
          putDocLn4 $ indent 16 $ pretty b
          putDocLn4 $ indent 8 $ text "to"
          putDocLn4 $ indent 16 $ pretty b'
          putDocLn4 $ indent 8 $ text "; now looking at the fns bound to " <> pretty ids

        mb_fns  <- mapM (visitF "KNLetFuns.2") ops
        occ_sts <- mapM getVarStatus ids'
        --let irrel_ids = [(id, id') | (id, id' , occst) <- zip3 ids ids' occ_sts, not (relevant occst id' ) ]
        --if (not $ null $ irrel_ids)
        --  then liftIO $ putDocLn $ text "letfuns dead ids: " <> pretty irrel_ids
        --  else return ()
        let fns' = map (\(fn, mb_fn) ->
                         case mb_fn of Cached _ f sz -> (f,sz)
                                       Failed _ -> error $ "KNExpr.hs: One or more recursive functions failed to residualize during inlining!"
                                                       ++ "\n" ++ show (tidIdent $ fnVar fn))
                   (zip fns mb_fns)
        let (idfns'', szs'') = unzip [((id, fn), sz)
                                     |((id, (fn, sz)), occst) <- zip (zip ids' fns' ) occ_sts
                                     , notDead occst]
        mapM_ bumpSize (zip szs'' (map Just $ zip ids' ids))
        residualize $ mkLetFuns idfns'' b'

    KNCallPrim sr ty prim vs -> do
        -- If enough is known about the values to the prim,
        -- we might be able to partially evaluate it.

        mb_consts <- mapM (extractConstExpr env) vs
        case evalPrim ty prim mb_consts of
             Just e  -> residualize e
             Nothing -> rezM1 (KNCallPrim sr ty prim) (mapM q vs)

    KNCall ty v vs -> do
      let resExpr s why = do --putDocLn $ text "resExpr " <> text s <$> indent 4 (pretty expr)
                             eff <- knTotalEffort
                             rezM2 (\v xs -> KNNotInlined (s,(why,eff,Nothing)) (KNCall ty v xs)) (qs ("KNCall v " ++ show s) v) (mapM (qs "KNCall vs") vs)
      let resExprA s why mb_cost = do --putDocLn $ text "resExprA " <> text s <$> indent 4 (pretty expr)
                          eff <- knTotalEffort
                          rezM2 (\v xs -> KNNotInlined (s,(why,eff,mb_cost)) (KNCall ty v xs)) (qs ("KNCall v " ++ show s) v) (mapM (qs "KNCall vs") vs)
      (_desc, _smry) <- case lookupVarOp env v of
                        Just (VO_E ope) -> do smry <- summarize ope
                                              return ("(a known expr); summary: ",
                                                        smry <$> pretty (opndOldValue ope))
                        Nothing         -> do return ("Nothing", text "")
                        Just (VO_F opf) -> do smry <- summarize opf
                                              return ("(a known fn); summary: ",
                                                       text "rec:" <> pretty (fnIsRec (opndOldValue opf))
                                                   <$> text "           " <> smry)
      --putDocLn7 $ text ("saw call of var " ++ show (tidIdent v)
      --                          ++ " ~?~> " ++ show (lookupVarMb v env) ++ "  ")
      --                     <>  text desc <+> smry
      --                     <$> text "\t\t@ call site:  [[ " <> pretty expr <> text " ]]"

      -- ``v`` is the binding for the function;
      -- ``v'`` is the alias at which it is called.
      -- Checking both names permits a hacky form of per-call-site inlining prevention.
      let maybeInlineCall opf v v' = do
           let shouldNotInline nm = "noinline_" `isPrefixOf` nm
           if shouldNotInline (show $ tidIdent v) || shouldNotInline (show $ tidIdent v')
             then do _ <- visitF "noinline" opf -- don't inline this function...
                     resExpr "noinline" FoldCallSiteOptOut

             else do handleCallOfKnownFunction expr resExprA opf v vs env qs

      case lookupVarOp env v of
        -- Peek through type applications...
        Just (VO_E (Opnd (KNTyApp _ v' []) _ _ _ _)) -> peekTyApps v'
          where peekTyApps v' =
                  case lookupVarOp env v' of
                    Just (VO_E (Opnd (KNTyApp _ v'' []) _ _ _ _)) -> peekTyApps v''
                    Just (VO_E  _) -> resExpr "tv-Just_VO_E" FoldNoBinding
                    Nothing        -> resExpr "tv-Nothing"   FoldNoBinding
                    Just (VO_F _) -> inlineBitcastedFunction v' ty vs env

        -- ...and variable rebindings...
        Just (VO_E (Opnd (KNVar v'0) _ _ _ _)) -> peekRebinding v'0
          where peekRebinding v' = do
                  putDocLn4 $ text $ "peeking through " ++ show v'
                  case lookupVarOp env v' of
                    Just (VO_E (Opnd (KNVar v'') _ _ _ _)) ->
                        if tidIdent v' == tidIdent v''
                          then do putDocLn4 $ text $ "var op was self-bound, residualizing call"
                                  resExpr "formal" FoldNoBinding -- formal parameters are self-bound when inlining
                          else do putDocLn4 $ text $ "peeking in turn through rebinding to " ++ show v''
                                  peekRebinding v''
                    Just (VO_E  _)  -> do putDocLn4 $ text $ "var op was VO_E (residualizing call)"
                                          resExpr "xv-Just_VO_E" FoldNoBinding
                    Nothing         -> do putDocLn4 $ text $ "var op was Nothing (residualizing call)"
                                          resExpr "xv-Nothing"   FoldNoBinding
                    Just (VO_F opf) -> do putDocLn4 $ text $ "var op was VO_F (maybe inlining call)"
                                          maybeInlineCall opf v v'

        -- If the callee isn't a known function, we can't possibly inline it.
        Just (VO_E _oe) -> do resExpr "ne-Just_VO_E_" FoldNoBinding
        Nothing         -> do resExpr "ne-Nothing"    FoldNoBinding

        Just (VO_F opf) -> do maybeInlineCall opf v v

handleCallOfKnownFunction expr resExprA opf@(Opnd fn0 _ _ _ _) v vs env qs = do
 smry <- summarize opf
 when (shouldInspect (tidIdent v) || shouldInspect (fnIdent fn0)) $ do
     putDocLn5 $ text "handleCallOfKnownFunction summarized" <+> text (show $ tidIdent v)
            <$> text "        " <> smry
            <$> text "        " <> pretty (fnIdent fn0)
            <$> text "        " <> pretty (fnIsRec fn0)
            <$> text "        " <> text ("visiting fn opf (" ++ (show $ tidIdent v) ++ ")")
            <$> text "               from call  [[" <+> pretty expr <+> text "]]"
 -- TODO this inhibits useful inlining opportunities
 -- but without it we infinitely loop on .e.g.  bootstrap/testcases/inlining-01
 do
   qvs'   <- mapM (qs "known call vs") vs
   mb_fn' <- visitF "handleCallOfKnownFunction" opf
   case mb_fn' of
    Failed cost -> do
      debugDocLn $ text "visited fn opf (failure!) from call\t" <> pretty expr
      resExprA "visitF failed" FoldInnerPending (Just cost)

    Cached _ fn' _ -> do
      --smry' <- summarize opf
      --putDocLn3 $  text "visited fn opf " <> smry
      --         <$> text "           ==> " <> smry'
      --         <$> text "               from call  [[" <+> pretty expr <+> text "]], producing:"
      --putDocLn3 $ indent 32 $ pretty fn'

      inCenMap <- gets inCallPassCensus >>= readRef
      let inCen v = Map.lookup (tidIdent v) inCenMap

      sizes <- mapM (bestEffortOpSize . lookupVarOp' env) qvs'

      -- Note: here, we're using the original vars, not the fresh ones.
      sizeCounter <- computeSizeCounter v (inCen v) (map inCen vs) sizes

      effortBefore <- knTotalEffort
      levelBefore  <- knInLevel
      --putDocLn7 $ text "handleCallOfKnownFunction trying to fold lambda from call [[" <+> pretty expr <+> text "]]"
      --        <$> text "         with size counter: " <> pretty sizeCounter

      fr_e'  <- catchError (foldLambda' expr fn' opf v qvs' sizeCounter env)
                           (\e -> do putDocLn6 $ text "******* foldLambda aborted inlining of call(size limit " <> text (show sizeCounter) <> text " ): " <> pretty expr <> text (show e)
                                     --putDocLn $ text "called fn was " <> pretty fn'
                                     putDocLn6 $ text $ show (tidIdent v) ++ " w/census " ++ show (inCen v)
                                     let ops = map (lookupVarOp' env) qvs'
                                     mapM_ (\(o,v) -> do smry <- summarizeVarOp o
                                                         putDocLn $ text ("for original arg " ++ show (tidIdent v) ++ ", " ++ " w/census " ++ show (inCen v) ++ "; ") <> smry)
                                           (zip ops vs)
                                     putDocLn6 $ text "called fn sized " <> text (show $ knSize (fnBody fn' ))
                                     effortAfter <- knTotalEffort
                                     return $ case e of
                                       InlineErrorSize   {}  -> FoldFail (FoldSize sizeCounter) expr (Just $ effortAfter - effortBefore)
                                       InlineErrorEffort doc -> FoldFail (FoldEffort doc)       expr (Just $ effortAfter - effortBefore))
      effortAfter <- knTotalEffort

      do st <- get
         let levelref = inCurrentLevel st
         writeRef levelref levelBefore

      putDocLn7 $ text "attempt to fold lambda from call [[" <+> pretty expr <+> text "]]"
                <> text "   with size counter: " <> pretty sizeCounter
                <$> text "level: " <> pretty levelBefore
                <> text "   ;; effort delta: " <> pretty (effortAfter - effortBefore)
                <> text "   ;; resulting size " <> pretty (case fr_e' of FoldInto _ esize _ _ -> esize
                                                                         FoldFail {} -> 0)

      case fr_e' of
         FoldInto (Rez e') esize _ _ -> do
            --when (shouldInspect (fnIdent fn')) $ do
            --    putDocLn $ indent 8 (pretty expr)
            --    putDocLn $ indent 16 (pretty e')
            residualizeCached e' esize

         FoldFail why _ cost -> do
            --when (shouldInspect (fnIdent fn')) $ do
            --    putDocLn $ text "lambda folding [" <> pretty expr <> text "] failed; residualizing call instead."

            resExprA "kNothing" why cost
  where
{- {{{
    primop (NamedPrim tid) = show (tidIdent tid)
    primop (PrimOp nm _)   = nm
    primop (PrimIntTrunc  {}) = "trunc"
    primop (CoroPrim      {}) = "coroprim"
    primop (PrimInlineAsm {}) = "inline-asm"

    mcefHead MCEF_0 = "Nothing" -- E.g. formal with no associated operand.
    mcefHead (MCEF_F _) = "<function>"
    mcefHead (MCEF_E e) = knExprHead e

    knExprHead x = case x of
        KNVar        v   -> "KNVar " ++ show v
        KNLiteral     {} -> "KNLiteral     " ++ show (knSize x)
        KNTuple       {} -> "KNTuple       " ++ show (knSize x)
        KNKillProcess {} -> "KNKillProcess " ++ show (knSize x)
        KNCallPrim _ _ p _ -> "KNCallPrim    " ++      (primop p) -- is zext_* constant enough?
        KNCall        {} -> "KNCall        " ++ show (knSize x)
        KNAppCtor     {} -> "KNAppCtor     " ++ show (knSize x)
        KNAlloc       {} -> "KNAlloc       " ++ show (knSize x)
        KNDeref       {} -> "KNDeref       " ++ show (knSize x)
        KNStore       {} -> "KNStore       " ++ show (knSize x)
        KNAllocArray  {} -> "KNAllocArray  " ++ show (knSize x)
        KNArrayRead   {} -> "KNArrayRead   " ++ show (knSize x)
        KNArrayPoke   {} -> "KNArrayPoke   " ++ show (knSize x)
        KNArrayLit    {} -> "KNArrayLit    " ++ show (knSize x)
        KNTyApp       {} -> "KNTyApp       " ++ show (knSize x)
        KNIf          {} -> "KNIf          " ++ show (knSize x)
        KNLetVal      {} -> "KNLetVal      " ++ show (knSize x)
        KNLetRec      {} -> "KNLetRec      " ++ show (knSize x)
        KNCase        {} -> "KNCase        " ++ show (knSize x)
        KNLetFuns     {} -> "KNLetFuns     " ++ show (knSize x)
        KNCompiles    {} -> "KNCompiles    " ++ show (knSize x)
        KNInlined     {} -> "KNInlined     " ++ show (knSize x)
        KNNotInlined  {} -> "KNNotInlined  " ++ show (knSize x)
}}} -}
    -- input are residual vars, not src vars, fwiw
    foldLambda' :: SrcExpr -> ResFn -> Opnd SrcFn -> TypedId MonoType
                -> [TypedId MonoType] -> SizeCounter -> SrcEnv -> In FoldResult
    foldLambda' expr fn' opnd@(Opnd _ _ _loc_vis loc_op _) _v vs' sizeCounter env = withPendingFold expr $ do
     let fn   = fn'
     let env' = extendEnv ids ids' ops env
                   where
                           ids  = map tidIdent (fnVars fn)
                           ids' = map tidIdent vs'
                           ops  = map (lookupVarOp' env) vs'

     -- ids   are the function's formals;
     -- vs'   are the function's actuals (residual vars)
     -- ops   are the corresponding operand structures.

     before <- knTotalEffort
     o_pending <- readRef loc_op
     case (o_pending, isRec fn && (\(OP_Limit k) -> k) o_pending <= 1) of
       (_, True)  -> do
         putDocLn6 $ text $ ":( :( :( lambda folding aborted for recursive function " ++ show (pretty expr)
         return $ FoldFail FoldRecursive expr (Just 0)
       (OP_Limit 0, _) -> do
         putDocLn6 $ text $ ":( :( :( lambda folding failed due to outer-pending flag for " ++ show (tidIdent $ fnVar fn) ++ " with vars " ++ show (map tidIdent vs') ++ "..."
         return $ FoldFail FoldOuterPending expr Nothing
       (OP_Limit k, _) -> do

         -- Attempt to inline the function body to produce e' ;
         -- if the intermediate result gets too big, the attempt will be
         -- aborted early, and the appropriate call will be residualized
         -- instead. If the attempt succeeds, we must explicitly return the
         -- size, because it must be accounted for in the current size counter.

         visitStatus <- opndVisitStatus opnd
         let (_firstVisit, cachedsize, t0) = case visitStatus of
                                          Unvisited      -> (True, 0, before)
                                          Visited _ n t0 -> (False, n, t0)

         let isVariable (IsConstant {}) = False
             isVariable (IsVariable {}) = True

         putDocLn3 $ text "{{{{{{{{{{{{{{{{{{"
         --putDocLn3 $ text "strt lambda folding for call " <+> pretty expr
         --putDocLn3 $ text $ "            setting outer-pending flag to "
         --                  ++ show (k - 1) ++ " for " ++ show (tidIdent $ fnVar fn) ++ " ;; " ++ show (_firstVisit, cachedsize)
         --putDocLn3 $ indent 16 $ pretty (fnBody fn)

         mb_sizes <- mapM (maybeCachedOpSize . lookupVarOp' env) vs'
         --mb_vars  <- mapM (\v -> do mbe <- maybeCachedEF (lookupVarOp' env v)
         --                           return $ mcefHead mbe) vs'
         constnts <- mapM (extractConstExpr' env) vs'

         let noConstants = all isVariable constnts || (null vs')
         (notTooBig, currsz, mblim) <- canBumpSizeBy cachedsize
         let tooBig = not notTooBig
         --inDebugStr ("foldLamba.A of " ++ show (fnIdent fn' ) ++ " ; " ++ show mb_vars
         --          ++ "\n               " ++ show constnts ++ " //// " ++ show (noConstants, tooBig, currsz, cachedsize, mblim))
         --inDebugStr ("foldLamba.B of " ++ show (fnIdent fn' ) ++ " ; " ++ show constnts)

         let inlineit = do
                 let needsOuterPendingGuard = _firstVisit || isRec fn
                 when needsOuterPendingGuard (writeRef loc_op $ OP_Limit (k - 1))
                 before <- knTotalEffort
                 stkref <- gets inCurrentPendings
                 stk <- readRef stkref
                 putDocLn3 $ text "attemping lambda fold of [[" <+> pretty expr <+> text "]] with current effort " <>
                                pretty before <> text " and stack " <> pretty stk
                           <$> indent 8 (text ("body of called lambda " ++ show (fnIdent fn') ++ " is:"))
                           <$> indent 8 (pretty (fnBody fn))
                 (Rez e' , size) <-
                    inBracket_' "bracket'" (return ())
                                (withSizeCounter ("foldLambda:"++show (fnIdent fn' )++" "++show (map tidIdent vs' )  ++ " ; " ++ show mb_sizes)
                                                     sizeCounter $
                                                  (knInline' (fnBody fn) env'))
                                (\fail -> do if fail
                                               then do
                                                 after <- knTotalEffort
                                                 when noConstants $ putDocLn6 (text "no-constant failed inlining effort was " <> pretty (after - before)
                                                                    <+> text "for cachedsize-" <> pretty cachedsize
                                                                    <+> text "call" <+> pretty expr <+> text " ;;;; " <> text (show (currsz, mblim)))
                                               else return ()
                                             )
                 when needsOuterPendingGuard
                   (if k == opLimitMax then writeRef loc_op $ OP_Limit k else return ())

                 putDocLn3 $ text $ "done lambda folding; resetting outer-pending flag to "
                                    ++ show k ++ " for " ++ show (tidIdent $ fnVar fn)
                 putDocLn3 $ indent 8 $ text "for call  " <+> pretty expr
                 -- putDocLn3 $ indent 16 $ pretty e'
                 putDocLn3 $ text "}}}}}}}}}}}}}}}}}}"

                 after <- knTotalEffort
                 when noConstants $ putDocLn6 (text "no-constant ok     inlining effort was " <> pretty (after - before)
                                                                    <+> text "for size-" <> pretty size
                                                                    <+> text "call" <+> pretty expr)

                 return $ FoldInto (Rez (KNInlined t0 before after expr e' )) size
                                     expr (after - before)

         case (noConstants, tooBig) of
           (True, True) -> do
              -- If there are no constant arguments being passed to the target,
              -- it won't shrink during inlining, so we can avoid doing the
              -- work of processing it if we know it would fail to residualize.
              putDocLn4 $ text $ "not lambda folding due to assumed size of " ++ show (tidIdent $ fnVar fn) ++ " with vars " ++ show (map tidIdent vs') ++ "..."
              return $ FoldFail (FoldTooBig cachedsize) expr (Just 0)
              {-
           (True, False) -> do
             -- If we decline to inline calls which have no constant args and
             -- are not too big, we will miss out on many opportunities to
             -- eliminate call overhead for e.g. nullary calls.

             -- Simply wrapping the body with args (instead of running knInline')
             -- reduces inlining time roughly in half on pidigits...
             --  ... but also seems to sometimes cause infinite loops/space leaks???
             --  ... hmm, inlined size is 2x rather than 0.5x...
              r <- readRef loc_vis
              let cachedFn = case r of
                                Visited v _ -> v
                                _   -> error $ "KNExpr.hs: no cached fn, sadness"
              uref <- gets inUniqRef
              renamed <- liftIO $ alphaRename' cachedFn uref
              let wrapped = knElimRebinds . mangle $ wrapBodyWithArgs renamed (map KNVar vs' )

              mb_rw <- inlineit
              case mb_rw of
                Nothing -> do
                  putDocLn $ text "inlineit returned Nothing, but we want to wrap body for " <> pretty expr
                  return Nothing
                Just (Rez w, c) -> do
                  if (knSize wrapped) == (knSize w) then
                    return $ Just (Rez wrapped, cachedsize)
                  else do
                    putDocLn $ text "inlineit returned thing of different size for " <> pretty expr
                    putDocLn $ indent 8 $ text "inlineit size was " <> pretty c
                    putDocLn $ indent 8 $ text "wrapped  size was " <> pretty cachedsize
                    putDocLn $ indent 8 $ text "inlineit knSize was " <> pretty (knSize w)
                    putDocLn $ indent 8 $ text "wrapped  knSize was " <> pretty (knSize wrapped)
                    return $ Just (Rez w, c)

              --return $ Just (Rez wrapped, cachedsize)
                {-
                    putDocLn3 $ text "********* call had no constants, and wasn't too big to inline... but called too many times"
                            <$> indent 8 (pretty expr)
                            <$> text "~~~~~" <> indent 4 (pretty $ (fnIdent fn):(map tidIdent vs))
                            -- <$> pretty v <> text " ;;;; " <+> text (show (inCen v))
                            -- <$> pretty (fnIdent fn) <> text " ;;;; " <+> text (show (inCen $ fnVar fn))
                     -- TODO check foldRange () problem in bignat.foster
                     -- compiliation time improves from 25s to 5s,
                     -- but this yields terrible performance, not surprisingly.
                    return Nothing
                    -}
                    -- -}
           _ -> do inlineit

-- visitF and visitE return (thing, size), rather than Rez (thing, size),
-- because the returned thing may not actually be residualized by the caller
-- (for example, because the caller finds out it was dead).
data VisitFResult = Cached Bool ResFn Int -- first-cached, size
                  | Failed Int -- cost

visitF :: String -> Opnd SrcFn -> In VisitFResult
visitF msg (Opnd fn env loc_fn _ loc_ip) = do
  ff <- readRef loc_fn
  case ff of
    Unvisited -> do
        ip <- readRef loc_ip
        case ip of
          IP_Limit 0 -> do
            debugDocLn $ text $ "inner-pending limit reached for " ++ show (tidIdent $ fnVar fn)
            return $ Failed 0
          IP_Limit k -> do
            putDocLn5 $ text "visitF(" <> text msg <> text ") called... using no-limit, for fn  "
                    <>  text (show (tidIdent $ fnVar fn)) <> text "  which is:"
                    <$> indent 16 (pretty fn)
            (fn' , size) <- do
                putDocLn7 $ text $ "{{{visiting "++show (fnIdent fn)++ " with no limit (for the first time)"
                inBracket_ ("visitF-IPLimit:" ++ show (fnIdent fn))
                           (writeRef loc_ip (IP_Limit (k - 1)))
                           (withSizeCounter ("visitF:nolimit:"++show (fnIdent fn))
                                            (SizeCounter 0 NoLimit)
                                            (knInlineFn' fn env))
                           (writeRef loc_ip (IP_Limit k))

            when (True || shouldInspect (fnIdent fn)) $ do
                putDocLn7 $ text ("}}}visitED "++show (fnIdent fn)++ " with no limit (for the first time)")
                        <$> indent 16 (pretty fn' )
            after <- knTotalEffort
            writeRef loc_fn (Visited fn' size after)
            return $ Cached True fn' size
    Visited f size _ -> do
      putDocLn6 $ text $ "reusing cached result (size " ++ show size ++ " for fn " ++ show (tidIdent $ fnVar fn)
      putDocLn6 $ indent 32 $ pretty f
      return $ Cached False f size
 where
    knInlineFn' :: SrcFn -> SrcEnv -> In (ResFn)
    knInlineFn' fn env = do
      let vs = fnVars fn
      vs'   <- mapM freshenTid vs
      let foldEnv env (v , v' ) = do
            ope <- mkOpExpr ("knInlineFn' " ++ show (tidIdent v')) (KNVar v' ) env
            return $ extendEnv [tidIdent v] [tidIdent v' ] [ VO_E ope ] env
      env' <- foldlM foldEnv env (zip vs vs' )
      --inDebugStr ("knInlineFn' being called on " ++ show (fnIdent fn))
      Rez body' <- knInline' (fnBody fn) env'
      --inDebugStr ("knInlineFn' called on " ++ show (fnIdent fn))
      return $ fn { fnBody = body' , fnVars = vs' }

{-
wrapBodyWithArgs fn args =
  mkLetVals (zip (map tidIdent $ fnVars fn) args) (fnBody fn)

canInlineMuch (KNLiteral {}) = False
canInlineMuch (KNAlloc {}) = False
canInlineMuch (KNAllocArray {}) = False
canInlineMuch (KNDeref {}) = False
canInlineMuch (KNArrayRead {}) = False
canInlineMuch (KNArrayPoke {}) = False
canInlineMuch (KNCallPrim {}) = False
canInlineMuch _ = True
-}

shouldInspect id = "natIsZero" == show id
                || "arrayIterReverse" `isInfixOf` show id

visitE :: ({-Res-}Ident, Opnd SrcExpr) -> In (ResExpr, Int)
visitE (resid, Opnd e env loc_e _ loc_ip) = do
  ef <- readRef loc_e
  case ef of
    Unvisited -> do
        ip <- readRef loc_ip
        case ip of
          IP_Limit 0 -> do
            -- bootstrap/testcases/rec-ctor-fns triggers this code path.
            debugDocLn $ text "inner-pending true for expr...????"
                           <$> pretty e
            return (KNVar (TypedId (typeKN e) resid), 0)
          IP_Limit k -> do
            -- Using a no-limit size counter results in non-linear processing time,
            -- but we discover more inlining opportunities.
            -- 4963 collections
            (Rez e' , size) <- do
                x <- gets inSizeLimit
                zr <- gets inSizeCntr
                z  <- readRef zr
                {-
                if canInlineMuch e then do
                    --liftIO $ putStrLn $ "visiting expr bound to " ++ show resid ++ " with limit " ++ show x
                    if snd (knSize e) > 4
                      then do putDocLn $ indent 8 $ text "too big, size=" <> pretty (knSize e)
                      else do putDocLn $ indent 8 $ pretty e
                  else do return ()
                  -}

                -- Inline e with the same size limit that's currently in place,
                -- but don't modify the current size counter until/unless we
                -- residualize the result.
                inBracket_ "IPLimit-<expr>"
                           (writeRef loc_ip (IP_Limit $ k - 1))
                           (withSizeCounter ("visitE:")
                                            (SizeCounter z x)
                                            (knInline' e env))
                           (writeRef loc_ip (IP_Limit k))
            after <- knTotalEffort
            writeRef loc_e (Visited e' size after)
            return (e', size)
    Visited r size _ -> do
        return (r, size)

inlineBitcastedFunction :: TypedId MonoType -> MonoType
                        -> [TypedId MonoType] -> SrcEnv -> In (Rez ResExpr)
inlineBitcastedFunction v' ty vs env = do
    -- Some of the formal parameters to the underlying function
    -- may be generically typed. Elsewhere in the compiler, we'll
    -- insert bitcasts around the called function, but when we're
    -- inlining, that won't work -- we need to bitcast every parameter
    -- with a type mismatch (not just those that are PtrTypeUnknown),
    -- and possibly also the result.
    let (FnType tys tyr _ _) = tidType v'
    binders_ref <- newRef []
    vs' <- mapM (\(ty, vorig) -> do
      if ty == tidType vorig
           then return vorig
           else do
                      let e = KNTyApp ty vorig []
                      newid <- freshenId' (Ident (T.pack "castarg") 0)
                      inNewVar newid
                      liftIO $ modIORef' binders_ref (++[(newid, e)])
                      return $ TypedId ty newid
                   ) (zip tys vs)
    binders <- liftIO $ readIORef binders_ref
    -- If we leave a YesTail marker on a call which is, strictly speaking,
    -- not tail due to a pending bitcast of its result, CFG building will
    -- drop the pending bitcast. But we don't need to do tht if the bitcast
    -- would be a no-op. Incidentally, this highlights a slight tension:
    -- fully monomorphizing avoids the need for bitcasts, but risks code blowup.
    if ty == tyr then do knInline' (mkLetVals binders $ KNCall ty  v' vs') env
                 else do newid <- freshenId' (Ident (T.pack "castres") 0)
                         inNewVar newid
                         let vres = TypedId tyr newid
                         knInline' (KNLetVal newid
                                      (mkLetVals binders $ KNCall tyr v' vs')
                                      (KNTyApp ty vres [])) env

-- {{{ Online constant folding
data ConstExpr = Lit            MonoType Literal
               | LitTuple       MonoType [ConstStatus] SourceRange
               | KnownCtor      MonoType (CtorId, CtorRepr) [ConstStatus]
               deriving Show

data ConstStatus = IsConstant (TypedId MonoType) ConstExpr
                 | IsVariable (TypedId MonoType)
                 deriving Show

extractConstExpr :: SrcEnv -> TypedId MonoType -> In ConstStatus
extractConstExpr env var = extractConstExprWith env var lookupVarOp

extractConstExpr' :: SrcEnv -> TypedId MonoType -> In ConstStatus
extractConstExpr' env var = extractConstExprWith env var (\e v -> Just $ lookupVarOp' e v)

extractConstExprWith env var lookup = go var where
  go v =
     case lookup env v of
       (Just (VO_E ope)) -> do
         (e', _) <- visitE (tidIdent v, ope)
         case e' of
            KNLiteral ty lit      -> return $ IsConstant v $ Lit ty lit
            KNTuple   ty vars rng -> do results <- mapM go vars
                                        return $ IsConstant v $ LitTuple ty results rng
            KNAppCtor ty cid vars -> do results <- mapM go vars
                                        return $ IsConstant v $ KnownCtor ty cid results
            -- TODO could recurse through binders
            -- TODO could track const-ness of ctor args
            _                     -> return $ IsVariable v
       _ -> return $ IsVariable v
addBindings [] e = e
addBindings ((id, cs):rest) e = KNLetVal id (exprOfCS cs) (addBindings rest e)

exprOfCS (IsVariable v)                         = KNVar v
exprOfCS (IsConstant _ (Lit ty lit))            = KNLiteral ty lit
exprOfCS (IsConstant _ (KnownCtor ty cid []))   = KNAppCtor ty cid []
exprOfCS (IsConstant _ (KnownCtor ty cid args)) = KNAppCtor ty cid (map varOfCS args)
exprOfCS (IsConstant _ (LitTuple ty args rng))  = KNTuple ty (map varOfCS args) rng

varOfCS (IsVariable v  ) = v
varOfCS (IsConstant v _) = v


-- We'll iterate through the list of arms. Initially, our match status will be
-- NoPossibleMatchYet because we haven't seen any arms at all. If e.g. the first
-- arm we see is a definite match, we'll immediately return those bindings.
-- If the first is a definite non-match, we'll discard it and continue.
-- When we first see an arm which is neither a definite yes or no match,
-- we'll change status to MatchPossible.
-- This prevents us from turning
--           case (v1, c2) of (c3, _) -> a    of (_, _) -> b  end
-- into      case (v1, c2)                    of (_, _) -> b  end
-- because we'll be in state MatchPossible (v1 ~?~ c3).
--
data MatchStatus = NoPossibleMatchYet | MatchPossible
                   deriving Show

data PatternMatchStatus = MatchDef [(Ident, ConstStatus)] | MatchAmbig | MatchNeg
                          deriving Show

-- Given a constant expression c, match against  (p1 -> e1) , ... , (pn -> en).
-- If c definitely matches some pattern pk, return ek.
-- Otherwise, return the list of arms which might possibly match c.
-- TODO handle partial matches:
--        case (a,b) of (True, x) -> f(x)
--      should become
--        case (a,b) of (True, x) -> f(b)
--      even thought it can't become simply ``f(b)`` because a might not be True.
matchConstExpr :: TypedId MonoType -> ConstExpr
               ->            [CaseArm PatternRepr (KNMono) MonoType]
               -> In (Either [CaseArm PatternRepr (KNMono) MonoType]
                             SrcExpr)
matchConstExpr v c arms = go arms [] NoPossibleMatchYet
  where go [] reverseArmsWhichMightMatch _ =
                 -- No conclusive match found, but we can still
                 -- match against only those arms that we didn't rule out.
                return $ Left (reverse reverseArmsWhichMightMatch)

        go (arm@(CaseArm pat e guard _ _):rest) armsWhichMightMatch potentialMatch =
          let rv = matchPatternWithConst pat (IsConstant v c) in
          case (guard, rv, potentialMatch) of
               (Nothing, MatchDef bindings, NoPossibleMatchYet)
                                      -> return $ Right (addBindings bindings e)
               -- We can (in theory) discard arms which definitely won't match,
               -- but pattern match compilation would then think that the match
               -- is incomplete and generate DT_Fail nodes unnecessarily.
               (Nothing, MatchNeg, _) -> go rest (arm:armsWhichMightMatch) potentialMatch
               _                      -> go rest (arm:armsWhichMightMatch) MatchPossible

        nullary True  = MatchDef []
        nullary False = MatchNeg

        -- If the constant matches the pattern, return the list of bindings generated.
        matchPatternWithConst :: PatternRepr ty -> ConstStatus -> PatternMatchStatus
        matchPatternWithConst p cs =
          case (cs, p) of
            (_, PR_Atom (P_Wildcard _ _  )) -> MatchDef []
            (_, PR_Atom (P_Variable _ tid)) -> MatchDef [(tidIdent tid, cs)]
            (IsVariable _  , _)     -> MatchAmbig
            (IsConstant _ c, _)     -> matchConst c p
              where matchConst c p =
                      case (c, p) of
                        (Lit _ (LitInt  i1), PR_Atom (P_Int  _ _ i2)) -> nullary $ litIntValue i1 == litIntValue i2
                        (Lit _ (LitBool b1), PR_Atom (P_Bool _ _ b2)) -> nullary $ b1 == b2
                        (LitTuple _ args _, PR_Tuple _ _ pats) ->
                            let parts = map (uncurry matchPatternWithConst) (zip pats args) in
                            let res = concatMapStatuses parts in
                            res
                            --trace ("matched tuple const against tuple pat " ++ show p ++ "\n, parts = " ++ show parts ++ " ;;; res = " ++ show res) res
                        (KnownCtor _ (kid, _) args, PR_Ctor _ _ pats (LLCtorInfo cid _ _)) | kid == cid ->
                            concatMapStatuses $ map (uncurry matchPatternWithConst) (zip pats args)
                        (_ , _) -> nullary False

        concatMapStatuses :: [PatternMatchStatus] -> PatternMatchStatus
        concatMapStatuses mbs = go mbs []
          where go []               acc = MatchDef (concat acc)
                go (MatchNeg:_)    _acc = MatchNeg
                go (MatchAmbig:_)  _acc = MatchAmbig
                go ((MatchDef xs):rest) acc = go rest (xs : acc)

evalPrim resty (PrimOp "==" _ty)
         [IsConstant _ (Lit _ (LitInt i1)),
          IsConstant _ (Lit _ (LitInt i2))]
                = Just (KNLiteral resty (LitBool $ litIntValue i1 == litIntValue i2))

evalPrim resty (PrimOp  ext _ty)
         [IsConstant _ (Lit _ (LitInt i1))] | ("zext_" `isPrefixOf` ext && litIntValue i1 >= 0)
                                           || ("sext_" `isPrefixOf` ext)
                = Just (KNLiteral resty (LitInt i1))
evalPrim resty (PrimOp  ext _ty)
         [IsConstant _ (Lit _ (LitInt i1))] | ("zext_" `isPrefixOf` ext && litIntValue i1 >= 0)
                                           || ("sext_" `isPrefixOf` ext)
                = Just (KNLiteral resty (LitInt i1))
evalPrim resty (PrimOp  "+" (PrimInt iN))
         [IsConstant _ (Lit _ (LitInt i1))
         ,IsConstant _ (Lit _ (LitInt i2))]
   | iN == I8  = Just (KNLiteral resty (mkLitInt $ i1 `addInt8` i2))
   | iN == I32 = Just (KNLiteral resty (mkLitInt $ i1 `addInt32` i2))
   | iN == I64 = Just (KNLiteral resty (mkLitInt $ i1 `addInt64` i2))
evalPrim resty (PrimOp  "-" (PrimInt iN))
         [IsConstant _ (Lit _ (LitInt i1))
         ,IsConstant _ (Lit _ (LitInt i2))]
   | iN == I8  = Just (KNLiteral resty (mkLitInt $ i1 `subInt8` i2))
   | iN == I32 = Just (KNLiteral resty (mkLitInt $ i1 `subInt32` i2))
   | iN == I64 = Just (KNLiteral resty (mkLitInt $ i1 `subInt64` i2))
-- TODO div , cmp , shifts , bitwise
-- TODO truncation?
-- TODO negate
-- TODO ...
evalPrim _ _ _ = Nothing
--evalPrim _ primop _ = trace ("evalPrim " ++ show primop) Nothing
-- }}}

-- {{{
mkLitInt :: (Integral a, Show a) => a -> Literal
mkLitInt x = LitInt $ mkLiteralIntWithTextAndBase (toInteger x) (show x) 10

wrap2 :: Num num => LiteralInt -> LiteralInt -> (num -> num -> num) -> num
wrap2 liA liB op = op (fromInteger $ litIntValue liA) (fromInteger $ litIntValue liB)

addInt8  a b = wrap2 a b (+) :: Int8
addInt32 a b = wrap2 a b (+) :: Int32
addInt64 a b = wrap2 a b (+) :: Int64
subInt8  a b = wrap2 a b (-) :: Int8
subInt32 a b = wrap2 a b (-) :: Int32
subInt64 a b = wrap2 a b (-) :: Int64
-- }}}

{-
knElimRebinds :: KNExpr' r t -> KNExpr' r t
knElimRebinds expr = go Map.empty expr where
  go :: Map Ident (TypedId t) -> KNExpr' r t -> KNExpr' r t
  go m expr =
    let q e' = go m e' in
    let qv v = case Map.lookup (tidIdent v) m of
                Just v' -> v'
                Nothing -> v in -- :: TypedId t -> TypedId t
    let qai (ArrayIndex v1 v2 sr sg) = ArrayIndex (qv v1) (qv v2) sr sg in
    let qf fn = fn { fnBody = q (fnBody fn) } in
    let qb (CaseArm _pat body mb_guard _binds _rng) =
            CaseArm _pat (q body) (fmap q mb_guard) _binds _rng
            -- We don't replace variables in patterns, because they are binders,
            -- not occurrences.
    in case expr of
            KNVar v -> KNVar (qv v)
            KNLetVal   x (KNVar v) k -> go (Map.insert x v m) k
            KNLetVal   x b    k -> KNLetVal x (q b) (q k)
            KNTyApp t v argtys  -> KNTyApp t (qv v) argtys
            KNKillProcess t m   -> KNKillProcess t m
            KNLiteral t lit     -> KNLiteral t lit
            KNCall    t v vs    -> KNCall   t (qv v) (map qv vs)
            KNCallPrim sr t p vs-> KNCallPrim sr t p (map qv vs)
            KNAppCtor  t cid  vs-> KNAppCtor  t cid  (map qv vs)
            KNLetFuns ids fns k -> KNLetFuns ids (map qf fns) (q k)
            KNLetRec  ids xps e -> KNLetRec  ids (map q xps)  (q e)
            KNIf     _t v b1 b2 -> KNIf     _t (qv v) (q b1) (q b2)
            KNAlloc  _t v rgn   -> KNAlloc  _t (qv v ) rgn
            KNDeref  _t v       -> KNDeref  _t (qv v )
            KNStore  _t v1 v2   -> KNStore  _t (qv v1) (qv v2)
            KNAllocArray t v rg zi -> KNAllocArray t (qv v) rg zi
            KNArrayRead  t ai   -> KNArrayRead  t (qai ai)
            KNArrayPoke  t ai v -> KNArrayPoke  t (qai ai) (qv v)
            KNArrayLit   t arr vals -> KNArrayLit t (qv arr) (mapRight qv vals)
            KNTuple      t vs s -> KNTuple      t (map qv vs) s
            KNCase   _t v bnds  -> KNCase   _t (qv v ) (map qb bnds)
            KNCompiles _r _t e  -> KNCompiles _r _t (q e)
            KNInlined _t0 _to _tn _old new  -> KNInlined _t0 _to _tn _old (q new)
            KNNotInlined x e -> KNNotInlined x (q e)
-}
fmapCaseArm :: (p1 t1 -> p2 t2) -> (e1 -> e2) -> (t1 -> t2) -> CaseArm p1 e1 t1 -> CaseArm p2 e2 t2
fmapCaseArm fp fe ft (CaseArm p e g b rng)
                    = CaseArm (fp p) (fe e) (fmap fe g)
                              [TypedId (ft t) id | TypedId t id <- b] rng

-- The non-local exits in the Chez Scheme inlining algorithm
-- would be very nice to implement using coroutines!
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- {{{||||||||||||||||||||||  Census (for inlining)  |||||||||||||||
-- Some very important inlining decisions are made much more reliable
-- if we can identify which functions are called or passed exactly once.
-- A function which is called at most once can be inlined regardless of
-- the size counter, and a function which is passed exactly once should
-- "donate" its size towards the callee's budget. This latter optimization
-- is extremely important for removing loop abstraction costs!
--
-- We limit the census to non-recursive functions, for now.
--
-- TODO in what situations would this be profitable for recursive
--      functions, which are not already covered by contification?
--
-- There's some redundancy here with census-based optimizations above
-- & in CFG.hs. So it goes.

type NumTimesCalled = Int
type NumTimesPassed = Int

inCensus :: KNMono -> Map Ident (NumTimesCalled, NumTimesPassed)
inCensus expr =
    let InCenState c p _ = execState (inCensusExpr expr)
                                     (InCenState Map.empty Map.empty Map.empty)
    in Map.unionWith (\(a,b) (c,d) -> (a+c, b+d))
                     (Map.map (\v -> (v, 0)) c)
                     (Map.map (\v -> (0, v)) p)

type InCen = State InCenState
data InCenState =  InCenState {
    cenCalled :: Map.Map Ident NumTimesCalled
  , cenPassed :: Map.Map Ident NumTimesPassed
  , cenVarmap :: Map Ident Ident -- for tracking bitcasts...
}

cenLookupId id = do
  st <- get
  return $ Map.findWithDefault id id (cenVarmap st)

cenAddIdRemapping id id' = do
  id'' <- cenLookupId id'
  st <- get
  put $ st { cenVarmap = Map.insert id id'' (cenVarmap st) }

cenSawCandidate id = do
  st <- get
  put $ st { cenPassed = Map.insert id 0 (cenPassed st)
           , cenCalled = Map.insert id 0 (cenCalled st) }

cenSawPassed v = do
  id <- cenLookupId (tidIdent v)
  st <- get
  put $ st { cenPassed = Map.adjust (+1) id (cenPassed st) }

cenSawCalled v = do
  id <- cenLookupId (tidIdent v)
  st <- get
  put $ st { cenCalled = Map.adjust (+1) id (cenCalled st) }

inCensusFn :: Fn RecStatus KNMono MonoType -> InCen ()
inCensusFn fn = do
  mapM_ (cenSawCandidate . tidIdent) (fnVars fn)
  inCensusExpr $ fnBody fn

inCensusExpr :: KNMono -> InCen ()
inCensusExpr expr = go expr where
  go expr = case expr of
    KNCase        _ _ arms     -> do mapM_ go (concatMap caseArmExprs arms)
    KNIf          _ _ e1 e2    -> do go e1 ; go e2
    KNLetVal      id  e1 e2    -> do go e1
                                     case e1 of
                                       (KNTyApp _ v _)
                                         -> cenAddIdRemapping id (tidIdent v)
                                       (KNVar v)
                                         -> cenAddIdRemapping id (tidIdent v)
                                       _ -> return ()
                                     go e2
    KNLetRec      _   es  b    -> do mapM_ go es ; go b
    {-
    KNLetFuns     [id] fns@[fn] b | not (isRec fn) -> do
                                     cenSawCandidate id
                                     mapM_ (go . fnBody) fns
                                     go b
                                     -}
    KNLetFuns     ids fns b    -> do mapM_ cenSawCandidate ids
                                     mapM_ inCensusFn fns
                                     go b

    KNCall     _ v vs -> do cenSawCalled v
                            mapM_ cenSawPassed vs

    KNAppCtor     _ _ vs -> mapM_ cenSawPassed vs
    KNCallPrim  _ _ _ vs -> mapM_ cenSawPassed vs
    KNTuple       _ vs _ -> mapM_ cenSawPassed vs
    KNVar           v    -> mapM_ cenSawPassed [v]
    KNAlloc       _ v _  -> mapM_ cenSawPassed [v]
    KNTyApp       _ v _  -> mapM_ cenSawPassed [v]
    KNStore     _  v1 v2 -> mapM_ cenSawPassed [v1,v2]

    -- Silently handle other cases...
    -- One potential improvement: track variable renamings.
    _ -> return ()

-- }}}


-- {{{||||||||||||||||||||||  Counting src call sites  |||||||||||||||
countCallSites :: KNMono -> Int
countCallSites expr = execState (go expr) 0 where
  go expr = case expr of
    KNCall {} -> do n <- get
                    let !x = n + 1
                    put x
    _ -> mapM_ go (childrenOf expr)

countInliningDecisionPoints :: KNMono -> Int
countInliningDecisionPoints expr = execState (go expr) 0 where
  go expr = case expr of
    KNInlined _ _ _ _ e -> do n <- get
                              let !x = n + 1
                              put x
                              go e
    KNNotInlined _ e    -> do n <- get
                              let !x = n + 1
                              put x
                              go e
    _ -> mapM_ go (childrenOf expr)
-- }}}
