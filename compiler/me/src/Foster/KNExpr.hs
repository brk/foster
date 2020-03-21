{-# LANGUAGE StandaloneDeriving, BangPatterns, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNExpr (kNormalizeModule, KNExpr, KNMono, FnMono,
                      KNExpr'(..), TailQ(..), typeKN, kNormalize,
                      KNCompilesResult(..),
                      knLoopHeaders, knLoopHeaders',
                      knSinkBlocks, knSize,
                      renderKN, renderKNM, renderKNF, renderKNFM,
                      handleCoercionsAndConstraints,
                      collectIntConstraints) where

import Prelude hiding ((<$>))

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Map(Map)
import Data.List(foldl')
import Data.Maybe(maybeToList, isJust)

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
import Foster.Infer(zonkType)
import Foster.Typecheck(tcTypeWellFormed, tcReplaceQuantifiedVars)

import Text.PrettyPrint.ANSI.Leijen

import qualified Data.Graph.Inductive.Graph            as Graph
import qualified Data.Graph.Inductive.Query.DFS        as Graph
import qualified Data.Graph.Inductive.PatriciaTree     as Graph
import qualified Data.Graph.Inductive.Query.Dominators as Graph

import Control.Monad.State(execStateT, StateT, forM_, liftM, liftM2, get, put, lift)
import Data.IORef(newIORef)

import Data.Maybe (fromMaybe)
import Data.UnionFind.IO(descriptor)

type KN = Tc

knFresh :: String -> KN Ident
--knFresh s = ccFreshId (T.pack s)
knFresh = tcFresh
--knFreshId = tcFreshT

ccFresh s = ccFreshId (T.pack s)

--------------------------------------------------------------------

type KNState = (Context TypeTC
               ,Map String [DataType TypeTC]
               ,Map String [EffectDecl TypeIL]
               ,Map String (DataType TypeIL))
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
    --let eds = Map.fromListWith (++) [(typeFormalName (effectDeclName ed), [ed]) | ed <- moduleILeffectDecls m]
    -- For debugging, try replacing the empty map by a call to error
    -- (after disabling StrictData, presumably).
    let st0 = (ctx, contextDataTypes ctx, Map.empty, Map.empty)
    dts'   <- mapM (convertDT st0) (moduleILdataTypes m)
    prims' <- mapM (convertDT st0) (moduleILprimTypes m)

    wellFormedEffectDeclsTC        (moduleILeffectDecls m)
    effds' <- mapM (convertED st0) (moduleILeffectDecls m)
    wellFormedEffectDeclsIL effds'

    let eds' = Map.fromListWith (++) [(typeFormalName (effectDeclName ed), [ed]) | ed <- effds']

    let allDataTypes = prims' ++ dts'
    let dtypeMap = Map.fromList [(typeFormalName (dataTypeName dt), dt) | dt <- allDataTypes]
    let st = (ctx, contextDataTypes ctx, eds', dtypeMap)
    decls' <- mapM (\(s,t, isForeign) -> do t' <- tcToIL st t ; return (s, t', isForeign)) (moduleILdecls m)
    body' <- do { ctors <- sequence $ concatMap (kNormalCtors st) allDataTypes
                ; effectWrappers <- sequence $ concatMap (kNormalEffectWrappers st) effds'
                ; body  <- kNormalize st (moduleILbody m)
                ; return $ wrapFns (ctors ++ effectWrappers) body
                }
    return $ ModuleIL body' decls' dts' prims' effds' (moduleILsourceLines m)
      where
        wrapFns :: [FnExprIL] -> KNExpr -> KNExpr
        wrapFns fs e = foldr (\f body -> KNLetFuns [fnIdent f] [f] body (rangeOf (fnAnnot f))) e fs

        wellFormedEffectDeclsTC :: [EffectDecl TypeTC] -> Tc ()
        wellFormedEffectDeclsTC effdecls = do mapM_ wellFormedEffectDeclTC effdecls

        wellFormedEffectDeclTC :: EffectDecl TypeTC -> Tc ()
        wellFormedEffectDeclTC effdecl = do
          let extctx = extendTyCtx ctx (map convertTyFormal $ effectDeclTyFormals effdecl)
          forM_ (effectDeclCtors effdecl) $ \ec -> do
            -- Effect decls might only mention some of their type parameters in output types,
            -- which don't appear in the corresponding data type declarations. So we'll manually
            -- check the type formals, which has the side effect of setting their kinds,
            -- which might end up being checked in wellFormedEffectDeclIL.
            tcTypeWellFormed "effect ctor output" extctx (effectCtorOutput ec)

        wellFormedEffectDeclsIL :: [EffectDecl TypeIL] -> Tc ()
        wellFormedEffectDeclsIL effdecls = do mapM_ wellFormedEffectDeclIL effdecls

        wellFormedEffectDeclIL :: EffectDecl TypeIL -> Tc ()
        wellFormedEffectDeclIL effdecl = do
          forM_ (effectDeclCtors effdecl) $ \ec -> do
            case kindOf (effectCtorOutput ec) of
              KindAnySizeType ->
                tcFails [text "The output type for effects must be representable as a pointer."
                        ,text "The effect constructor `"
                                <> text (T.unpack $ dataCtorName (effectCtorAsData ec))
                                <> text "` has an output type, " <> pretty (effectCtorOutput ec)
                                <> text ", which appears non-pointer-sized."
                        ,prettyWithLineNumbers (effectDeclRange effdecl)]
              _ -> return ()


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
    --when (show (tidIdent $ fnVar fn) `elem` ["main", "print_text_bare"]) $ do
    --  let fx = fnTypeTCEffect (tidType (fnVar fn))
    --  tcLift $ putStrLn $ "kNormalizeFn saw fn " ++ show (tidIdent $ fnVar fn) ++ " with type " ++ show (tidType (fnVar fn))
    --  tcLift $ putStrLn $ "kNormalizeFn fx raw " ++ show fx
    --  fx' <- zonkType fx
    --  tcLift $ putStrLn $ "kNormalizeFn fx zonked " ++ show fx'

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
      AnnLiteral annot ty (LitInt int) -> do ailInt qt (rangeOf annot) int ty
      AnnLiteral _rng ty lit  -> do ty' <- qt ty ; return $ KNLiteral ty' lit
      E_AnnVar   _rng (v,_)   -> do v'  <- qv v  ; return $ KNVar v'
      AnnKillProcess _rng t m -> do t'  <- qt t  ; return $ KNKillProcess t' m

      AnnTuple annot _ kind es -> do nestedLets (map go es) (\vs ->
                                      KNTuple (TupleTypeIL kind (map tidType vs)) vs (rangeOf annot))
      AnnAlloc  rng _t a amr  -> do nestedLets [go a] (\[x] -> KNAlloc (PtrTypeIL $ tidType x) x amr (rangeOf rng))
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

      AnnAllocArray rng _ a aty mb_amr zi -> do
            t <- qt aty
            let amr = case mb_amr of
                        Just amr -> amr
                        Nothing  -> MemRegionGlobalHeap
            nestedLets [go a] (\[x] -> KNAllocArray (ArrayTypeIL t) x amr zi (rangeOf rng))

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
            litint = LitInt (LiteralInt (fromIntegral n) 32 (show n))
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
                          return $ KNLetFuns [fn_id] [knFn] fnvar (rangeOf (fnAnnot annFn))

      -- For bound function literals
      AnnLetVar _rng id (E_AnnFn annFn) b -> do
                          knFn <- kNormalizeFn st annFn
                          b' <- go b
                          return $ KNLetFuns [id] [knFn] b' (rangeOf (fnAnnot annFn))

      AnnLetFuns rng ids fns a   -> do
                                knFns <- mapM (kNormalizeFn st) fns
                                liftM (\a' -> KNLetFuns ids knFns a' (rangeOf rng)) (go a)

      AnnLetVar _rng id a b -> do liftM2 (buildLet id) (go a) (go b)
      AnnLetRec _rng ids exprs e  -> do
                    -- Unlike with LetVal, we can't float out the
                    -- inner bindings, because they're presuambly
                    -- defined in terms of the ids being bound.
                    exprs' <- mapM go exprs
                    e'     <- go e
                    return $ KNLetRec ids exprs' e'

      AnnHandler annot t fx e arms mb_xform resumeids -> do
                                  t' <- qt t
                                  fx' <- qt fx
                                  e' <- go e
                                  arms' <- compileHandlerArms arms
                                  mb_xform' <- liftMaybe go mb_xform
                                  if kindOf t' == KindAnySizeType
                                    then tcFails [text "The type of effect-invoking code must (currently) be representable as a pointer."
                                                 ,text "This appears to have the wrong kind: " <> pretty t'
                                                 ,highlightFirstLineDoc (rangeOf annot)]
                                    else return $ KNHandler annot t' fx' e' arms' mb_xform' resumeids

      AnnCase _rng t e arms -> do t' <- qt t
                                  e' <- go e
                                  nestedLetsDo [return e'] (\[v] -> do compileCaseArms arms t' v)
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

                _else -> do knCall ti b args

      AnnAppCtor annot t c es -> do
        let repr = lookupCtorRepr (lookupCtor c)
        t'  <- qt t
        nestedLets (map go es) (\vs -> KNAppCtor  t' (c, repr) vs (rangeOf annot))

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

        compileHandlerArms :: [CaseArm Pattern (AnnExpr TypeTC) TypeTC]
                        -> KN [CaseArm PatternRepr KNExpr TypeIL]
        compileHandlerArms arms = do
          let gtp (CaseArm p e g b r) = do
                p' <- qp p
                e' <- kNormalize st e
                g' <- liftMaybe (kNormalize st) g
                b' <- mapM qv b
                return (CaseArm p' e' g' b' r)
          mapM gtp arms

        -- We currently perform the following source-to-source transformation
        -- on the result of a normalized pattern match:
        --  * Guard splitting:
        --      Every arm with a guard is split into its own pattern match.
        --      The body of the arm turns into
        --          if guard then body else continue-matching !
        --      where continue-matching ! is a lambda containing the
        --      translation of the remaining arms.
        compileCaseArms :: [CaseArm Pattern (AnnExpr TypeTC) TypeTC]
                        -> TypeIL -> TypedId TypeIL
                        -> KN KNExpr
        compileCaseArms arms t v = do
          arms' <- compileHandlerArms arms

          let go (arm:arms) | isGuarded arm = go' [arm] arms
              go allArms = uncurry go' (span (not . isGuarded) allArms)
              -- Compile maximal chunks of un-guarded arms

              go' clump arms = do
                  kid <- knFresh "kont"
                  let kty = FnTypeIL [] t FastCC FT_Proc
                  let kontOf body = Fn {
                          fnVar      = TypedId kty (GlobalSymbol (T.pack $ show kid) NoRename)
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
                          (MissingSourceRange "case-arms")
          if anyCaseArmIsGuarded arms
            then go arms'
            else return $ KNCase t v arms'

        isGuarded arm = isJust (caseArmGuard arm)

        anyCaseArmIsGuarded [] = False
        anyCaseArmIsGuarded (arm:arms) = isGuarded arm || anyCaseArmIsGuarded arms

        lookupCtor :: CtorId -> DataCtor TypeIL
        lookupCtor cid =
            let (_, _, effMap, dtypeMap) = st in
            case Map.lookup (ctorTypeName cid) dtypeMap of
               Just dt -> let
                            [ctor] = filter (\ctor -> dataCtorName ctor == T.pack (ctorCtorName cid))
                                            (dataTypeCtors dt) in
                          ctor
               Nothing ->
                  case Map.lookup (ctorTypeName cid) effMap of
                    Nothing -> error $ "lookupCtor failed for " ++ show cid
                    Just eff ->
                      let
                        [ctor] = filter (\ctor -> dataCtorName ctor == T.pack (ctorCtorName cid))
                                        (map effectCtorAsData $ concatMap effectDeclCtors eff) in
                      ctor

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
            P_Ctor  rng ty pats (CtorInfo cid dc) -> do
                        pats' <- mapM qp pats
                        ty'   <- qt ty
                        let patTys = map typeOf pats'
                        let cinfo' = LLCtorInfo cid (lookupCtorRepr (lookupCtor cid))
                                                patTys (dataCtorLone dc)
                        return $ PR_Ctor rng ty' pats' cinfo'

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
            LookupEffectHandler tag -> return $ LookupEffectHandler tag
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
     TyAppTC (TyConTC "Float32") [] -> return $ TyAppIL (TyConIL "Float32") []
     TyAppTC (TyConTC dtname) tys -> do
         let (_, dtypeMapX, effDeclMapX, _) = st
         case Map.lookup dtname dtypeMapX of
           Just [dt] -> case dtUnboxedRepr dt of
             Nothing -> do iltys <- mapM q tys
                           return $ TyAppIL (TyConIL dtname) iltys
             Just rr -> do rr tys >>= q
           Just dts | length dts > 1
             -> tcFails [text "Multiple definitions for data type" <+> text dtname]
           _ -> case Map.lookup dtname effDeclMapX of
                  Just [_] -> do iltys <- mapM q tys
                                 return $ TyAppIL (TyConIL dtname) iltys
                  Just eds | length eds > 1
                    -> tcFails [text "Multiple definitions for effect " <+> text dtname]
                  _ -> tcFails [text "Unable to find effect" <+> text dtname]
     TyAppTC _ _ -> error $ "tcToIL saw TyApp of non-TyCon"
     PrimIntTC  size    -> do return $ PrimIntIL size
     TupleTypeTC ukind types -> do tys <- mapM q types
                                   kind <- unUnifiedWithDefault ukind KindPointerSized
                                   return $ TupleTypeIL kind tys
     FnTypeTC  ss t _fx cc cs _levels -> do
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
     RefTypeTC  ty       -> do liftM PtrTypeIL (q ty)
     ArrayTypeTC   ty    -> do liftM ArrayTypeIL (q ty)
     ForAllTC  ktvs rho  -> do t <- q rho
                               return $ ForAllIL ktvs t
     TyVarTC  tv@(SkolemTyVar _ _ k) _mbk -> return $ TyVarIL tv k
     TyVarTC  tv@(BoundTyVar _ _sr)  uniK -> do
        --do uk <- unUnified uniK
        --   tcLift $ putDocLn $ red (text "tyVarTC(bound) ") <> pretty typ <> text "  had unifiable kind as " <> pretty uk
        k <- unUnifiedWithDefault uniK KindAnySizeType
        return $ TyVarIL tv k
     MetaTyVarTC m -> do
        mty <- readTcMeta m
        case mty of
          Unbound _-> if mtvIsEffect m
                       then return (TyAppIL (TyConIL "effect.Empty") [])
                       else do {-tcWarn [text $ "Found un-unified unification variable "
                                ++ show (mtvUniq m) ++ "(" ++ mtvDesc m ++ ")!"]-}
                               return $ TupleTypeIL KindPointerSized []
          BoundTo t -> let t' = shallowStripRefinedTypeTC t in
                       -- TODO: strip refinements deeply 
                       q t'
                       {-
                       if show t == show t'
                         then q t'
                         else error $ "meta ty var : " ++ show t ++ " =====> " ++ show t'
-}

-- For datatypes which have been annotated as being unboxed (and are eligible
-- to be so represented), we want to convert from a "data type name reference"
-- to "directly unboxed tuple" representation, since the context which maps
-- names to datatypes will not persist through the rest of the compilation pipeline.
--
dtUnboxedRepr :: DataType TypeTC -> Maybe ([TypeTC] -> Tc TypeTC)
dtUnboxedRepr dt =
  case dataTypeName dt of
    TypeFormal _ _ KindAnySizeType ->
      case dataTypeCtors dt of
        [ctor] -> 
          Just $ \tys ->
                       liftM (TupleTypeTC (UniConst KindAnySizeType))
                          (mapM (substTypeTC tys (dataCtorDTTyF ctor))
                               (dataCtorTypes ctor))
        _ -> Nothing
    TypeFormal _ _ _otherKinds -> Nothing
 where
    substTypeTC :: [TypeTC] -> [TypeFormal] -> TypeTC -> Tc TypeTC
    substTypeTC tys formals = tcReplaceQuantifiedVars mapping
      where mapping = [(BoundTyVar nm rng, ty)
                      | (ty, TypeFormal nm rng _kind) <- zip tys formals]

convertDataCtor f (DataCtor dataCtorName tyformals types repr lone range) = do
  tys <- mapM f types
  return $ DataCtor dataCtorName tyformals tys repr lone range

convertED :: KNState -> EffectDecl TypeTC -> KN (EffectDecl TypeIL)
convertED st (EffectDecl name formals effctors range) = do
  let dctors = [dctor | EffectCtor dctor _ <- effctors]
  let tys    = [ty    | EffectCtor _    ty <- effctors]
  fakeDT <- convertDT st $ DataType name formals dctors False range
  tys' <- mapM (tcToIL st) tys
  let effctors' = [EffectCtor dctor' ty' | (dctor', ty') <- zip (dataTypeCtors fakeDT) tys']
  return $ EffectDecl name formals effctors' range
  
  {-
  ctors' <- mapM (\(EffectCtor dctor ty) -> do
    let f = tcToIL st
    dctor' <- convertDataCtor f dctor
    ty'    <- f ty
    return $ EffectCtor dctor' ty') ctors
  return $ EffectDecl name formals ctors' range
  -}

-- Wrinkle: need to extend the context used for checking ctors!
convertDT :: KNState -> DataType TypeTC -> KN (DataType TypeIL)
convertDT st (DataType dtName tyformals ctors isForeign range) = do
  -- f :: TypeTC -> Tc TypeIL
  let f = tcToIL st
  cts <- mapM (convertDataCtor f) ctors

  optrep <- tcShouldUseOptimizedCtorReprs
  let dt = DataType dtName tyformals cts isForeign range
  let reprMap = Map.fromList $ optimizedCtorRepresesentations dt
  return $ dt { dataTypeCtors = withDataTypeCtors dt (getCtorRepr reprMap optrep) }
    where
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
                Unbound _ -> do writeTcMeta m (PrimIntTC I32)
                                check         (PrimIntTC I32)
                BoundTo tt -> check tt
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

ailInt qt rng int ty = do
  -- 1. We need to make sure that the types eventually given to an int
  --    are large enough to hold it.
  -- 2. For ints with an un-unified meta type variable,
  --    such as from silly code like (let x = 0; in () end),
  --    we should update the int's meta type variable
  --    with the smallest type that accomodates the int.
  case ty of
    PrimIntTC isb -> do
      sanityCheckIntLiteralNotOversized rng (intSizeOf isb) int
      ti <- qt ty
      return $ KNLiteral ti (LitInt int)

    TyAppTC (TyConTC "Int") [] -> do
      -- Big integer literals can't be oversized!
      ti <- qt ty
      return $ KNLiteral ti (LitInt int)

    MetaTyVarTC m -> do
      mty <- readTcMeta m
      case mty of
        BoundTo t -> do ailInt qt rng int t
        Unbound _-> do tcFails [text "Int literal should have had type inferred for it!"]

    RefinedTypeTC v _ _ -> ailInt qt rng int (tidType v)

    TyAppTC (TyConTC "Float32") [] -> do
      sanityCheckIntLiteralNotOversized rng 23 int -- 23 bits in mantisaa, not 32!
      ti <- qt ty
      return $ KNLiteral ti (LitFloat $ LiteralFloat (fromIntegral $ litIntValue int)
                                                     (litIntText int))

    TyAppTC (TyConTC "Float64") [] -> do
      sanityCheckIntLiteralNotOversized rng 53 int -- 53 bits in mantisaa, not 64!
      ti <- qt ty
      return $ KNLiteral ti (LitFloat $ LiteralFloat (fromIntegral $ litIntValue int)
                                                     (litIntText int))

    _ -> do tcFails [text "Unable to assign integer literal the type" <+> pretty ty
                    ,prettyWithLineNumbers rng]

sanityCheckIntLiteralNotOversized rng typeSize int =
    sanityCheck (typeSize >= litIntMinBits int) $
       "Int constraint violated; context-imposed exact size (in bits) was " ++ show typeSize
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
        AnnHandler _rng t fx e arms mb_xform resumeid -> do
                                         ei <- q e
                                         bsi <- mapM (\(CaseArm p e guard bindings rng) -> do
                                                     e' <- q e
                                                     guard' <- liftMaybe q guard
                                                     return (CaseArm p e' guard' bindings rng)) arms
                                         mb_x <- liftMaybe q mb_xform
                                         return $ AnnHandler _rng t fx ei bsi mb_x resumeid
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
    else do ty' <- zonkType ty
            tcFails [text "Kind mismatch:", highlightFirstLineDoc rng
              , text "Cannot instantiate type variable " <> pretty tv <> text " of kind " <> pretty tvkind
              , indent 8 (text "with type " <> pretty ty' <> text " of kind " <> pretty tykind)]


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
                _ <- mapMaybeM collectIntConstraints guard
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
          ty' <- repr ty
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
    KNLetVal x e c _ -> mkKNLetVal x e (buildLet ident c inexpr)

    -- Convert  let f = letfuns g = ... in g in <<f>>
    --     to   letfuns g = ... in let f = g in <<f>>
    KNLetFuns ids fns a sr -> KNLetFuns ids fns (buildLet ident a inexpr) sr

    -- Convert  let i = x in i
    --      to  x
    KNVar _ ->
      case inexpr of
        KNVar v | tidIdent v == ident -> bound
        _                             -> mkKNLetVal ident bound inexpr

    _ -> mkKNLetVal ident bound inexpr


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
          (KNLetFuns ids fns (KNVar v) sr) -> do
            innerlet <- nestedLets' es (v:vars) k
            return $ KNLetFuns ids fns innerlet sr

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
          Right (KNLetFuns ids fns (KNVar v) sr) -> do
            innerlet <- nestedLets' es (Right v:vars) k
            return $ KNLetFuns ids fns innerlet sr

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
    kNormalCtor _datatype (DataCtor _cname _tyformals _tys Nothing _lone _range) = do
      error "Cannot wrap a data constructor with no representation information."

    kNormalCtor datatype (DataCtor cname _tyformals tys (Just repr) _lone range) = do
      let dname = dataTypeName datatype
      let arity = Prelude.length tys
      let cid   = CtorId (typeFormalName dname) (T.unpack cname) arity
      let genFreshVarOfType t = do fresh <- knFresh ".autogen"
                                   return $ TypedId t fresh
      vars <- mapM genFreshVarOfType tys
      let ret tid = return
               Fn { fnVar   = tid
                  , fnVars  = vars
                  , fnBody  = KNAppCtor resty (cid, repr) vars range
                  , fnIsRec = ()
                  , fnAnnot = annotForRange range
                  } where resty =
                            case tidType tid of
                                 FnTypeIL _ r _ _ -> r
                                 ForAllIL _ (FnTypeIL _ r _ _) -> r
                                 _ -> error $ "KNExpr.hs: kNormalCtor given non-function type!"
      let (ctx, _, _, _) = st
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

-- Given::
--     effect E (A1::K1) ... (An::Kn)
--        of E_Op1 (T1::KT1) .. (Tn::KTn) => Tr
--        ...
--  we emit a procedure called ``do_E_Op1`` with body::
--    { args... =>
--      coro = prim lookup_handler_for_effect (E A1 .. An);
--      coro_yield_to coro (Op1 args...)
--    }
--
-- which the program treats as if it has type::
--   forall (A1::K1) ... (An::Kn) { T1 => ... => Tn => Tr @ (E A1 ... An) }
--
--
kNormalEffectWrappers :: KNState -> EffectDecl TypeIL -> [KN (FnExprIL)]
kNormalEffectWrappers st ed = map kNormalEffectWrapper (zip [0..] (effectDeclCtors ed))
  where
    kNormalEffectWrapper :: (Int, EffectCtor TypeIL) -> KN FnExprIL
    kNormalEffectWrapper (n, EffectCtor (DataCtor cname tyformals tys drepr _lone range) outty) = do
      let dname = effectDeclName ed
      let arity = Prelude.length tys
      let cid   = CtorId (typeFormalName dname) (T.unpack cname) arity
      let genFreshVarOfType t = do fresh <- knFresh ".autogen"
                                   return $ TypedId t fresh
      vars <- mapM genFreshVarOfType tys
      coro   <- knFresh ".coro"
      opval  <- knFresh ".opval"
      let effty = TyAppIL (TyConIL $ typeFormalName $ effectDeclName ed)
                          [TyVarIL (BoundTyVar nm sr) kind | TypeFormal nm sr kind <- tyformals]
          coroty = TupleTypeIL KindPointerSized []

      let {- resty = case tidType tid of
                        FnTypeIL _ r _ _ -> r
                        ForAllIL _ (FnTypeIL _ r _ _) -> r
                        _ -> error $ "KNExpr.hs: kNormalCtor given non-function type!"
          -}
          repr = case drepr of
                   Nothing -> CR_Default n
                   Just r  -> r
          effb = case effty of
                   TyAppIL base _ -> base
                   other          -> other
          body = mkKNLetVal opval (KNAppCtor effty (cid, repr) vars (MissingSourceRange "eff-ctor")) -- (KNCallPrim range effty (PrimOp "effect_ctor" effty) vars)
                   (mkKNLetVal coro (KNCallPrim range coroty (PrimOp "lookup_handler_for_effect" effb) [])
                    (KNCallPrim range outty (CoroPrim CoroYield outty effty)
                                            [TypedId coroty coro, TypedId effty opval]))
      let ret tid = return
               Fn { fnVar   = tid
                  , fnVars  = vars
                  , fnBody  = body
                  , fnIsRec = ()
                  , fnAnnot = annotForRange range
                  }
      let (ctx, _, _, _) = st
      let do_cname = T.concat [T.pack "do_", cname]
      case termVarLookup do_cname (contextBindings ctx) of
        Nothing -> error $ "KNExpr.hs: Unable to find binder for effect constructor " ++ show do_cname
        Just (TypedId t id, _) -> do t' <- tcToIL st t
                                     ret (TypedId t' id)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


-- |||||||||||||||||||||||||| Local Block Sinking |||||||||||||||{{{

-- This transformation inserts markers for functions according to
-- their dominator tree.
--
-- Block sinking is needed for contification to work properly;
-- without it, a contifiable function would get contified into an outer scope,
-- which doesn't work (since functions eventually get lifted to toplevel).
-- However, moving closures to inner scopes can change the asympototic allocation
-- profile of a program if the closure ends up not getting contified -- thus,
-- we only insert markers rather than re-locating functions.
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
--
--
-- Brief summary of our algorithm:
--   * Walk the AST, extracting:
--     * Which functions contain which other functions (parent/child relation)
--     * Which identifiers are mentioned in each function
--   * For each function F:
--     * Build a "call" graph in which function identifiers are nodes and mentions are edges.
--       Prune out irrelevant edges by computing the reachable closure from F.
--     * Compute (immediate) dominators for each node in the graph.
--   * Now, comparing the parent/child relation with the dominator relation shows
--     which functions need to be relocated, and where.
--
-- This algorithm, like many recursive functional AST traversals,
-- is unfortunately O(n^2) in the depth of functions being nested.
-- But fortunately n is usually small in programs written by humans.
--
collectFunctions :: Fn RecStatus (KNExpr' RecStatus t) t -> [(Ident, Ident, Fn RecStatus (KNExpr' RecStatus t) t)]  -- (parent, binding, child)
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
          KNRelocDoms  _ e -> go xs e
          KNIf            _ _ e1 e2   -> go (go xs e1) e2
          KNLetVal          _ e1 e2 _ -> go (go xs e1) e2
          KNHandler _ _  _ e1 arms mb_e _ -> let es = concatMap caseArmExprs arms
                                                 ex = case mb_e of
                                                        Nothing -> []
                                                        Just e2 -> [e2] in
                                                   foldl' go xs (ex ++ e1:es)
          KNCase       _ _ arms       -> let es = concatMap caseArmExprs arms in
                                       foldl' go xs es
          KNLetRec     _ es b       -> foldl' go xs (b:es)
          KNLetFuns    ids fns b _sr ->
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
          KNAppCtor     _ _ vs _sr -> uu xs vs
          KNCallPrim  _ _ _ vs -> uu xs vs
          KNVar           v    -> vv xs v
          KNAlloc       _ v _ _sr -> vv xs v
          KNTyApp       _ v _  -> vv xs v
          KNStore     _  v1 v2 -> vv (vv xs v1) v2
          KNCall        _ v vs -> vv (uu xs vs) v
          KNIf          _ v e1 e2   -> go (go (vv xs v) e1) e2
          KNLetVal      _   e1 e2 _ -> go (go xs e1) e2
          KNHandler _ _  _ ea arms mb _ -> let es = concatMap caseArmExprs arms
                                               xx = foldl' go (go xs ea) es in
                                           case mb of
                                             Nothing -> xx
                                             Just ex -> go xx ex
          KNCase        _ v arms    -> let es = concatMap caseArmExprs arms in
                                       foldl' go (vv xs v) es
          KNLetRec     _ es b ->       foldl' go xs (b:es)
          KNLetFuns    _ fns b _sr -> Set.union xs $ go (Set.unions $ map collectMentions fns) b
          KNCompiles _r _t e             -> go xs e
          KNRelocDoms  _  e -> go xs e

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
      KNLetVal      id  e1   e2 _    -> mkKNLetVal id   (q e1)    (q e2)
      KNLetRec      ids es   e       -> KNLetRec   ids (map q es) (q e)
      KNHandler _a ty fx ea arms mbe resumeid -> KNHandler _a ty fx (q ea) (map (fmapCaseArm id q id) arms) (fmap q mbe) resumeid
      KNCase        ty v arms        -> KNCase     ty v (map (fmapCaseArm id q id) arms)
      KNLetFuns     ids fns e sr     -> mkLetFuns (rebuilder (zip ids fns)) (q e) sr
      KNCompiles _r _t e             -> KNCompiles _r _t (q e)
      KNRelocDoms ids e -> KNRelocDoms ids (q e)

mkLetFuns []       e _sr = e
mkLetFuns bindings e  sr = KNLetFuns ids fns e sr where (ids, fns) = unzip bindings

knSinkBlocks :: (Pretty t, Show t) => ModuleIL (KNExpr' RecStatus t) t -> Compiled (ModuleIL (KNExpr' RecStatus t) t)
knSinkBlocks m = do
  let rebuilder idsfns = [(id, localBlockSinking fn) | (id, fn) <- idsfns]
  return $ m { moduleILbody = rebuildWith rebuilder (moduleILbody m) }

localBlockSinking :: (Pretty t, Show t) => Fn RecStatus (KNExpr' RecStatus t) t -> Fn RecStatus (KNExpr' RecStatus t) t
localBlockSinking knf =
    let newfn = rebuildFn knf in
    newfn
      {-
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
              -}
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

  relocationTargets = Map.fromListWith (++) relocationTargetsList

  -- If a function is dominated by a node which is not its parent, relocate it.
  -- relocationTargetsList :: [(Fn (KNExpr' t) t, Ident)]
  relocationTargetsList = [(dom, [(id, f)])
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

  -- Remove unreachable functions.
  rebuilder idsfns =
      [(id, rebuildFn fn)
      |(id, fn) <- idsfns,
       Set.member (fnIdent fn) reachable]

  -- Add new bindings for functions which should be relocated.
  addBindingsFor f body = let (ids, fns) = unzip newfns in
                          let fnMarker fn isCyclic =
                                fn { fnIsRec = if isCyclic then YesRec else NotRec } in
                          let mkLetFuns' ids _fns body =
                                if null ids then body else KNRelocDoms ids body in
                          mkFunctionSCCs ids fns body fnMarker mkLetFuns'
        where
          ourDominatees = case Map.lookup (fnIdent f) relocationTargets of
                              Just xs -> xs
                              _ -> []
          newfns = map (\(id, fn) -> (id, rebuildFn fn)) ourDominatees

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||| Loop Headers |||||||||||||||||||||||{{{

-- Insert loop headers for recursive functions in the program.
--
-- This pass gets called twice during compilation. The first time,
-- it's applied to every function being compiled, in preparation for
-- subsequent inlining/contification. To avoid adding allocations,
-- the first time will look only at tail recursion.
--
-- The second time we'll add loop headers is if we encounter a donatable
-- recursive-but-not-tail-recursive function during inlining -- which only
-- happens if the first pass bailed out. In such cases, there may still be
-- a benefit to adding a loop header that introduces a new allocation,
-- because it should allow at least one donatable parameter to become
-- specialized within the loop, thus offsetting the "cost" of the new alloc.
-- So the second time around, we'll also consider non-tail recursion.
--
-- For each recursive function, we'll look at all the recursive
-- calls it makes, and which arguments each call passes.
--
-- If there's a subset of arguments which are passed at every recursive
-- call, these arguments will be factored out of the loop header
-- and each recursive call.
--
-- Since the (inner) loop header is only called from tail position, it will
-- be contifiable by definition. Note that we must count
-- any occurrences in nested functions as non-tail calls.
--
-- Adding loop headers has two benefits:
--   1) Passing fewer arguments as loop arguments avoids unnecessary copies.
--   2) When inlining is applied, inlining a function wrapped in a loop header
--      corresponds to specializing the recursive function to its arguments,
--      rather than merely unrolling the loop once.
--
-- See Andrew Appel's 1994 paper "Loop Headers in lambda-calculus or CPS"
-- for more examples: http://www.cs.princeton.edu/~appel/papers/460.pdf
--
--
-- Example:
--
-- Consider the case of bytesFoldlFragmentsFromLen, which contains
-- both tail and non-tail recursion; it looks something like
--
--    bytesFoldlFragmentsFromLen = { bytes => f => offset =>
--      case bytes of ... bytesFoldlFragmentsFromLen b1 f offset
--                        bytesFoldlFragmentsFromLen b2 f 0
--    }
--
-- Notably, the bytes argument is never invariant between calls,
-- the f argument is always invariant, and the offset argument is
-- only invariant for non-tail calls.
--
-- We want to transform the function like so:
--    bytesFoldlFragmentsFromLen = { bytes0 => f => offset0 =>
--      nontailheader = { bytes1 => bytes1 =>
--        tailheader = { bytes => offset =>
--          case bytes of ... nontailheader b1 offset
--                            tailheader b2 f 0
--        }; tailheader bytes1 offset1
--      }; nontailheader bytes0 offset0
--    }
--
-- This way, the tailheader will be contified, and the f argument will
-- be specialized when the bytesFoldlFragmentsFromLen wrapper is inlined.
-- Even though the offset parameter is invariant in non-tail calls, it
-- doesn't get dropped from the non-tail header.
--
-- Consider the following function, which has only non-tail recursion:
--
--    fold2 = { f2 => x => b => nullp => car => cdr =>
--      if (nullp x) then b else
--       f2 (car x) (fold2 f2 (cdr x) b nullp car cdr)
--      end
--    };
--
-- Inserting both headers produces
--
--    fold2 = { f2 => x0 => b => nullp => car => cdr =>
--      nontailheader = { x1 =>
--        tailheader = { x =>
--           if (nullp x) then b else
--            f2 (car x) (nontailheader f2 (cdr x) b nullp car cdr)
--           end
--        }; tailheader x1
--      }; nontailheader x0
--    };

type Hdr = StateT HdrState Compiled
data HdrState =   HdrState {
    headers :: LoopHeaders
  , census  :: LoopCensus
  , varmap  :: Map Ident Ident -- for tracking bitcasts...
  , nontail :: Bool
}

-- Map each function's (outer) bound identifier to a fresh id,
-- fresh variables, and a flag indicating whether any tail calls to
-- the function were detected, since we only care about arguments
-- passed to tail calls.
data LoopHeader  = LoopHeader OuterIdent [TypedId MonoType] InnerIdent    OuterIdent InnerIdent
type LoopHeaders = Map Ident (LoopHeader, Bool, Bool) -- tail usages, non-tail usages
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
type LoopInfo = Map Ident LoopSummary
data LoopSummary = LoopSummary LoopHeader [Maybe (TypedId MonoType)] Bool Bool

isAllNothing [] = True
isAllNothing (Nothing:xs) = isAllNothing xs
isAllNothing (_      :_ ) = False

computeInfo :: LoopCensus -> LoopHeaders -> LoopInfo
computeInfo census headers =
    Map.mapMaybeWithKey go census
  where go id mt = let Just (hdr, tailcalled, nontailcalled) = Map.lookup id headers in
                   if tailcalled && (isAllNothing mt || nontailcalled)
                     then Nothing
                     else Just (LoopSummary hdr mt tailcalled nontailcalled)

ccFreshen :: Ident -> Compiled Ident
ccFreshen (Ident name _) = ccFreshId name
ccFreshen id@(GlobalSymbol _ _) = error $ "KNExpr.hs: cannot freshen global " ++ show id
ccFreshenTid (TypedId t id) = do id' <- ccFreshen id
                                 return $ TypedId t id'

mustCont :: Ident -> Bool
mustCont id = identPrefix id `startsWith` T.pack ".cont"
           || identPrefix id `startsWith` T.pack "mustbecont_"
  where startsWith t1 t2 = t2 `T.isPrefixOf` t1

knLoopHeaderCensusFn activeids (id, fn) = do
  if mustCont id
    then return () -- Don't create loop headers for continuation functions!
    else do
      let vars = fnVars fn
      id'    <- lift $ ccFresh  ("mustbecont_hdr." ++ T.unpack (identPrefix (fnIdent fn)) ++ "_")
      id''   <- lift $ ccFresh  ("mustbecont_hdr_"  ++ T.unpack (identPrefix (fnIdent fn)) ++ "_")
      id'nt  <- lift $ ccFresh  ("loop.hdr.nt." ++ T.unpack (identPrefix (fnIdent fn)) ++ "_")
      id''nt <- lift $ ccFresh  ("loophdr.nt."  ++ T.unpack (identPrefix (fnIdent fn)) ++ "_")
      vars' <- lift $ mapM ccFreshenTid vars -- generate new vars for wrapper in advance
      st <- get
      put $ st { headers = Map.insert id ((LoopHeader id' vars' id'' id'nt id''nt), False, False) (headers st)
              , census  = Map.insert id (map Just vars)                              (census st) }
  --trace ("computing loop header census w/ activeids " ++ show activeids ++ " for\n " ++ show (pretty (fnBody fn))) $
  knLoopHeaderCensus YesTail activeids (fnBody fn)

knLoopHeaderCensus :: TailQ -> Set Ident -> KNMono -> Hdr ()
knLoopHeaderCensus tailq activeids expr = go' tailq expr where
  go        expr = go' tailq expr
  go' tailq expr = case expr of
    KNCase        _ _ patbinds -> do mapM_ go (concatMap caseArmExprs patbinds)
    KNIf          _ _ e1 e2    -> do go e1 ; go e2
    KNLetVal      id  e1 e2 _  -> do go' NotTail e1
                                     case e1 of
                                       (KNTyApp _ v _)
                                         -> addIdRemapping id (tidIdent v)
                                       (KNVar v)
                                         -> addIdRemapping id (tidIdent v)
                                       _ -> return ()
                                     go e2
    KNLetRec      _   es  b    -> do mapM_ (go' NotTail) es ; go b
    KNLetFuns     ids fns b _sr -> do
      case () of
        _ | all mustCont ids -> do
          mapM_ (knLoopHeaderCensusFn activeids) (zip ids fns)
          -- We can keep the same activeids for continuations.

        _ | all isRec fns -> do
          mapM_ (knLoopHeaderCensusFn (Set.fromList ids)) (zip ids fns)
          -- Note: when we recur, activeids will not
          -- include the bound ids, so calls in the
          -- body will be (properly) ignored.

        _ -> return ()

      go b

    KNCall _ v vs -> do
      st <- get
      id <- lookupId (tidIdent v)
      if (tailq == YesTail || nontail st) && Set.member id activeids
        then do put $ st { census  = Map.adjust (mergeInfo vs) id (census st)
                         , headers = Map.adjust (\(hdr, ptc, pntc) ->
                                                  (hdr, ptc  || (tailq == YesTail)
                                                      , pntc || (tailq /= YesTail))) id (headers st) }
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
knLoopHeaders m = do body' <- knLoopHeaders' (moduleILbody m) False
                     return $ m { moduleILbody = body' }

knLoopHeaders' :: KNMono -> Bool -> Compiled KNMono
knLoopHeaders' expr addLoopHeadersForNonTailLoops = do
    HdrState h c r _ <- execStateT (knLoopHeaderCensus YesTail Set.empty expr)
                                   (HdrState Map.empty Map.empty Map.empty
                                             addLoopHeadersForNonTailLoops)
    let info = computeInfo c h
    return $ qq info r [] YesTail expr
 where
  qq info r inScopeHeaders tailq expr =
   let qv id = Map.lookup (Map.findWithDefault id id r ) info in
   let q = qq info r inScopeHeaders in
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
    KNRelocDoms ids e -> KNRelocDoms ids (q tailq e)
    KNHandler a  ty fx ea arms mbe resumeid -> KNHandler a ty fx (q NotTail ea) (map (fmapCaseArm id (q tailq) id) arms) (fmap (q tailq) mbe) resumeid
    KNCase        ty v arms     -> KNCase ty v (map (fmapCaseArm id (q tailq) id) arms)
    KNIf          ty v e1 e2    -> KNIf     ty v (q tailq e1) (q tailq e2)
    KNLetVal      id   e1 e2 fe2-> let e1' = q NotTail e1
                                       e2' = q tailq   e2
                                       knz = KNLiteral (PrimInt I1) (LitBool False)
                                       frees = fe2 -- Conservative approximation to freeIdents e2'
                                   in if isPure e1' && not (id `Set.member` frees)
                                       then mkKNLetVal id knz e2' -- see {note 1}
                                       else mkKNLetVal id e1' e2'
    KNLetRec      ids es  b     -> KNLetRec ids (map (q NotTail) es) (q tailq b)
    KNLetFuns     [id] [fn] b sr ->
        case qv id of
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
          Just (LoopSummary (LoopHeader id' vs' id'' id'nt id''nt) mt tc ntc) | tc || ntc -> -- vs' is the complete list of fresh args
            let body   = qq info r (id':id'nt:inScopeHeaders) YesTail $ fnBody fn

                v'inr  = TypedId (selectUsefulArgs id' mt (tidType (fnVar fn))) id'
                v''inr = TypedId (selectUsefulArgs id' mt (tidType (fnVar fn))) id''
                vars   = dropUselessArgs mt (fnVars fn)
                -- The inner, tail-recursive body
                fn'inr = Fn { fnVar   = v''inr
                            , fnVars  = vars
                            , fnBody  = body
                            , fnIsRec = computeIsFnRec' (freeIdentsFn body vars) [id']
                            , fnAnnot = annotForRange (rangeOf fn)
                            }
                
                (v'mid, id'mid, fn'mid) =
                  if addLoopHeadersForNonTailLoops && ntc
                    then
                      let
                        -- The middle, non-tail wrapper
                        v'nt  = TypedId (selectUsefulArgs id' mt (tidType (fnVar fn))) id'nt
                        v''nt = TypedId (selectUsefulArgs id' mt (tidType (fnVar fn))) id''nt
                        body' = if tc
                                  then KNLetFuns [ id' ] [ fn'inr ]
                                        (KNCall (typeKN (fnBody fn)) v'inr (dropUselessArgs mt vs' ))
                                        sr
                                  else body
                        fn'nt = Fn  { fnVar   = v''nt
                                    , fnVars  = vars
                                    , fnBody  = body'
                                    , fnIsRec = computeIsFnRec' (freeIdentsFn body' vars) [id'nt]
                                    , fnAnnot = annotForRange (rangeOf fn)
                                    }
                       in (v'nt, id'nt, fn'nt)
                     else (v'inr, id', fn'inr)

                -- The "original" fn definition, which calls the middle wrapper with the relevant args.
                vars'' = renameUsefulArgs mt vs'
                body'' = KNLetFuns [ id'mid ] [ fn'mid ]
                          (KNCall (typeKN (fnBody fn)) v'mid (dropUselessArgs mt vs' ))
                          sr
                fn' = Fn  { fnVar   = fnVar fn
                          , fnVars  = vars''
                          , fnBody  = body''
                          , fnIsRec = computeIsFnRec' (freeIdentsFn body'' vars'') [id]
                          , fnAnnot = fnAnnot fn
                          } in
            KNLetFuns [id ] [ fn' ] (qq (Map.delete id info) r inScopeHeaders tailq b) sr
              
          -- No loop summary, or summary with no wrapper to generate.
          _ -> KNLetFuns [id] [fn { fnBody = (q YesTail $ fnBody fn) }] (q tailq b) sr
    KNLetFuns     ids fns b sr   ->
        -- If we have a nest of recursive functions,
        -- the replacements should only happen locally, not intra-function.
        -- This is handled by the inScopeHeaders state variable.
        KNLetFuns ids (map (\fn -> fn { fnBody = q YesTail (fnBody fn) }) fns) (q tailq b) sr

    -- If we see a *tail* call to a recursive function, replace it with
    -- the appropriate pre-computed call to the corresponding loop header.
    KNCall ty v vs -> do
      case qv (tidIdent v) of
        Just (LoopSummary (LoopHeader id _ _ idnt _) mt _tc _ntc)
          | (tailq == YesTail || addLoopHeadersForNonTailLoops)
             && id `elem` inScopeHeaders
          ->
             let targetId = if tailq == YesTail then id else idnt in
             KNCall ty (TypedId (selectUsefulArgs targetId mt (tidType v)) targetId)
                       (dropUselessArgs mt vs)
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

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

when True   action = do action
when False _action = return ()

instance CanMakeFun MonoType where
    mkFunType args ret = FnType args ret FastCC FT_Func

fmapCaseArm :: (p1 t1 -> p2 t2) -> (e1 -> e2) -> (t1 -> t2) -> CaseArm p1 e1 t1 -> CaseArm p2 e2 t2
fmapCaseArm fp fe ft (CaseArm p e g b rng)
                    = CaseArm (fp p) (fe e) (fmap fe g)
                              [TypedId (ft t) id | TypedId t id <- b] rng

