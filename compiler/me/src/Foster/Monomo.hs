{-# LANGUAGE FlexibleContexts, Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Monomo (monomorphize) where

import Prelude hiding ((<$>))

import Foster.Base
import Foster.Kind
import Foster.KNUtil
import Foster.Config
import Foster.MonoType
import Foster.ConvertExprAST()
import Foster.Context
import Foster.Output

import qualified Data.Text as T

import Text.PrettyPrint.ANSI.Leijen

import Data.Map(Map)
import Data.Map as Map(lookup, alter, fromList, union, empty, insert)
import Data.List as List(all)
import Control.Monad(when, liftM, liftM2, liftM3, liftM4)
import Control.Monad.State(evalStateT, get, gets, put, StateT, liftIO, lift)

-- This monomorphization pass is similar in structure to MLton's;
-- a previous worklist-based version was modeled on BitC's polyinstantiator.
--
-- The expression to be monomorphized is a tree of SCCs of function definitions
-- arranged in dependency order. As we descend into the tree, we'll associate
-- each (uniquely named) polymorphic definition with a cache of monomorphized
-- definitions. When we encounter a type application, we'll monomorphize and
-- cache the associated definition. One advantage of doing things this way,
-- rather than using a worklist of function definitions, is that it's much
-- more straightforward to maintain a properly scoped type environment.
--
-- On the way back up the tree, we'll replace each SCC of bindings
-- with the generated monomorphic definitions.

monomorphize :: ModuleIL (KNExpr' ()        TypeIL  ) TypeIL
   -> Compiled (ModuleIL (KNExpr' RecStatus MonoType) MonoType)
monomorphize (ModuleIL body decls dts primdts effdecls lines) = do
    wantedFns <- gets ccDumpFns
    let monoState0 = MonoState Map.empty Map.empty Map.empty [] wantedFns
    flip evalStateT monoState0 $ do
               monobody <- monoKN emptyMonoSubst False body
               specs    <- gets monoDTSpecs
               monodts     <- monomorphizedDataTypesFrom dts specs
               monoprimdts <- monomorphizedDataTypesFrom primdts []
               monodecls <- mapM monoExternDecl decls
               monoeffs  <- monomorphizedEffectDeclsFrom effdecls specs
               return $ ModuleIL monobody monodecls (monodts ++ monoeffs) monoprimdts [] lines


monoPrim :: MonoSubst -> FosterPrim TypeIL -> Mono (FosterPrim MonoType)
monoPrim subst prim = do
  let qt = monoType subst
  case prim of
       NamedPrim tid      -> liftM NamedPrim (monoVar subst tid)
       PrimOp nm ty       -> liftM (PrimOp nm) (qt ty)
       PrimIntTrunc i1 i2 -> return $ PrimIntTrunc i1 i2
       CoroPrim   p t1 t2 -> liftM2 (CoroPrim p) (qt t1) (qt t2)
       PrimInlineAsm ty cnt cns fx -> qt ty >>= \ty' -> return $ PrimInlineAsm ty' cnt cns fx
       LookupEffectHandler tag -> return $ LookupEffectHandler tag

monoVar :: MonoSubst -> TypedId TypeIL -> Mono (TypedId MonoType)
monoVar subst v = do
  liftTID (monoType subst) v

monoKN :: MonoSubst -> Bool -> (KNExpr' () TypeIL) -> Mono (KNExpr' RecStatus MonoType)
monoKN subst inTypeExpr e =
 let qt = monoType subst
     qv = monoVar subst
     qp = monoPrim subst -- avoid need for RankNTypes...
     qa = liftArrayIndexM qv
     qq = monoKN subst inTypeExpr
     generic t = case kindOf t of KindPointerSized -> return PtrTypeUnknown
                                  _                -> qt t
 in
 case e of
  -- These cases are trivially inductive.
  KNLiteral       t lit    -> liftM2 KNLiteral       (qt t) (return lit)
  KNTuple         t vs a   -> liftM3 KNTuple         (qt t) (mapM qv vs) (return a)
  KNKillProcess   t s      -> liftM2 KNKillProcess   (qt t) (return s)
  KNCallPrim   sr t p vs   -> liftM3(KNCallPrim sr)  (qt t) (qp p) (mapM qv vs)
  KNAllocArray    t v amr zi -> liftM4 KNAllocArray    (qt t) (qv v) (return amr) (return zi)
  KNAlloc         t v amr  -> liftM3 KNAlloc         (qt t) (qv v) (return amr)
  KNDeref         t v      -> liftM2 KNDeref         (qt t) (qv v)
  KNStore         t v1 v2  -> liftM3 KNStore         (qt t) (qv v1) (qv v2)
  KNArrayRead     t ai     -> liftM2 KNArrayRead     (qt t) (qa ai)
  KNArrayPoke     t ai v   -> liftM3 KNArrayPoke     (qt t) (qa ai) (qv v)
  KNArrayLit      t arr xs -> liftM3 KNArrayLit      (qt t) (qv arr) (mapRightM qv xs)
  KNVar                  v -> liftM  KNVar                  (qv v)
  KNCompiles    r t e      -> liftM2 (KNCompiles r) (qt t) (qq e)
  KNCall          t v vs   -> do t' <- qt t
                                 let t'' = substRefinementArgs v t' vs
                                 --liftIO $ putStrLn "ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ"
                                 --liftIO $ putStrLn $ show t'
                                 --liftIO $ putStrLn $ show t''
                                 liftM2 (KNCall t'') (qv v) (mapM qv vs)
  KNInlined {}    -> error $ "Monomo.hs expects inlining to run after monomorphization!"
  KNNotInlined {} -> error $ "Monomo.hs expects inlining to run after monomorphization!"
  KNRelocDoms ids e -> liftM (KNRelocDoms ids) (qq e)
  -- The cases involving sub-expressions are syntactically heavier,
  -- but are still basically trivially inductive.

  KNCase          t v pats -> do liftM3 KNCase          (qt t) (qv v)
                                         (mapM (monoPatternBinding subst) pats)
  KNIf            t v e1 e2-> do liftM4 KNIf (qt t) (qv v) (qq e1) (qq e2)
  KNLetVal       id e   b  -> do case e of KNAppCtor {} -> monoAddCtorOrigin id
                                           _ -> return ()
                                 [e' , b' ] <- mapM qq [e, b]
                                 return $ KNLetVal      id e'  b'
  KNLetRec     ids exprs e -> do (e' : exprs' ) <- mapM qq (e:exprs)
                                 return $ KNLetRec      ids exprs' e'

  -- Handlers are conceptually in the above trivial-ish-sub-expression category,
  -- but we glom on the compilation/translation to coroutine primitives here,
  -- since monomorphization lets us get precise type distinctions in polymorphic code.

  KNHandler annot t fx e pats mbx (resumeid, resumebareid) -> do
    t' <- qt t
    fx' <- qt fx
    e' <- qq e
    pats' <- mapM (monoPatternBinding subst) pats
    mbx' <- liftMaybe qq mbx

    liftIO $ putDocLn $ text ""
    liftIO $ putDocLn $ text "KNHandler for " <$> prettyWithLineNumbers (rangeOf annot)
    liftIO $ putDocLn $ text "      had inferred effect " <> pretty fx
    liftIO $ putDocLn $ text "      had value    type   " <> pretty t <> text " monomorphized to " <> pretty t'
    liftIO $ putDocLn $ text "      had action   type   " <> pretty (typeKN e)
    liftIO $ putDocLn $ text ""

    unitid <- lift $ ccFreshId $ T.pack "unit"
    gofnidL <- lift $ ccFreshId $ T.pack "effect_handler.go"
    let Ident prefix uniq = gofnidL
    gofnidG <- return $ GlobalSymbol (T.pack ("_" ++ T.unpack prefix ++ "/" ++ show uniq)) NoRename
    actionid   <- lift $ ccFreshId $ T.pack "action"

    let Ident resprefix resuniq = resumeid
    let Ident resbareprefix resbareuniq = resumebareid
    resumeidG <- return $ GlobalSymbol (T.pack ("_" ++ T.unpack resprefix ++ "/" ++ show resuniq)) NoRename
    resumebareidG <- return $ GlobalSymbol (T.pack ("_" ++ T.unpack resbareprefix ++ "/" ++ show resbareuniq)) NoRename

    gencoroid  <- lift $ ccFreshId $ T.pack "gencoro"

    let boolty = boolMonoType
    let resumeargty = t'
    let inputargty = PtrTypeUnknown
    let coroty = CoroType inputargty resumeargty
    let fnty = FnType [coroty, resumeargty] inputargty FastCC FT_Func -- arg types are a lie, for now...
    let i64 = PrimInt I64
    --liftM3 (KNHandler t' ) (qq e) (mapM (monoPatternBinding subst) pats) (liftMaybe qq mbe)

    gofn <- do
      coroid <- lift $ ccFreshId $ T.pack "corox"
      argid  <- lift $ ccFreshId $ T.pack "argx"
      ylded  <- lift $ ccFreshId $ T.pack "yielded"
      isded  <- lift $ ccFreshId $ T.pack "isdead"
      effectid  <- lift $ ccFreshId $ T.pack "effectid"
      resargid  <- lift $ ccFreshId $ T.pack "resarg"

      -- TODO this is wrong, should use the outty from typechecking.
      let resumefnty = FnType [resumeargty] t' FastCC FT_Func
      let resumefn = Fn (TypedId resumefnty resumeidG) [TypedId PtrTypeUnknown resargid]
                      (KNCall t' (TypedId fnty gofnidL) [TypedId coroty coroid, TypedId resumeargty resargid])
                      NotRec annot
      let resumebarefn = Fn (TypedId resumefnty resumebareidG) [TypedId PtrTypeUnknown resargid]
                      (KNCall t' (TypedId fnty gofnidL) [TypedId coroty coroid, TypedId resumeargty resargid])
                      NotRec annot
      let vs = [TypedId coroty coroid, TypedId inputargty argid]

      --liftIO $ putDocLn $ text "mbx is " <> pretty mbx'
      liftIO $ putStrLn $ "line 179"
      fin <- case mbx' of
                 Nothing -> return (KNVar $ TypedId resumeargty ylded)
                 Just x -> do xformid <- lift $ ccFreshId $ T.pack "xformid"
                              return (KNLetVal xformid x $
                                     (KNCall resumeargty (TypedId (typeKN x) xformid)
                                              [TypedId resumeargty ylded]))
      liftIO $ putStrLn $ "line 186"
      let body = --KNLetVal effectid (KNLiteral unitty (LitText $ T.pack $ show t')) $
                 KNLetVal effectid (KNCallPrim (rangeOf annot) i64 (PrimOp "tag_of_effect" fx') []) $
                 KNLetVal ylded (KNCallPrim (rangeOf annot) resumeargty (CoroPrim CoroInvoke inputargty resumeargty)
                                        [TypedId coroty coroid, TypedId i64 effectid, TypedId inputargty argid]) $
                  KNLetVal isded (KNCallPrim (rangeOf annot) boolty (CoroPrim CoroIsDead inputargty resumeargty)
                                        [TypedId coroty coroid]) $
                  KNIf t' (TypedId boolty isded)
                    fin
                    (KNLetFuns [resumeid, resumebareid] [resumefn, resumebarefn]
                      (KNCase t' (TypedId resumeargty ylded)
                        pats'
                        -- TODO include 'other' branch?
                        ))
      -- Assume recursive, conservatively.
      liftIO $ putStrLn $ "line 201"
      return $ Fn (TypedId fnty gofnidG) vs body YesRec annot

    let unitty = TupleType []
    return $ KNLetFuns [gofnidL] [gofn]
        (KNLetVal unitid (KNTuple unitty [] (rangeOf annot))
        (KNLetVal actionid e'
        (KNLetVal gencoroid (KNCallPrim (rangeOf annot) coroty (CoroPrim CoroCreate inputargty resumeargty)
                          [TypedId (FnType [] t' FastCC FT_Func) actionid])
            (KNCall t' (TypedId fnty gofnidL) [TypedId coroty gencoroid, TypedId unitty unitid]))))

  -- Here are the interesting bits:
  KNAppCtor       t c vs   -> do
    -- Turn (ForAll [('a,KindAnySizeType)]. (TyConAppIL Maybe 'a:KindAnySizeType))
    -- into                                   TyConApp "Maybe" [PtrTypeUnknown]
    t' <- qt t
    case t' of
      StructType {} -> do
        vs' <- mapM qv vs
        return $ KNTuple t' vs' (MissingSourceRange $ "<unboxed ctor:" ++ show c ++ ">")
      TyApp (TyCon dtname) args -> do
        c' <- monoMarkDataType c dtname args
        vs' <- mapM qv vs
        return $ KNAppCtor t' c' vs'
      _ -> error $ "monoKN of KNAppCtor saw unexpected type " ++ show t'

  KNLetFuns     ids fns0 b  -> do
    let fns = computeRecursivenessAnnotations fns0 ids
    let (monos, polys) = split (zip ids fns)



    monoAddOrigins polys
    -- Expose the definitions of the polymorphic
    -- functions for instantiation, then handle
    -- the monomorphic functions.
    ids' <- return              (fst $ unzip monos)
    fns' <- mapM (monoFn subst) (snd $ unzip monos)

    -- Translate the body, which drives further
    -- instantiation of the polymorphics.
    b' <- qq b

    (polyids, polyfns) <- do let (polyids, polyfns) = unzip polys
                             polyfns' <- mapM (monoFn subst) polyfns
                             return (polyids, polyfns' )
    (monoids, monofns) <- monoGatherVersions ids

    when False $ liftIO $ do
      putStrLn $ "monos/polys for " ++ show ids ++ ": " ++ show (fst $ unzip monos, fst $ unzip polys)
      putDoc $ vcat $ [showStructure (tidType (fnVar f)) | f <- snd $ unzip monos]
      putStrLn $ "   polyids: " ++ show polyids
      putStrLn $ "   monoids: " ++ show monoids
      putStrLn $ "   ids':    " ++ show ids'
      {-
      putStrLn $ "fns0:"
      putDoc $ vcat $ map pretty fns0
      putStrLn $ "polys:"
      putDoc $ vcat $ map pretty polys
      putStrLn $ "polyfns:"
      putDoc $ vcat $ map pretty polyfns
      putStrLn $ ""
      -}

    let knFunMarker fn _isCyclic = fn
    let res = mkFunctionSCCs (polyids ++ monoids) (polyfns ++ monofns)
                 (mkKNLetFuns ids'    fns'    b')
                  knFunMarker
                  mkKNLetFuns
            where mkKNLetFuns []  []  b = b
                  mkKNLetFuns ids fns b = KNLetFuns ids fns b

    -- We keep the polymorphic versions around in case they have been
    -- referenceed without being instantiated. If they are dead, they
    -- will be trivially removed during shrinking.
    return $ res

  KNTyApp t v [] -> do -- coercion, rather than a type application per se.
    liftIO $ putStrLn $ "Monomorphizing coercion..."
    liftIO $ putStrLn $ show t
    liftIO $ putStrLn $ show v
    t' <- qt t
    v' <- qv v
    return $ KNTyApp t' v' []

  KNTyApp t (TypedId (ForAllIL ktvs _rho) polybinder) argtys -> do
    monotys <- mapM generic argtys
    let extsubst = extendMonoSubst subst monotys ktvs

    -- For example:     polybinder :: forall x:Type, x => Maybe x
    --                                t   = NatInf(IL) => Maybe NatInf
    t'  <- monoType subst    t    --  t'  = NatInf(Mo) => Maybe NatInf
    t'' <- monoType extsubst _rho --  t'' = PtrTypeUnk => Maybe PtrTypeUnk
    

    -- If we're polymorphically instantiating a global symbol
    -- (i.e. a proc) then we can statically look up the proc
    -- definition and create a monomorphized copy (equally well for
    -- both pointer-sized and types with special calling conventions).
    mb_polydef <- monoGetOrigin polybinder
    case mb_polydef of
       Just (PolyOriginCtor      ) -> do
          return $ bitcast t' (TypedId t'' polybinder)

       Just (PolyOriginFn polydef) -> do
          monobinder <- monoInstantiate polydef polybinder monotys extsubst t''

          whenMonoWanted monobinder $ liftIO $ do
            putDoc $ text "for polybinder " <+> pretty polybinder
                    <+> text " turning into " <+> pretty monobinder
                    <$> text "     with argtys " <+> pretty monotys 
                    <+> text " simplified from " <+> pretty argtys
                    <$> (indent 10 (text "rho is" <+> (align (showStructure _rho))
                    <$>             text "t   is" <+> (align (showStructure t))
                    <$>             text "t'  is" <+> (align (showStructure t'))
                    <$>             text "t'' is" <+> (align (showStructure t'')))) <> line

          -- We need to bitcast the proc we generate because we're
          -- sharing similarly-kinded instantiations, but we want for
          -- the translated return type of id:[T] to be T, not void*.
          return $ bitcast t' (TypedId t'' monobinder)
          -- The real type of the value associated with monoid is not t',
          -- it's really [monotys/ktvs]rho... but we can cheat, for now.
       -- If we're polymorphically instantiating something with a statically
       -- known definition, we can create a monomorphized copy (equally well
       -- for both pointer-sized and types with special calling conventions).

       -- On the other hand, we can't statically monomorphize unknown
       -- variables, but we can use a trivial bitcast if all the type
       -- arguments happen to be pointer-sized.
       Nothing ->
         if List.all (\t -> kindOf t /= KindAnySizeType) monotys || inTypeExpr
                 -- In a type expression, we're not actually going to pass any
                 -- values at runtime, so even if we can't poly-instantiate an
                 -- unknown definition, it's still okay. If all the parameters
                 -- are pointer-sized, though, we can use a generic definition.
            then return $ bitcast t' (TypedId t'' polybinder)
            else error $ "Cannot instantiate unknown function " ++ show polybinder ++ "'s type variables "
               ++ show ktvs
               ++ " with types "
               ++ show argtys
               ++ "\ngenericized to "
               ++ show monotys
               ++ " (of which at least one type is not pointer-sized). "
               ++ "\nFor now, polymorphic instantiation of non-pointer-sized types"
               ++ " is only allowed on functions at the top level!"
               ++ "\nThis is a silly restriction for local bindings,"
               ++ " and could be solved with a dash of flow"
               ++ " analysis,\nbut the issues are much deeper for"
               ++ " polymorphic function arguments"
               ++ " (higher-rank polymorphism)...\n"
            -- -}
  KNTyApp _ _ _  -> do error $ "Expected polymorphic instantiation to affect a polymorphic variable!"

instance Kinded MonoType where
  kindOf x = case x of
    PrimInt     {}     -> KindAnySizeType
    StructType  {}     -> KindAnySizeType

    TyCon       {}     -> KindAnySizeType
    TyApp       {}     -> KindPointerSized

    TupleType   {}     -> KindPointerSized
    CoroType    {}     -> KindPointerSized
    FnType      {}     -> KindPointerSized
    ArrayType   {}     -> KindPointerSized
    PtrType     {}     -> KindPointerSized
    PtrTypeUnknown     -> KindPointerSized
    RefinedType v _ _  -> kindOf (tidType v)

-- TODO this probably needs to traverse inside types to find refinements...
substRefinementArgs _v (RefinedType v e args) xs =
    --trace ("subst in call to " ++ show _v ++ " ..... " ++ show args ++ " with " ++ show xs) $
                       RefinedType v (knSubst (Map.fromList (zip args (map tidIdent xs))) e) args
substRefinementArgs _a t _xs = t

monoFn :: MonoSubst -> Fn RecStatus KNExpr TypeIL -> Mono MonoFn
monoFn subst (Fn v vs body isrec rng) = do
  let qv = monoVar subst
  body' <- monoKN subst False body
  v'  <- qv v
  vs' <- mapM qv vs
  let rv = (Fn v' vs' body' isrec rng)
  --liftIO $ putDocLn $ text "monoFn given input fn " <$> pretty fn <$> string (show (tidType (fnVar fn )))
  --liftIO $ putDocLn $ text "monoFn returning" <$> pretty rv <$> string (show (tidType (fnVar rv )))

  return rv

monoPatternBinding :: MonoSubst -> CaseArm PatternRepr KNExpr TypeIL
                          -> Mono (CaseArm PatternRepr KNMono MonoType)
monoPatternBinding subst (CaseArm pat expr guard vs rng) = do
  pat'   <- monoPattern subst pat
  vs'    <- mapM (monoVar subst) vs
  expr'  <-            monoKN subst False expr
  guard' <- liftMaybe (monoKN subst False) guard
  return (CaseArm pat' expr' guard' vs' rng)

monoPatternAtom subst pattern =
 case pattern of
   P_Wildcard rng t            -> liftM (P_Wildcard rng) (monoType subst t)
   P_Variable rng v            -> liftM (P_Variable rng) (monoVar  subst v)
   P_Bool     rng t b          -> liftM (\t' -> P_Bool rng t' b) (monoType subst t)
   P_Int      rng t i          -> liftM (\t' -> P_Int  rng t' i) (monoType subst t)

monoPattern subst pattern =
 let mp = mapM (monoPattern subst) in
 case pattern of
   PR_Atom           atom       -> liftM  (PR_Atom        ) (monoPatternAtom subst atom)
   PR_Tuple    rng t pats       -> liftM2 (PR_Tuple    rng) (monoType subst t) (mp pats)
   PR_Or       rng t pats       -> liftM2 (PR_Or       rng) (monoType subst t) (mp pats)
   PR_Ctor     rng t pats ctor  -> liftM3 (PR_Ctor     rng) (monoType subst t) (mp pats)
                                                            (monoCtorInfo subst ctor)

monoCtorInfo subst (LLCtorInfo cid repr tys) = do
          tys' <- mapM (monoType subst) tys
          return $ (LLCtorInfo cid repr tys')

monomorphizedEffectDeclsFrom :: [EffectDecl TypeIL] -> [(String, [MonoType])] -> Mono [DataType MonoType]
monomorphizedEffectDeclsFrom eds specs = do
   dts' <- mapM monomorphizedEffectDecls eds
   return $ concat dts'
 where monomorphizedEffectDecl :: EffectDecl TypeIL -> [MonoType] -> Mono (DataType MonoType)
       monomorphizedEffectDecl (EffectDecl name formals ctors range) args = do
                 ctors' <- mapM (monomorphizedEffectCtor subst) ctors
                 return $    (DataType (getMonoFormal name args) []
                                       ctors' False range)
                               where
         subst = extendSubst emptyMonoSubst formals args

         monomorphizedEffectCtor :: MonoSubst -> EffectCtor TypeIL -> Mono (DataCtor MonoType)
         monomorphizedEffectCtor subst (EffectCtor (DataCtor name _tyformals types repr range) _outty) = do
           types' <- mapM (monoType subst) types
           return $ DataCtor name [] types' repr range

       dtSpecMap = mapAllFromList specs

       monomorphizedEffectDecls :: EffectDecl TypeIL -> Mono [DataType MonoType]
       monomorphizedEffectDecls ed@(EffectDecl formal tyformals _ _range) =
         -- We'll always produce the "regular" version of the data type...
         let genericTys = [PtrTypeUnknown | _ <- tyformals] in
         let monotyss = case Map.lookup (typeFormalName formal) dtSpecMap of
                            Nothing -> []
                            Just m  -> m
         in mapM (monomorphizedEffectDecl ed) (monotyss `eqSetInsert` genericTys)

monomorphizedDataTypesFrom :: [DataType TypeIL] -> [(String, [MonoType])] -> Mono [DataType MonoType]
monomorphizedDataTypesFrom dts specs = do
   dts' <- mapM monomorphizedDataTypes dts
   return $ concat dts'
 where monomorphizedDataType :: DataType TypeIL -> [MonoType] -> Mono (DataType MonoType)
       monomorphizedDataType (DataType name formals ctors isForeign range) args = do
                 ctors' <- mapM (monomorphizedCtor subst) ctors
                 return $    (DataType (getMonoFormal name args) []
                                       ctors' isForeign range)
                               where
         subst = extendSubst emptyMonoSubst formals args

         monomorphizedCtor :: MonoSubst -> DataCtor TypeIL -> Mono (DataCtor MonoType)
         monomorphizedCtor subst
                   (DataCtor name _tyformals types repr range) = do
           types' <- mapM (monoType subst) types
           return $ DataCtor name [] types' repr range

       dtSpecMap = mapAllFromList specs

       monomorphizedDataTypes :: DataType TypeIL -> Mono [DataType MonoType]
       monomorphizedDataTypes dt =
         -- We'll always produce the "regular" version of the data type...
         let genericTys = [PtrTypeUnknown | _ <- dataTypeTyFormals dt] in
         let monotyss = case Map.lookup (typeFormalName $ dataTypeName dt) dtSpecMap of
                            Nothing -> []
                            Just m  -> m
         in mapM (monomorphizedDataType dt) (monotyss `eqSetInsert` genericTys)

-- :: (KNExpr' RecStatus MonoType)
bitcast ty v =
  if ty == tidType v
    then KNVar v
    else KNTyApp ty v []

type EqSet t = [t]
eqSetInsert :: Eq t => [t] -> t -> [t]
eqSetInsert [] t = [t]
eqSetInsert zs@(x:_) t | x == t = zs
eqSetInsert (x:xs) t = x:(eqSetInsert xs t)

-- As we monomorphize the program, we'll note which data type instantiations
-- we see; then, at the end, we'll produce specialized versions of the program's
-- data types, according to what arguments the program uses.
monoMarkDataType (cid, repr) dtname monotys = do
  state <- get
  put state { monoDTSpecs = eqSetInsert (monoDTSpecs state) (dtname, monotys) }
  return (cid { ctorTypeName = getMonoName (ctorTypeName cid) monotys }, repr)

monoExternDecl (s, t, isForeign) = liftM (\t' -> (s, t', isForeign)) (monoType emptyMonoSubst t)


-- Monomorphized polymorphic values get different names.
-- The variant in which every type is an opaque pointer keeps the original
-- name; the other variants get distinct names.
cvtMonoId :: {-Poly-} Ident -> [MonoType] -> {-Mono-}  Ident
cvtMonoId id tys =
  if allTypesAreBoxed tys
    then id
    else idAppend id (show tys)

getMonoName nm tys = if allTypesAreBoxed tys then nm else nm ++ (show tys)
getMonoFormal (TypeFormal name sr kind) tys =
               TypeFormal (getMonoName name tys) sr kind

allTypesAreBoxed tys =
          List.all (\t -> case t of { PtrTypeUnknown -> True ; _ -> False }) tys

idAppend id s = case id of (GlobalSymbol o alt) -> (GlobalSymbol (beforeS o) alt)
                           (Ident o m)          -> (Ident (beforeS o) m)
                where beforeS o = o `T.append` T.pack s

-- Given a definition like   polyfn = { forall ...,  body }
-- we want to return an identifier for a suitably monomorphized version.
-- If we've already monomorphized the function, we'll return its procid;
-- otherwise, we'll monomorphize it first.
monoInstantiate :: FnExprIL' -> {-Poly-} Ident
                -> [MonoType]       -> MonoSubst      -> MonoType
                -> Mono ({- Mono -} Ident)
monoInstantiate polydef polybinder
                monotys subst      ty' = do
  let polyprocid = tidIdent $ fnVar polydef
  let monoprocid_raw = cvtMonoId polyprocid monotys
  let monobinder_raw = cvtMonoId polybinder monotys

  prev <- seen monoprocid_raw
  case prev of
    Just monobinder -> do
            return monobinder
    Nothing -> do
       monobinder <- lift $ ccRefreshLocal monobinder_raw
       if polybinder == monobinder
         then return monobinder
         else do
            monoprocid <- lift $ ccRefreshLocal monoprocid_raw
            markSeen monoprocid_raw monobinder
            monodef  <- replaceFnVar monoprocid polydef >>= alphaRenameIL
                                >>= monoFn subst >>= replaceFnVarTy ty'
            monoPutResult polybinder (MonoResult monobinder monodef)
            return monobinder
 where
  replaceFnVarTy ty fn = return fn { fnVar = TypedId ty (tidIdent (fnVar fn)) }

  seen :: MonoProcId -> Mono (Maybe MonoProcId)
  seen id = do state <- get ; return $ Map.lookup id (monoSeenIds state)

  markSeen :: MonoProcId -> MonoProcId -> Mono ()
  markSeen id newid = do
    state <- get
    put state { monoSeenIds = Map.insert id newid (monoSeenIds state) }

  replaceFnVar :: Show t => MonoProcId -> Fn r KNExpr t -> Mono (Fn r KNExpr t)
  replaceFnVar moid fn = do
    whenMonoWanted (tidIdent $ fnVar fn) $ liftIO $ do
      putStrLn $ "polydef fn var:: " ++ show (fnVar fn)
      putStrLn $ "monodef fn var:: " ++ show (TypedId (tidType $ fnVar fn) moid)
    return fn { fnVar = TypedId (tidType $ fnVar fn) moid }


alphaRenameIL :: (Show r2, Pretty r, Pretty r2)
              => Fn r (KNExpr' r2 TypeIL) TypeIL -> Mono (Fn r (KNExpr' r2 TypeIL) TypeIL)
alphaRenameIL fn = do
  fn' <- lift $ alphaRename' fn
  --liftIO $ putDocLn $ text "alphaRename started with" <$> pretty fn <$> string (show (tidType (fnVar fn)))
  --liftIO $ putDocLn $ text "alphaRename turned it into" <$> pretty fn' <$> string (show (tidType (fnVar fn' )))
  return fn'

-- ||||||||||||||||| Monomorphic Type Substitution ||||||||||||||{{{

type MonoSubst = Map TyVar MonoType
emptyMonoSubst = Map.empty

-- Extend the given substitution to map the given TypeFormals to types.
extendSubst subst formals tys =
  let btv (TypeFormal s sr k) = (BoundTyVar s sr, k) in
  extendMonoSubst subst tys (map btv formals)

extendMonoSubst :: MonoSubst -> [MonoType] -> [(TyVar, Kind)] -> MonoSubst
extendMonoSubst subst monotypes ktyvars =
  let tyvarOf (tv, _kind) = tv in
  let ext = Prelude.zip (map tyvarOf ktyvars) monotypes in
  Map.union (Map.fromList ext) subst

monoType :: MonoSubst -> TypeIL -> Mono MonoType
monoType subst ty =
  let q = monoType subst
      qv (TypedId ty id) = do ty' <- q ty ; return (TypedId ty' id) in
  case ty of
     TyConIL nam       -> return $ TyCon nam
     TyAppIL con types -> liftM2 TyApp (q con) (mapM q types)
     PrimIntIL size         -> return $ PrimInt size
     TupleTypeIL KindAnySizeType types -> liftM StructType (mapM q types)
     TupleTypeIL _               types -> liftM TupleType  (mapM q types)
     FnTypeIL  ss t cc cs -> do ss' <- mapM q ss
                                t'  <- q t
                                return $ FnType ss' t' cc cs
     RefinedTypeIL v e args -> do v' <- qv v
                                  e' <- monoKN subst True e
                                  return $ RefinedType v' e' args
     CoroTypeIL s t         -> liftM2 CoroType  (q s) (q t)
     ArrayTypeIL ty         -> liftM  ArrayType (q ty)
     PtrTypeIL ty           -> liftM  PtrType   (q ty)
     -- Type checking should prevent us from trying to instantiate a Boxed
     -- variable with anything but a boxed type.
     ForAllIL ktvs rho    -> monoType (extendMonoSubst subst
                                            [PtrTypeUnknown | _ <- ktvs]
                                                            ktvs) rho
     TyVarIL tv _kind     -> return $ monoSubstLookup subst tv -- TODO check kind?

-- Type variables of pointer-sized kind get translated into
-- opaque pointer types; other type variables are looked up
-- in the type substitution.
monoSubstLookup :: MonoSubst -> TyVar -> MonoType
monoSubstLookup _subst (SkolemTyVar  _ _ KindEffect) = error $ "Monomo.hs: kind effect subst..."
monoSubstLookup _subst (SkolemTyVar  _ _ KindPointerSized) = PtrTypeUnknown
monoSubstLookup _subst (SkolemTyVar  _ _ KindAnySizeType)  =
        --TyConApp ("BAD:SKOLEM TY VAR, ANY SIZE TYPE:"++nm) []
        error $ "Monomorphization (Monomo.hs:monoSubsLookup) "
             ++ "found a bad skolem type variable with non-pointer kind"
monoSubstLookup subst tv@(BoundTyVar _nm _sr) =
  case Map.lookup tv subst of
      Just monotype -> monotype
      Nothing -> if True
                  then --TyConApp ("AAAAAAmissing:" ++ _nm ++ showSourceRange _sr) []
                       PtrTypeUnknown
                  else error $
                         "Monomorphization (Monomo.hs:monoSubsLookup) "
                      ++ "found no monotype for variable " ++ show tv
                      ++ "\nsubst is " ++ show subst
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||| Monadic Helpers ||||||||||||||||||||||{{{
data MonoState = MonoState {
    -- Before instantiating a polymorphic function at a given type,
    -- we first check to see if we've already seen it; if so, then
    -- we don't need to add anything to the work list.
    monoSeenIds :: Map MonoProcId MonoProcId
  , monoOrigins :: Map PolyBinder (PolyOrigin)
  , monoResults :: Map PolyBinder [MonoResult]
  , monoDTSpecs :: EqSet (DataTypeName, [MonoType])
  , monoWantedFns :: [String]
}

type MonoProcId = Ident
type MonoBinder = Ident
type PolyBinder = Ident

data MonoResult = MonoResult MonoProcId MonoFn

type MonoFn    = Fn RecStatus KNMono MonoType
type FnExprIL' = Fn RecStatus KNExpr TypeIL

type Mono = StateT MonoState Compiled

split :: [(Ident, FnExprIL')] -> ([(MonoBinder, FnExprIL')]
                                 ,[(PolyBinder, FnExprIL')])
split idsfns = ( [idfn | (idfn,False) <- aug]
               , [idfn | (idfn,True ) <- aug])
        where aug         = map tri idsfns
              tri (id,fn) = ((id,fn),isInstantiable $ tidType $ fnVar fn)

              isInstantiable (ForAllIL [] t) = isInstantiable t
              isInstantiable (ForAllIL _  _) = True
              isInstantiable _               = False

monoAddCtorOrigin id = do
  state <- get
  put state { monoOrigins = Map.union (monoOrigins state)
                                      (Map.fromList [(id, PolyOriginCtor)]) }

monoAddOrigins :: [(PolyBinder, FnExprIL')] -> Mono ()
monoAddOrigins polys = do
  state <- get
  put state { monoOrigins = Map.union (monoOrigins state)
                                      (Map.fromList [(p, PolyOriginFn f)
                                                    |(p,f) <- polys]) }

data PolyOrigin = PolyOriginFn FnExprIL'
                | PolyOriginCtor

monoGetOrigin :: PolyBinder -> Mono (Maybe PolyOrigin)
monoGetOrigin polyid = do
  state <- get
  return $ Map.lookup polyid (monoOrigins state)

monoPutResult :: PolyBinder -> MonoResult -> Mono ()
monoPutResult polyid result = do
  state <- get
  let addResult (Nothing) = Just $ [result]
      addResult (Just rs) = Just $ result:rs
  put state { monoResults = Map.alter addResult polyid (monoResults state) }

monoGatherVersions :: [PolyBinder] -> Mono ([MonoProcId], [MonoFn])
monoGatherVersions polyids = do
  resultsMap <- gets monoResults
  let results :: PolyBinder -> [(MonoProcId, MonoFn)]
      results polyid = case Map.lookup polyid resultsMap of
                         Nothing -> []
                         Just rs -> map (\(MonoResult mid mfn) -> (mid, mfn)) rs
  return $ unzip $ concatMap results polyids

whenMonoWanted id action = do
  wantedFns <- gets monoWantedFns
  if T.unpack (identPrefix id) `elem` wantedFns
    then action
    else return ()

computeRecursivenessAnnotations fns ids = map annotate fns where
  computeIsFnRec fn ids = computeIsFnRec' (freeIdents fn) ids
  annotate fn = Fn { fnVar   = fnVar fn
                   , fnVars  = fnVars fn
                   , fnBody  = fnBody fn
                   , fnIsRec = (computeIsFnRec fn ids)
                   , fnAnnot = fnAnnot fn
                   }

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
