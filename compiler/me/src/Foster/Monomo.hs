-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Monomo (monomorphize) where

import Foster.Base
import Foster.Kind
import Foster.KNExpr
import Foster.Config
import Foster.TypeIL
import Foster.MonoType

import qualified Data.Text as T

import Text.PrettyPrint.ANSI.Leijen

import Data.Map(Map)
import Data.Map as Map(insert, lookup, alter, fromList, union, empty)
import Data.Set(Set)
import Data.Set as Set(member, insert, empty)
import Data.List as List(all)
import Control.Monad(liftM, liftM2, when)
import Control.Monad.State(evalStateT, runStateT, get, gets, put, StateT, liftIO)
import Data.IORef

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
monomorphize (ModuleIL body decls dts primdts lines) = do
    uref      <- gets ccUniqRef
    wantedFns <- gets ccDumpFns
    let monoState0 = MonoState Set.empty Map.empty Map.empty [] uref wantedFns
    (monobody, st) <- liftIO $ runStateT (monoKN emptyMonoSubst body) monoState0
    let monodts = monomorphizedDataTypesFrom dts (monoDTSpecs st)
    return $ ModuleIL monobody monodecls monodts monoprimdts lines
      where
        monoprimdts = monomorphizedDataTypesFrom primdts []
        monodecls   = map monoExternDecl decls

mono :: Functor f => MonoSubst -> f TypeIL -> f MonoType
mono subst v = fmap (monoType subst) v

monoKN :: MonoSubst -> (KNExpr' () TypeIL) -> Mono (KNExpr' RecStatus MonoType)
monoKN subst e =
 let qt = monoType subst
     qv = mono subst
     qp = mono subst -- avoid need for RankNTypes...
     qa = fmap qv
     generic t = case kindOf t of KindPointerSized -> PtrTypeUnknown
                                  _                -> qt t
 in
 case e of
  -- These cases are trivially inductive.
  KNLiteral       t lit    -> return $ KNLiteral       (qt t) lit
  KNTuple         t vs a   -> return $ KNTuple         (qt t) (map qv vs) a
  KNKillProcess   t s      -> return $ KNKillProcess   (qt t) s
  KNCall       tc t v vs   -> return $ KNCall       tc (qt t) (qv v) (map qv vs)
  KNCallPrim      t p vs   -> return $ KNCallPrim      (qt t) (qp p) (map qv vs)
  KNAllocArray    t v      -> return $ KNAllocArray    (qt t) (qv v)
  KNAlloc         t v _rgn -> return $ KNAlloc         (qt t) (qv v) _rgn
  KNDeref         t v      -> return $ KNDeref         (qt t) (qv v)
  KNStore         t v1 v2  -> return $ KNStore         (qt t) (qv v1) (qv v2)
  KNArrayRead     t ai     -> return $ KNArrayRead     (qt t) (qa ai)
  KNArrayPoke     t ai v   -> return $ KNArrayPoke     (qt t) (qa ai) (qv v)
  KNVar                  v -> return $ KNVar                  (qv v)
  -- The cases involving sub-expressions are syntactically heavier,
  -- but are still basically trivially inductive.
  KNCase          t v pats -> do pats' <- mapM (monoPatternBinding subst) pats
                                 return $ KNCase          (qt t) (qv v) pats'
  KNUntil         t c b r  -> do [econd, ebody] <- mapM (monoKN subst) [c, b ]
                                 return $ KNUntil      (qt t) econd ebody r
  KNIf            t v e1 e2-> do [ethen, eelse] <- mapM (monoKN subst) [e1,e2]
                                 return $ KNIf         (qt t) (qv v) ethen eelse
  KNLetVal       id e   b  -> do case e of KNAppCtor {} -> monoAddCtorOrigin id
                                           _ -> return ()
                                 [e' , b' ] <- mapM (monoKN subst) [e, b]
                                 return $ KNLetVal      id e'  b'
  KNLetRec     ids exprs e -> do (e' : exprs' ) <- mapM (monoKN subst) (e:exprs)
                                 return $ KNLetRec      ids exprs' e'
  -- Here are the interesting bits:
  KNAppCtor       t c vs   -> do
    -- Turn (ForAll [('a,KindAnySizeType)]. (TyConAppIL Maybe 'a:KindAnySizeType))
    -- into                                   TyConApp "Maybe" [PtrTypeUnknown]
    let t'@(TyConApp dtname args) = qt t
    c' <- monoMarkDataType c dtname args
    return $ KNAppCtor t' c' (map qv vs)

  KNLetFuns     ids fns0 b  -> do
    let fns = computeRecursivenessAnnotations fns0 ids
    let (monos, polys) = split (zip ids fns)

    when False $ liftIO $ do
      putStrLn $ "monos/polys: " ++ show (fst $ unzip monos, fst $ unzip polys)
      putDoc $ vcat $ [showStructure (tidType (fnVar f)) | f <- snd $ unzip monos]

    monoAddOrigins polys
    -- Expose the definitions of the polymorphic
    -- functions for instantiation, then handle
    -- the monomorphic functions.
    ids' <- return              (fst $ unzip monos)
    fns' <- mapM (monoFn subst) (snd $ unzip monos)

    -- Translate the body, which drives further
    -- instantiation of the polymorphics.
    b' <- monoKN subst b

    (monoids, monofns) <- monoGatherVersions ids

    return $ mkFunctionSCCs monoids monofns
                 (KNLetFuns ids'    fns'    b')
                  KNLetFuns

  KNTyApp _ _ [] -> error "Monomo.hs: cannot type-apply with no arguments!"
  KNTyApp t (TypedId (ForAllIL ktvs _rho) polybinder) argtys -> do
    let monotys  = map generic argtys
    let extsubst = extendMonoSubst subst monotys ktvs

    let t'  = monoType subst    t
    let t'' = monoType extsubst _rho

    -- If we're polymorphically instantiating a global symbol
    -- (i.e. a proc) then we can statically look up the proc
    -- definition and create a monomorphized copy (equally well for
    -- both pointer-sized and types with special calling conventions).
    mb_polydef <- monoGetOrigin polybinder
    case mb_polydef of
       Just (PolyOriginCtor      ) -> do
          return $ KNTyApp t' (TypedId t'' polybinder) []

       Just (PolyOriginFn polydef) -> do
          monobinder <- monoInstantiate polydef polybinder monotys extsubst t''

          whenMonoWanted monobinder $ liftIO $ do
            putStrLn $ "for monobinder " ++ show monobinder ++ ", t   is " ++ show t
            putStrLn $ "for monobinder " ++ show monobinder ++ ", t'  is " ++ show t'
            putStrLn $ "for monobinder " ++ show monobinder ++ ", t'' is " ++ show t''

          -- We need to bitcast the proc we generate because we're
          -- sharing similarly-kinded instantiations, but we want for
          -- the translated return type of id:[T] to be T, not void*.
          return $ KNTyApp t' (TypedId t'' monobinder) []
          -- The real type of the value associated with monoid is not t',
          -- it's really [monotys/ktvs]rho... but we can cheat, for now.
       -- If we're polymorphically instantiating something with a statically
       -- known definition, we can create a monomorphized copy (equally well
       -- for both pointer-sized and types with special calling conventions).

       -- On the other hand, we can't statically monomorphize unknown
       -- variables, but we can use a trivial bitcast if all the type
       -- arguments happen to be pointer-sized.
       Nothing ->
          --return $ KNTyApp t' (TypedId t' polybinder) []
          if List.all (\(_tv, kind) -> kind == KindPointerSized) ktvs
            then return $ KNTyApp t' (TypedId t' polybinder) []
            else error $ "Cannot instantiate unknown function " ++ show polybinder ++ "'s type variables "
               ++ show ktvs
               ++ " with types "
               ++ show argtys
               ++ "\ngenericized to "
               ++ show monotys
               ++ "\nFor now, polymorphic instantiation of non-pointer-sized types"
               ++ " is only allowed on functions at the top level!"
               ++ "\nThis is a silly restriction for local bindings,"
               ++ " and could be solved with a dash of flow"
               ++ " analysis,\nbut the issues are much deeper for"
               ++ " polymorphic function arguments"
               ++ " (higher-rank polymorphism)...\n"
            -- -}
  KNTyApp _ _ _  -> do error $ "Expected polymorphic instantiation to affect a polymorphic variable!"

monoFn :: MonoSubst -> Fn RecStatus KNExpr TypeIL -> Mono MonoFn
monoFn subst (Fn v vs body isrec rng) = do
  let qv = mono subst
  body' <- monoKN subst body
  return (Fn (qv v) (map qv vs) body' isrec rng)

monoPatternBinding :: MonoSubst -> CaseArm PatternRepr KNExpr TypeIL
                          -> Mono (CaseArm PatternRepr KNMono MonoType)
monoPatternBinding subst (CaseArm pat expr guard vs rng) = do
  let pat' = monoPattern subst pat
  let vs'  = map (mono subst) vs
  expr'  <-            monoKN subst  expr
  guard' <- liftMaybe (monoKN subst) guard
  return (CaseArm pat' expr' guard' vs' rng)

monoPatternAtom subst pattern =
 case pattern of
   P_Wildcard rng t            -> P_Wildcard rng (monoType subst t)
   P_Variable rng v            -> P_Variable rng (mono     subst v)
   P_Bool     rng t b          -> P_Bool     rng (monoType subst t) b
   P_Int      rng t i          -> P_Int      rng (monoType subst t) i

monoPattern subst pattern =
 let mp = map (monoPattern subst) in
 case pattern of
   PR_Atom           atom       -> PR_Atom         (monoPatternAtom subst atom)
   PR_Tuple    rng t pats       -> PR_Tuple    rng (monoType subst t) (mp pats)
   PR_Ctor     rng t pats ctor  -> PR_Ctor     rng (monoType subst t) (mp pats)
                                                   (monoCtorInfo subst ctor)

monoCtorInfo subst (LLCtorInfo cid repr tys) =
                   (LLCtorInfo cid repr tys')
                where tys'   = map (monoType subst) tys

monomorphizedDataTypesFrom dts specs = concatMap monomorphizedDataTypes dts
 where monomorphizedDataType :: DataType TypeIL -> [MonoType] -> DataType MonoType
       monomorphizedDataType (DataType name formals ctors range) args =
                             (DataType (getMonoFormal name args) []
                                       (map (monomorphizedCtor subst) ctors) range)
                               where
         subst = extendSubst emptyMonoSubst formals args

         monomorphizedCtor :: MonoSubst -> DataCtor TypeIL -> DataCtor MonoType
         monomorphizedCtor subst
               (DataCtor name _tyformals types range) =
                DataCtor name [] (map (monoType subst) types) range

       dtSpecMap = mapAllFromList specs

       monomorphizedDataTypes :: DataType TypeIL -> [DataType MonoType]
       monomorphizedDataTypes dt@(DataType formal tyformals _ _range) =
         -- We'll always produce the "regular" version of the data type...
         let genericTys = [PtrTypeUnknown | _ <- tyformals] in
         let monotyss = case Map.lookup (typeFormalName formal) dtSpecMap of
                            Nothing -> []
                            Just m  -> m
         in map (monomorphizedDataType dt) (monotyss `eqSetInsert` genericTys)

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

monoExternDecl (s, t) = (s, monoType emptyMonoSubst t)

-- Monomorphized polymorphic values get different names.
-- The variant in which every type is an opaque pointer keeps the original
-- name; the other variants get distinct names.
getMonoId :: {-Poly-} Ident -> [MonoType] -> {-Mono-}  Ident
getMonoId id tys =
  if allTypesAreBoxed tys
    then id
    else idAppend id (show tys)

getMonoName nm tys = if allTypesAreBoxed tys then nm else nm ++ (show tys)
getMonoFormal (TypeFormalAST name kind) tys =
               TypeFormalAST (getMonoName name tys) kind

allTypesAreBoxed tys =
          List.all (\t -> case t of { PtrTypeUnknown -> True ; _ -> False }) tys

idAppend id s = case id of (GlobalSymbol o) -> (GlobalSymbol $ beforeS o)
                           (Ident o m)      -> (Ident (beforeS o) m)
                where beforeS o = o `T.append` T.pack s

-- Given a definition like   polyfn = { forall ...,  body }
-- we want to return an identifier for a suitably monomorphized version.
-- If we've already monomorphized the function, we'll return its procid;
-- otherwise, we'll monomorphize it first.
monoInstantiate :: FnExprIL -> {-Poly-} Ident
                -> [MonoType]       -> MonoSubst      -> MonoType
                -> Mono ({- Mono -} Ident)
monoInstantiate polydef polybinder
                monotys subst      ty' = do
  let polyprocid = tidIdent $ fnVar polydef
  let monoprocid = getMonoId polyprocid monotys
  let monobinder = getMonoId polybinder monotys
  have <- seen monoprocid
  if have
   then return monobinder
   else do  markSeen monoprocid
            monodef  <- replaceFnVar monoprocid polydef >>= alphaRename
                                >>= monoFn subst >>= replaceFnVarTy ty'
            monoPutResult polybinder (MonoResult monobinder monodef)
            return monobinder
 where
  replaceFnVarTy ty fn = return fn { fnVar = TypedId ty (tidIdent (fnVar fn)) }

  seen :: MonoProcId -> Mono Bool
  seen id = do state <- get ; return $ Set.member id (monoSeenIds state)

  markSeen :: MonoProcId -> Mono ()
  markSeen id = do state <- get
                   put state { monoSeenIds = Set.insert id (monoSeenIds state) }

  replaceFnVar :: MonoProcId -> Fn r KNExpr TypeIL -> Mono (Fn r KNExpr TypeIL)
  replaceFnVar moid fn = do
    whenMonoWanted (tidIdent $ fnVar fn) $ liftIO $ do
      putStrLn $ "polydef fn var:: " ++ show (fnVar fn)
      putStrLn $ "monodef fn var:: " ++ show (TypedId (tidType $ fnVar fn) moid)
    return fn { fnVar = TypedId (tidType $ fnVar fn) moid }

showFnStructure :: Fn r KNExpr TypeIL -> Doc
showFnStructure (Fn fnvar args body _ _srcrange) =
  pretty fnvar <+> text "=" <+>
                     text "{" <+> hsep (map pretty args)
                 <$> indent 2 (showStructure body)
                 <$> text "}" <> line

alphaRename :: Fn r KNExpr TypeIL -> Mono (Fn r KNExpr TypeIL)
alphaRename fn = do
  uref <- gets monoUniques
  renamed <- liftIO $ evalStateT (renameFn fn) (RenameState uref Map.empty)

  whenMonoWanted (tidIdent $ fnVar fn) $ liftIO $ do
      putDoc $ text "fn:      " <$> showFnStructure fn
      putDoc $ text "renamed: " <$> showFnStructure renamed

  return renamed
   where
    renameV :: TypedId TypeIL -> Renamed (TypedId TypeIL)
    renameV tid@(TypedId _ (GlobalSymbol _)) = return tid
    renameV     (TypedId t id) = do
      state <- get
      case Map.lookup id (renameMap state) of
        Nothing  -> do id' <- renameI id
                       return (TypedId t id' )
        Just _u' -> error "can't rename a variable twice!"

    renameI id@(GlobalSymbol _) = return id
    renameI id@(Ident s _)      = do u' <- fresh
                                     let id' = Ident s u'
                                     remap id id'
                                     return id'
      where
        fresh :: Renamed Uniq
        fresh = do uref <- gets renameUniq ; mutIORef uref (+1)

        mutIORef :: IORef a -> (a -> a) -> Renamed a
        mutIORef r f = liftIO $ modifyIORef r f >> readIORef r

        remap id id' = do state <- get
                          put state { renameMap = Map.insert id id' (renameMap state) }

    qv :: TypedId t -> Renamed (TypedId t)
    qv (TypedId t i) = do i' <- qi i ; return $ TypedId t i'

    qi v@(GlobalSymbol _) = return v
    qi v = do state <- get
              case Map.lookup v (renameMap state) of
                Just v' -> return v'
                Nothing -> return v

    renameFn :: Fn r KNExpr TypeIL -> Renamed (Fn r KNExpr TypeIL)
    renameFn (Fn v vs body isrec rng) = do
       (v' : vs') <- mapM renameV (v:vs)
       body' <- renameKN body
       return (Fn v' vs' body' isrec rng)

    renameArrayIndex (ArrayIndex v1 v2 rng s) =
      mapM qv [v1,v2] >>= \[v1' , v2' ] -> return $ ArrayIndex v1' v2' rng s

    renameKN :: KNExpr -> Renamed KNExpr
    renameKN e =
      case e of
      KNLiteral       {}       -> return e
      KNKillProcess   {}       -> return e
      KNTuple         t vs a   -> mapM qv vs     >>= \vs' -> return $ KNTuple t vs' a
      KNCall       tc t v vs   -> mapM qv (v:vs) >>= \(v':vs') -> return $ KNCall tc t v' vs'
      KNCallPrim      t p vs   -> liftM  (KNCallPrim      t p) (mapM qv vs)
      KNAppCtor       t c vs   -> liftM  (KNAppCtor       t c) (mapM qv vs)
      KNAllocArray    t v      -> liftM  (KNAllocArray    t) (qv v)
      KNAlloc         t v _rgn -> liftM  (\v' -> KNAlloc  t v' _rgn) (qv v)
      KNDeref         t v      -> liftM  (KNDeref         t) (qv v)
      KNStore         t v1 v2  -> liftM2 (KNStore         t) (qv v1) (qv v2)
      KNArrayRead     t ai     -> liftM  (KNArrayRead     t) (renameArrayIndex ai)
      KNArrayPoke     t ai v   -> liftM2 (KNArrayPoke     t) (renameArrayIndex ai) (qv v)
      KNVar                  v -> liftM  KNVar                  (qv v)
      KNCase          t v arms -> do arms' <- mapM renameCaseArm arms
                                     v'    <- qv v
                                     return $ KNCase       t v' arms'
      KNUntil         t c b r  -> do [econd, ebody] <- mapM renameKN [c, b ]
                                     return $ KNUntil      t econd ebody r
      KNIf            t v e1 e2-> do [ethen, eelse] <- mapM renameKN [e1,e2]
                                     v' <- qv v
                                     return $ KNIf         t v' ethen eelse
      KNLetVal       id e   b  -> do id' <- renameI id
                                     [e' , b' ] <- mapM renameKN [e, b]
                                     return $ KNLetVal id' e'  b'
      KNLetRec     ids exprs e -> do ids' <- mapM renameI ids
                                     (e' : exprs' ) <- mapM renameKN (e:exprs)
                                     return $ KNLetRec ids' exprs'  e'
      KNLetFuns     ids fns b  -> do ids' <- mapM renameI ids
                                     fns' <- mapM renameFn fns
                                     b'   <- renameKN b
                                     return $ KNLetFuns ids' fns' b'
      KNTyApp t v argtys       -> qv v >>= \v' -> return $ KNTyApp t v' argtys

    renameCaseArm (CaseArm pat expr guard vs rng) = do
        pat' <- renamePattern pat
        vs' <- mapM qv vs -- TODO or renameV ?
        expr'  <-           renameKN expr
        guard' <- liftMaybe renameKN guard
        return (CaseArm pat' expr' guard' vs' rng)

    renamePatternAtom pattern = do
     case pattern of
       P_Wildcard {}          -> return pattern
       P_Bool     {}          -> return pattern
       P_Int      {}          -> return pattern
       P_Variable rng v       -> qv v >>= \v' -> return $ P_Variable rng v'

    renamePattern pattern = do
     let mp = mapM renamePattern
     case pattern of
       PR_Atom     atom             -> renamePatternAtom atom >>= \atom' -> return $ PR_Atom atom'
       PR_Ctor     rng t pats ctor  -> mp pats >>= \pats' -> return $ PR_Ctor  rng t pats' ctor
       PR_Tuple    rng t pats       -> mp pats >>= \pats' -> return $ PR_Tuple rng t pats'


data RenameState = RenameState {
                       renameUniq :: IORef Uniq
                     , renameMap  :: Map Ident Ident
                   }
type Renamed = StateT RenameState IO

-- ||||||||||||||||| Monomorphic Type Substitution ||||||||||||||{{{

type MonoSubst = Map TyVar MonoType
emptyMonoSubst = Map.empty

-- Extend the given substitution to map the given TypeFormalASTs to types.
extendSubst subst formals tys =
  let btv (TypeFormalAST s k) = (BoundTyVar s, k) in
  extendMonoSubst subst tys (map btv formals)

extendMonoSubst :: MonoSubst -> [MonoType] -> [(TyVar, Kind)] -> MonoSubst
extendMonoSubst subst monotypes ktyvars =
  let tyvarOf (tv, _kind) = tv in
  let ext = Prelude.zip (map tyvarOf ktyvars) monotypes in
  Map.union (Map.fromList ext) subst

monoType :: MonoSubst -> TypeIL -> MonoType
monoType subst ty =
  let q = monoType subst in
  case ty of
     TyConAppIL nam types -> TyConApp nam (map q types)
     PrimIntIL size       -> PrimInt size
     PrimFloat64IL        -> PrimFloat64
     TupleTypeIL types    -> TupleType (map q types)
     FnTypeIL  ss t cc cs -> FnType    (map q ss) (q t) cc cs
     CoroTypeIL s t       -> CoroType (q s) (q t)
     ArrayTypeIL ty       -> ArrayType (q ty)
     PtrTypeIL ty         -> PtrType   (q ty)
     -- Type checking should prevent us from trying to instantiate a Boxed
     -- variable with anything but a boxed type.
     ForAllIL ktvs rho    -> monoType (extendMonoSubst subst
                                            [PtrTypeUnknown | _ <- ktvs]
                                                            ktvs) rho
     TyVarIL tv _kind     -> monoSubstLookup subst tv -- TODO check kind?

-- Type variables of pointer-sized kind get translated into
-- opaque pointer types; other type variables are looked up
-- in the type substitution.
monoSubstLookup :: MonoSubst -> TyVar -> MonoType
monoSubstLookup _subst (SkolemTyVar  _ _ KindPointerSized) = PtrTypeUnknown
monoSubstLookup _subst (SkolemTyVar  _ _ KindAnySizeType)  =
        --TyConApp ("BAD:SKOLEM TY VAR, ANY SIZE TYPE:"++nm) []
        error $ "Monomorphization (Monomo.hs:monoSubsLookup) "
             ++ "found a bad skolem type variable with non-pointer kind"
monoSubstLookup subst tv@(BoundTyVar nm) =
  case Map.lookup tv subst of
      Just monotype -> monotype
      Nothing -> if True
                  then TyConApp ("AAAAAAmissing:"++nm) []
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
    monoSeenIds :: Set MonoProcId
  , monoOrigins :: Map PolyBinder (PolyOrigin)
  , monoResults :: Map PolyBinder [MonoResult]
  , monoDTSpecs :: EqSet (DataTypeName, [MonoType])
  , monoUniques :: IORef Uniq
  , monoWantedFns :: [String]
}

type MonoProcId = Ident
type MonoBinder = Ident
type PolyBinder = Ident

data MonoResult = MonoResult MonoProcId MonoFn

type MonoFn   = Fn RecStatus KNMono MonoType
type FnExprIL = Fn RecStatus KNExpr TypeIL

type Mono = StateT MonoState IO

split :: [(Ident, FnExprIL)] -> ([(MonoBinder, FnExprIL)]
                                ,[(PolyBinder, FnExprIL)])
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

monoAddOrigins :: [(PolyBinder, FnExprIL)] -> Mono ()
monoAddOrigins polys = do
  state <- get
  put state { monoOrigins = Map.union (monoOrigins state)
                                      (Map.fromList [(p, PolyOriginFn f)
                                                    |(p,f) <- polys]) }

data PolyOrigin = PolyOriginFn FnExprIL
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
  annotate fn = Fn { fnVar   = fnVar fn
                   , fnVars  = fnVars fn
                   , fnBody  = fnBody fn
                   , fnIsRec = (computeIsFnRec fn ids)
                   , fnAnnot = fnAnnot fn
                   }

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
