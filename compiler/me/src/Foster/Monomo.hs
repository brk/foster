-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Monomo (monomorphize) where

import Foster.Base
import Foster.Kind
import Foster.KNUtil
import Foster.Config
import Foster.AnnExprIL
import Foster.MonoType
import Foster.ConvertExprAST()
import Foster.Context

import qualified Data.Text as T

import Text.PrettyPrint.ANSI.Leijen

import Data.Map(Map)
import Data.Map as Map(lookup, alter, fromList, union, empty)
import Data.Set(Set)
import Data.Set as Set(member, insert, empty)
import Data.List as List(all)
import Control.Monad(when, liftM, liftM2, liftM3, liftM4)
import Control.Monad.State(evalStateT, get, gets, put, StateT, liftIO, lift)
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
             -> (AIExpr -> Compiled KNExpr)
   -> Compiled (ModuleIL (KNExpr' RecStatus MonoType) MonoType)
monomorphize (ModuleIL body decls dts primdts lines) knorm = do
    uref      <- gets ccUniqRef
    wantedFns <- gets ccDumpFns
    let monoState0 = MonoState Set.empty Map.empty Map.empty [] uref wantedFns knorm
    evalStateT (do
                   monobody <- monoKN emptyMonoSubst body
                   specs    <- gets monoDTSpecs
                   monodts     <- monomorphizedDataTypesFrom dts specs
                   monoprimdts <- monomorphizedDataTypesFrom primdts []
                   monodecls <- mapM monoExternDecl decls
                   return $ ModuleIL monobody monodecls monodts monoprimdts lines)
                              monoState0

monoPrim :: MonoSubst -> FosterPrim TypeIL -> Mono (FosterPrim MonoType)
monoPrim subst prim = do
  let qt = monoType subst
  case prim of
       NamedPrim tid      -> liftM NamedPrim (monoVar subst tid)
       PrimOp nm ty       -> liftM (PrimOp nm) (qt ty)
       PrimIntTrunc i1 i2 -> return $ PrimIntTrunc i1 i2
       CoroPrim   p t1 t2 -> liftM2 (CoroPrim p) (qt t1) (qt t2)

monoVar :: MonoSubst -> TypedId TypeIL -> Mono (TypedId MonoType)
monoVar subst v = do
  liftTID (monoType subst) v

monoKN :: MonoSubst -> (KNExpr' () TypeIL) -> Mono (KNExpr' RecStatus MonoType)
monoKN subst e =
 let qt = monoType subst
     qv = monoVar subst
     qp = monoPrim subst -- avoid need for RankNTypes...
     qa = liftArrayIndexM qv
     generic t = case kindOf t of KindPointerSized -> return PtrTypeUnknown
                                  _                -> qt t
 in
 case e of
  -- These cases are trivially inductive.
  KNLiteral       t lit    -> liftM2 KNLiteral       (qt t) (return lit)
  KNTuple         t vs a   -> liftM3 KNTuple         (qt t) (mapM qv vs) (return a)
  KNKillProcess   t s      -> liftM2 KNKillProcess   (qt t) (return s)
  KNCall          t v vs   -> liftM3 KNCall          (qt t) (qv v) (mapM qv vs)
  KNCallPrim      t p vs   -> liftM3 KNCallPrim      (qt t) (qp p) (mapM qv vs)
  KNAllocArray    t v      -> liftM2 KNAllocArray    (qt t) (qv v)
  KNAlloc         t v _rgn -> liftM3 KNAlloc         (qt t) (qv v) (return _rgn)
  KNDeref         t v      -> liftM2 KNDeref         (qt t) (qv v)
  KNStore         t v1 v2  -> liftM3 KNStore         (qt t) (qv v1) (qv v2)
  KNArrayRead     t ai     -> liftM2 KNArrayRead     (qt t) (qa ai)
  KNArrayPoke     t ai v   -> liftM3 KNArrayPoke     (qt t) (qa ai) (qv v)
  KNArrayLit      t arr vals -> liftM3 KNArrayLit    (qt t) (qv arr) (mapRightM qv vals)
  KNVar                  v -> liftM  KNVar                  (qv v)
  KNCompiles    r t e       -> liftM2 (KNCompiles r) (qt t) (monoKN subst e)
  KNInlined {} -> error $ "Monomo.hs expects inlining to run after monomorphization!"
  -- The cases involving sub-expressions are syntactically heavier,
  -- but are still basically trivially inductive.
  KNCase          t v pats -> do liftM3 KNCase          (qt t) (qv v)
                                         (mapM (monoPatternBinding subst) pats)
  KNIf            t v e1 e2-> do liftM4 KNIf (qt t) (qv v) (monoKN subst e1) (monoKN subst e2)
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
    t'@(TyConApp dtname args) <- qt t
    c' <- monoMarkDataType c dtname args
    vs' <- mapM qv vs
    return $ KNAppCtor t' c' vs'

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
                 (mkKNLetFuns ids'    fns'    b')
                  mkKNLetFuns
            where mkKNLetFuns []  []  b = b
                  mkKNLetFuns ids fns b = KNLetFuns ids fns b

  KNTyApp _ _ [] -> error "Monomo.hs: cannot type-apply with no arguments!"
  KNTyApp t (TypedId (ForAllIL ktvs _rho) polybinder) argtys -> do
    monotys <- mapM generic argtys
    let extsubst = extendMonoSubst subst monotys ktvs

    -- For example:              polybinder :: forall x:Type, x => Maybe x
    t'  <- monoType subst    t    --  t'  = NatInf(Mo) => Maybe NatInf
    t'' <- monoType extsubst _rho --  t'' = PtrTypeUnk => Maybe PtrTypeUnk
    --                                   t   = NatInf(IL) => Maybe NatInf

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
            putStrLn $ "for monobinder " ++ show monobinder ++ ", t   is " ++ show t
            putStrLn $ "for monobinder " ++ show monobinder ++ ", t'  is " ++ show t'
            putStrLn $ "for monobinder " ++ show monobinder ++ ", t'' is " ++ show t''

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
          --return $ KNTyApp t' (TypedId t' polybinder) []
          if List.all (\(_tv, kind) -> kind == KindPointerSized) ktvs
            then return $ bitcast t' (TypedId t'' polybinder)
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
  let qv = monoVar subst
  body' <- monoKN subst body
  v'  <- qv v
  vs' <- mapM qv vs
  return (Fn v' vs' body' isrec rng)

monoPatternBinding :: MonoSubst -> CaseArm PatternRepr KNExpr TypeIL
                          -> Mono (CaseArm PatternRepr KNMono MonoType)
monoPatternBinding subst (CaseArm pat expr guard vs rng) = do
  pat'   <- monoPattern subst pat
  vs'    <- mapM (monoVar subst) vs
  expr'  <-            monoKN subst  expr
  guard' <- liftMaybe (monoKN subst) guard
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
   PR_Ctor     rng t pats ctor  -> liftM3 (PR_Ctor     rng) (monoType subst t) (mp pats)
                                                            (monoCtorInfo subst ctor)

monoCtorInfo subst (LLCtorInfo cid repr tys) = do
          tys' <- mapM (monoType subst) tys
          return $ (LLCtorInfo cid repr tys')

monomorphizedDataTypesFrom :: [DataType TypeIL] -> [(String, [MonoType])] -> Mono [DataType MonoType]
monomorphizedDataTypesFrom dts specs = do
   dts' <- mapM monomorphizedDataTypes dts
   return $ concat dts'
 where monomorphizedDataType :: DataType TypeIL -> [MonoType] -> Mono (DataType MonoType)
       monomorphizedDataType (DataType name formals ctors range) args = do
                 ctors' <- mapM (monomorphizedCtor subst) ctors
                 return $    (DataType (getMonoFormal name args) []
                                       ctors' range)
                               where
         subst = extendSubst emptyMonoSubst formals args

         monomorphizedCtor :: MonoSubst -> DataCtor TypeIL -> Mono (DataCtor MonoType)
         monomorphizedCtor subst
                   (DataCtor name _tyformals types range) = do
           types' <- mapM (monoType subst) types
           return $ DataCtor name [] types' range

       dtSpecMap = mapAllFromList specs

       monomorphizedDataTypes :: DataType TypeIL -> Mono [DataType MonoType]
       monomorphizedDataTypes dt@(DataType formal tyformals _ _range) =
         -- We'll always produce the "regular" version of the data type...
         let genericTys = [PtrTypeUnknown | _ <- tyformals] in
         let monotyss = case Map.lookup (typeFormalName formal) dtSpecMap of
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

monoExternDecl (s, t) = liftM (\t' -> (s, t')) (monoType emptyMonoSubst t)

-- Monomorphized polymorphic values get different names.
-- The variant in which every type is an opaque pointer keeps the original
-- name; the other variants get distinct names.
getMonoId :: {-Poly-} Ident -> [MonoType] -> {-Mono-}  Ident
getMonoId id tys =
  if allTypesAreBoxed tys
    then id
    else idAppend id (show tys)

getMonoName nm tys = if allTypesAreBoxed tys then nm else nm ++ (show tys)
getMonoFormal (TypeFormal name kind) tys =
               TypeFormal (getMonoName name tys) kind

allTypesAreBoxed tys =
          List.all (\t -> case t of { PtrTypeUnknown -> True ; _ -> False }) tys

idAppend id s = case id of (GlobalSymbol o) -> (GlobalSymbol $ beforeS o)
                           (Ident o m)      -> (Ident (beforeS o) m)
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

  replaceFnVar :: Show t => MonoProcId -> Fn r KNExpr t -> Mono (Fn r KNExpr t)
  replaceFnVar moid fn = do
    whenMonoWanted (tidIdent $ fnVar fn) $ liftIO $ do
      putStrLn $ "polydef fn var:: " ++ show (fnVar fn)
      putStrLn $ "monodef fn var:: " ++ show (TypedId (tidType $ fnVar fn) moid)
    return fn { fnVar = TypedId (tidType $ fnVar fn) moid }

alphaRename :: Fn r (KNExpr' r2 t) t -> Mono (Fn r (KNExpr' r2 t) t)
alphaRename fn = do
   uref <- gets monoUniques
   liftIO $ alphaRename' fn uref

-- ||||||||||||||||| Monomorphic Type Substitution ||||||||||||||{{{

type MonoSubst = Map TyVar MonoType
emptyMonoSubst = Map.empty

-- Extend the given substitution to map the given TypeFormals to types.
extendSubst subst formals tys =
  let btv (TypeFormal s k) = (BoundTyVar s, k) in
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
     TyConAppIL nam types   -> liftM (TyConApp nam) (mapM q types)
     PrimIntIL size         -> return $ PrimInt size
     PrimFloat64IL          -> return $ PrimFloat64
     TupleTypeIL types      -> liftM TupleType (mapM q types)
     FnTypeIL  ss t cc cs -> do ss' <- mapM q ss
                                t'  <- q t
                                return $ FnType ss' t' cc cs
     RefinedTypeIL v e      -> liftM2 RefinedType (qv v) (convertPrecond subst e)
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
  , monoKNormalize :: AIExpr -> Compiled KNExpr
}

convertPrecond :: MonoSubst -> AIExpr -> Mono KNMono
convertPrecond subst expr = do
        ke <- monoAI expr
        monoKN subst ke

monoAI :: AIExpr -> Mono (KNExpr' () TypeIL)
monoAI e = do
  kn <- gets monoKNormalize
  lift $ kn e

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
  annotate fn = Fn { fnVar   = fnVar fn
                   , fnVars  = fnVars fn
                   , fnBody  = fnBody fn
                   , fnIsRec = (computeIsFnRec fn ids)
                   , fnAnnot = fnAnnot fn
                   }

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
