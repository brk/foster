module Foster.Infer(
    tcUnifyTypes, tcUnifyFT, tcUnifyCC, tcUnifyKinds
  , parSubstTcTy
  , tySubst
  , extractSubstTypes
) where

import Data.Map(Map)
import qualified Data.Map as Map(lookup, empty, insert, findWithDefault, singleton)
import qualified Data.List as List(length, elem, lookup)
import Data.Maybe(fromMaybe)
import Text.PrettyPrint.ANSI.Leijen
import Data.UnionFind.IO(descriptor, setDescriptor, equivalent, union)

import Foster.Base
import Foster.TypeTC
import Foster.Context

----------------------

type TypeSubst = Map Uniq TypeTC

type UnifySoln = Maybe TypeSubst

data TypeConstraint = TypeConstrEq TypeTC TypeTC

emptyTypeSubst = Map.empty

----------------------

extractSubstTypes :: [MetaTyVar TypeTC] -> TypeSubst -> Tc [TypeTC]
extractSubstTypes metaVars tysub = do
    mapM lookup metaVars where
         lookup m =
               fromMaybe (return $ MetaTyVarTC m)
                         (fmap return $ Map.lookup (mtvUniq m) tysub)

assocFilterOut :: Eq a => [(a,b)] -> [a] -> [(a,b)]
assocFilterOut lst keys = [(a,b) | (a,b) <- lst, not(List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt.
parSubstTcTy :: [(TyVar, TypeTC)] -> TypeTC -> TypeTC
parSubstTcTy prvNextPairs ty =
    let q = parSubstTcTy prvNextPairs in
    case ty of
        TyVarTC  tv          -> fromMaybe ty $ List.lookup tv prvNextPairs
        MetaTyVarTC   {}     -> ty
        PrimIntTC     {}     -> ty
        PrimFloat64TC {}     -> ty
        TyConAppTC  nm tys   -> TyConAppTC  nm (map q tys)
        TupleTypeTC k  types -> TupleTypeTC k  (map q types)
        RefTypeTC    t       -> RefTypeTC    (q t)
        ArrayTypeTC  t       -> ArrayTypeTC  (q t)
        FnTypeTC  ss t fx cc cs -> FnTypeTC     (map q ss) (q t) (q fx) cc cs -- TODO unify calling convention?
        CoroTypeTC  s t      -> CoroTypeTC  (q s) (q t)
        ForAllTC  ktvs rho   ->
                let prvNextPairs' = prvNextPairs `assocFilterOut` (map fst ktvs)
                in  ForAllTC  ktvs (parSubstTcTy prvNextPairs' rho)
        RefinedTypeTC v e args -> RefinedTypeTC (fmap q v) e args -- TODO recurse in e?

-- Replaces types for meta type variables (unification variables)
-- according to the given type substitution.
tySubst :: TypeSubst -> TypeTC -> TypeTC
tySubst subst ty =
    let q = tySubst subst in
    case ty of
        MetaTyVarTC m          -> Map.findWithDefault ty (mtvUniq m) subst
        PrimIntTC     {}       -> ty
        PrimFloat64TC {}       -> ty
        TyVarTC       {}       -> ty
        TyConAppTC   nm tys    -> TyConAppTC   nm (map q tys)
        RefTypeTC     t        -> RefTypeTC    (q t)
        ArrayTypeTC   t        -> ArrayTypeTC  (q t)
        TupleTypeTC k types    -> TupleTypeTC k (map q types)
        FnTypeTC  ss t fx cc cs -> FnTypeTC     (map q ss) (q t) (q fx) cc cs
        CoroTypeTC  s t        -> CoroTypeTC  (q s) (q t)
        ForAllTC  tvs rho      -> ForAllTC  tvs (q rho)
        RefinedTypeTC v e args -> RefinedTypeTC (fmap q v) e args

-------------------------------------------------
illegal (TyVarTC (BoundTyVar {})) = True
illegal (ForAllTC {})             = True
illegal _                         = False
-------------------------------------------------

tcUnifyThings :: (Eq t, Show t) => Unifiable t -> Unifiable t -> (t -> t -> Tc ()) -> Tc ()
tcUnifyThings thing1 thing2 errAction = do
  let uni ft (_,r) = do
        mbx <- tcLift $ descriptor r
        case mbx of
          Nothing -> do tcLift $ setDescriptor r (Just ft)
          Just ft' -> tcUnifyThings (UniConst ft) (UniConst ft' ) errAction
      cmp ft1 ft2 =
          if ft1 == ft2 then return ()
                        else errAction ft1 ft2
  case (thing1, thing2) of
    (UniConst ft1, UniConst ft2) -> cmp ft1 ft2
    (UniConst ft1, UniVar v) -> uni ft1 v
    (UniVar v, UniConst ft2) -> uni ft2 v
    (UniVar (_,p), UniVar (_,q)) -> do
       eq <- tcLift $ equivalent p q
       if eq
        then return ()
        else do
           mbp <- tcLift $ descriptor p
           mbq <- tcLift $ descriptor q
           case (mbp, mbq) of
             (Just ft1, Just ft2) -> cmp ft1 ft2
             (Just _,   Nothing)  -> tcLift $ union q p
             _                    -> tcLift $ union p q

-- Only warn, don't throw an error, if we try to unify a proc with a func.
-- This happens for code like ``listFoldl xs Cons Nil`` where ``listFoldl``
-- expects functions but ``Cons`` and ``Nil`` are procs.  Later on we'll
-- detect such mismatches and insert thunks to mediate the disconnect.
tcUnifyFT uft1 uft2 = tcUnifyThings uft1 uft2
     (\_ _ -> tcWhenVerbose $
        tcLift $ putDoc $ text "WARNING: unable to unify disparate proc/func annotations" <> line)

-- Likewise, code like ``run-it read_i32`` will cause a CCC/FastCC mismatch,
-- which will be papered over with a proc wrapper.
tcUnifyCC ucc1 ucc2 = tcUnifyThings ucc1 ucc2
     (\_ _ -> tcWhenVerbose $
        tcLift $ putDoc $ text "WARNING: unable to unify disparate calling conventions" <> line)

tcUnifyKinds uk1 uk2 = tcUnifyThings uk1 uk2
     (\k1 k2 -> tcFails [text "Unable to unify kinds " <> pretty k1 <+> text "and" <+> pretty k2])

-------------------------------------------------

tcUnifyTypes :: TypeTC -> TypeTC -> Tc UnifySoln
tcUnifyTypes t1 t2 = tcUnifyLoop [TypeConstrEq t1 t2] emptyTypeSubst

tcUnifyMoreTypes tys1 tys2 constraints tysub =
 tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints) tysub

-------------------------------------------------
tcUnifyLoop :: [TypeConstraint] -> TypeSubst -> Tc UnifySoln
tcUnifyLoop [] tysub = return $ Just tysub

tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub = do
 --tcLift $ putStrLn ("tcUnifyLoop: t1 = " ++ show t1 ++ "; t2 = " ++ show t2)
 if illegal t1 || illegal t2
  then tcFailsMore
        [text "Bound type variables cannot be unified! Unable to unify"
        ,text "\t" <> pretty t1 <> string "\nand\n\t" <> pretty t2
        ,text "t1::", showStructure t1, text "t2::", showStructure t2]
  else
   case (t1, t2) of
    (PrimFloat64TC, PrimFloat64TC) -> do
      tcUnifyLoop constraints tysub

    ((PrimIntTC  n1), (PrimIntTC  n2)) ->
          if n1 == n2 then do tcUnifyLoop constraints tysub
            else tcFailsMore [text $ "Unable to unify different primitive types: "
                             ,indent 2 $ pretty n1 <> text " vs " <> pretty n2
                             ]

    ((TyVarTC  tv1), (TyVarTC  tv2)) ->
       if tv1 == tv2 then tcUnifyLoop constraints tysub
                     else tcFailsMore [text $ "Unable to unify different type variables: "
                                       ++ show tv1 ++ " vs " ++ show tv2]

    ((TyConAppTC  nm1 tys1), (TyConAppTC  nm2 tys2)) ->
      if nm1 == nm2
        then do tcUnifyMoreTypes tys1 tys2 constraints tysub
        else do msg <- getStructureContextMessage
                tcFailsMore [text $ "Unable to unify different type constructors: "
                                  ++ nm1 ++ " vs " ++ nm2,
                             msg]

    ((TupleTypeTC kind1 tys1), (TupleTypeTC kind2 tys2)) ->
        if List.length tys1 /= List.length tys2
          then tcFailsMore [text $ "Unable to unify tuples of different lengths"
                           ++ " ("   ++ show (List.length tys1)
                           ++ " vs " ++ show (List.length tys2)
                           ++ ")."]
          else do tcUnifyKinds kind1 kind2
                  tcUnifyMoreTypes tys1 tys2 constraints tysub

    -- Mismatches between unitary tuple types probably indicate
    -- parsing/function argument handling mismatch.

    ((FnTypeTC  as1 a1 fx1 cc1 ft1), (FnTypeTC  as2 a2 fx2 cc2 ft2)) -> do
        if List.length as1 /= List.length as2
          then tcFailsMore [string "Unable to unify functions of different arity!\n"
                           <> pretty as1 <> string "\nvs\n" <> pretty as2]
          else do tcUnifyCC cc1 cc2
                  tcUnifyFT ft1 ft2
                  tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip as1 as2]
                            ++  (TypeConstrEq a1 a2)
                               :(TypeConstrEq fx1 fx2)
                               :constraints) tysub

    ((CoroTypeTC  a1 a2), (CoroTypeTC  b1 b2)) ->
        tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub

    ((ForAllTC  ktyvars1 rho1), (ForAllTC  ktyvars2 rho2)) ->
        let (tyvars1, kinds1) = unzip ktyvars1 in
        let (tyvars2, kinds2) = unzip ktyvars2 in
        if List.length tyvars1 /= List.length tyvars2
         then tcFails [string "Unable to unify foralls of different arity!\n" <> pretty t1 <> string "\nvs\n" <> pretty t2]
         else if kinds1 /= kinds2
          then tcFails [text $ "Unable to unify foralls with differently-kinded type variables"]
          else let t1 = rho1 in
               let tySubst = zip tyvars2 (map (\(tv,_) -> TyVarTC  tv) ktyvars1) in
               let t2 = parSubstTcTy tySubst rho2 in
               tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((RefinedTypeTC (TypedId t1 _n1) _e1 _), (RefinedTypeTC (TypedId t2 _n2) _e2 _)) ->
      -- TODO make sure that n/e match...
      tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((MetaTyVarTC m), ty) -> tcUnifyVar m ty tysub constraints
    (ty, (MetaTyVarTC m)) -> tcUnifyVar m ty tysub constraints

    ((RefTypeTC  t1), (RefTypeTC  t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((ArrayTypeTC  t1), (ArrayTypeTC  t2)) -> do
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((RefinedTypeTC v _ _), ty) -> do
      tcUnifyLoop ((TypeConstrEq (tidType v) ty):constraints) tysub

    (ty, (RefinedTypeTC v _ _)) -> do
      tcUnifyLoop ((TypeConstrEq ty (tidType v)):constraints) tysub

    _otherwise -> do
      msg <- getStructureContextMessage
      tcFailsMore
        [string "Unable to unify\n\t" <> pretty t1 <> string "\nand\n\t" <> pretty t2
        ,text "t1::", showStructure t1, text "t2::", showStructure t2
        ,msg]

tcUnifyVar :: MetaTyVar TypeTC  -> TypeTC  -> TypeSubst -> [TypeConstraint] -> Tc UnifySoln

-- Ignore attempts to unify a meta type variable with itself.
tcUnifyVar m1 (MetaTyVarTC m2) tysub constraints | m1 == m2
  = tcUnifyLoop constraints tysub

tcUnifyVar m ty tysub constraints = do
    --do
    --  tcm <- readTcMeta m
    --  tcLift $ putStrLn $ "================ Unifying meta var " ++ show (pretty $ MetaTyVarTC m) ++ " :: " ++ show (pretty tcm)
    --                 ++ "\n============================= with " ++ show (pretty $ ty)
    let tysub' = Map.insert (mtvUniq m) ty tysub
    tcUnifyLoop (tySubstConstraints constraints (Map.singleton (mtvUniq m) ty)) tysub'
      where
        tySubstConstraints constraints tysub = map tySub constraints
          where q = tySubst tysub
                tySub (TypeConstrEq t1 t2) = TypeConstrEq (q t1) (q t2)

