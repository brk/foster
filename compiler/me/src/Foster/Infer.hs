module Foster.Infer(
    tcUnifyTypes
  , parSubstTcTy
  , tySubst
  , extractSubstTypes
) where

import Data.Map(Map)
import qualified Data.Map as Map(lookup, empty, insert, findWithDefault, singleton)
import qualified Data.List as List(length, elem, lookup)
import Data.Maybe(fromMaybe)
import Text.PrettyPrint.ANSI.Leijen

import Foster.Base
import Foster.TypeTC
import Foster.Context
import Foster.PrettyAnnExpr

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
        MetaTyVarTC {}       -> ty
        PrimIntTC  _         -> ty
        PrimFloat64TC        -> ty
        TyConAppTC  nm tys   -> TyConAppTC  nm (map q tys)
        TupleTypeTC  types   -> TupleTypeTC  (map q types)
        RefTypeTC    t       -> RefTypeTC    (q t)
        ArrayTypeTC  t       -> ArrayTypeTC  (q t)
        FnTypeTC  ss t p cc cs -> FnTypeTC     (map q ss) (q t) p cc cs -- TODO unify calling convention?
        CoroTypeTC  s t      -> CoroTypeTC  (q s) (q t)
        ForAllTC  ktvs rho   ->
                let prvNextPairs' = prvNextPairs `assocFilterOut` (map fst ktvs)
                in  ForAllTC  ktvs (parSubstTcTy prvNextPairs' rho)

-- Replaces types for meta type variables (unification variables)
-- according to the given type substitution.
tySubst :: TypeSubst -> TypeTC -> TypeTC
tySubst subst ty =
    let q = tySubst subst in
    case ty of
        MetaTyVarTC m          -> Map.findWithDefault ty (mtvUniq m) subst
        PrimIntTC    {}        -> ty
        PrimFloat64TC          -> ty
        TyVarTC      {}        -> ty
        TyConAppTC   nm tys    -> TyConAppTC   nm (map q tys)
        RefTypeTC     t        -> RefTypeTC    (q t)
        ArrayTypeTC   t        -> ArrayTypeTC  (q t)
        TupleTypeTC  types     -> TupleTypeTC  (map q types)
        FnTypeTC  ss t p cc cs -> FnTypeTC     (map q ss) (q t) p cc cs
        CoroTypeTC  s t        -> CoroTypeTC  (q s) (q t)
        ForAllTC  tvs rho      -> ForAllTC  tvs (q rho)

-------------------------------------------------
illegal (TyVarTC (BoundTyVar _)) = True
illegal (ForAllTC {})            = True
illegal _                        = False
-------------------------------------------------

tcUnifyTypes :: TypeTC -> TypeTC -> Tc UnifySoln
tcUnifyTypes t1 t2 = tcUnify [TypeConstrEq t1 t2]
  where
    tcUnify :: [TypeConstraint] -> Tc UnifySoln
    tcUnify constraints = tcUnifyLoop constraints emptyTypeSubst

tcUnifyMoreTypes tys1 tys2 constraints tysub =
 tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints) tysub

tcUnifyLoop :: [TypeConstraint] -> TypeSubst -> Tc UnifySoln
tcUnifyLoop [] tysub = return $ Just tysub

tcUnifyLoop ((TypeConstrEq (PrimIntTC  I32) (PrimIntTC  I32)):constraints) tysub
  = tcUnifyLoop constraints tysub

tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub = do
 --tcLift $ putStrLn ("tcUnifyLoop: t1 = " ++ show t1 ++ "; t2 = " ++ show t2)
 if illegal t1 || illegal t2
  then tcFailsMore
        [string ("Bound type variables cannot be unified!\n" ++
               "Unable to unify\n\t") <> pretty t1 <> string "\nand\n\t" <> pretty t2
        ,text "t1::", showStructure t1, text "t2::", showStructure t2]
  else
   case (t1, t2) of
    (PrimFloat64TC , PrimFloat64TC ) -> tcUnifyLoop constraints tysub
    ((PrimIntTC  n1), (PrimIntTC  n2)) ->
      if n1 == n2 then tcUnifyLoop constraints tysub
                  else do msg <- getStructureContextMessage
                          tcFailsMore [text $ "Unable to unify different primitive types: "
                                       ++ show n1 ++ " vs " ++ show n2
                                       , msg]

    ((TyVarTC  tv1), (TyVarTC  tv2)) ->
       if tv1 == tv2 then tcUnifyLoop constraints tysub
                     else tcFailsMore [text $ "Unable to unify different type variables: "
                                       ++ show tv1 ++ " vs " ++ show tv2]

    ((TyConAppTC  nm1 tys1), (TyConAppTC  nm2 tys2)) ->
      if nm1 == nm2
        then tcUnifyMoreTypes tys1 tys2 constraints tysub
        else do msg <- getStructureContextMessage
                tcFailsMore [text $ "Unable to unify different type constructors: "
                                  ++ nm1 ++ " vs " ++ nm2,
                             msg]

    ((TupleTypeTC  tys1), (TupleTypeTC  tys2)) ->
        if List.length tys1 /= List.length tys2
          then tcFailsMore [text $ "Unable to unify tuples of different lengths"
                           ++ " ("   ++ show (List.length tys1)
                           ++ " vs " ++ show (List.length tys2)
                           ++ ")."]
          else tcUnifyMoreTypes tys1 tys2 constraints tysub

    -- Mismatches between unitary tuple types probably indicate
    -- parsing/function argument handling mismatch.

    ((FnTypeTC  as1 a1 p1 _cc1 _), (FnTypeTC  as2 a2 p2 _cc2 _)) -> do
        case (p1, p2) of
          (NoPrecondition _, NoPrecondition _) -> return ()
          _ -> tcLift $ do putStrLn $ "TODO: type inference `unifying' preconditions"
                           putStrLn $ "\t" ++ show (pretty p1)
                           putStrLn $ "and"
                           putStrLn $ "\t" ++ show (pretty p2)
        if List.length as1 /= List.length as2
          then tcFailsMore [string "Unable to unify functions of different arity!\n"
                           <> pretty as1 <> string "\nvs\n" <> pretty as2]
          else tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip as1 as2]
                         ++ (TypeConstrEq a1 a2):constraints) tysub

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

    ((MetaTyVarTC m), ty) -> tcUnifyVar m ty tysub constraints
    (ty, (MetaTyVarTC m)) -> tcUnifyVar m ty tysub constraints

    ((RefTypeTC  t1), (RefTypeTC  t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((ArrayTypeTC  t1), (ArrayTypeTC  t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

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
    --  tcLift $ putStrLn $ "================ Unifying meta var " ++ show (pretty $ MetaTyVar m) ++ " :: " ++ show (pretty tcm)
    --                 ++ "\n============================= with " ++ show (pretty $ ty)
    let tysub' = Map.insert (mtvUniq m) ty tysub
    tcUnifyLoop (tySubstConstraints constraints (Map.singleton (mtvUniq m) ty)) tysub'
      where
        tySubstConstraints constraints tysub = map tySub constraints
          where q = tySubst tysub
                tySub (TypeConstrEq t1 t2) = TypeConstrEq (q t1) (q t2)

