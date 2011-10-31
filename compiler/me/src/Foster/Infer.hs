module Foster.Infer(
    tcUnifyTypes
  , parSubstTy
  , tySubst
  , extractSubstTypes
) where

import Data.Map(Map)
import qualified Data.Map as Map(lookup, empty, insert, findWithDefault, singleton)
import List(length, elem, lookup)
import Data.Maybe(fromMaybe)

import Foster.Base
import Foster.TypeAST
import Foster.Context

----------------------

type TypeSubst = Map Uniq TypeAST

type UnifySoln = Maybe TypeSubst

data TypeConstraint = TypeConstrEq TypeAST TypeAST

emptyTypeSubst = Map.empty

----------------------

-- extractSubstTypes :: [MetaTyVar] -> TypeSubst -> Tc [TypeAST]
extractSubstTypes metaVars tysub rng = do
    mapM lookup metaVars where
         lookup (Meta uniq _ desc) =
               fromMaybe (tcFails [out $ "Subst map missing key: " ++ desc
                                                   ++ highlightFirstLine rng])
                         (fmap return $ Map.lookup uniq tysub)

instance Eq TypeAST where
    t1 == t2 = typesEqual t1 t2

assocFilterOut :: (Eq a) => [(a,b)] -> [a] -> [(a,b)]
assocFilterOut lst keys =
    [(a,b) | (a,b) <- lst, not (List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt;
-- unlike tySubst, this replaces arbitrary types with other types.
parSubstTy :: [(TypeAST, TypeAST)] -> TypeAST -> TypeAST
parSubstTy prvNextPairs ty =
    let q = parSubstTy prvNextPairs in
    case ty of
        TyVarAST   {}  -> fromMaybe ty $ List.lookup ty prvNextPairs
        MetaTyVar  {}  -> fromMaybe ty $ List.lookup ty prvNextPairs
        TyConAppAST nm tys -> fromMaybe (TyConAppAST nm (map q tys)) $
                                         List.lookup ty prvNextPairs
        PrimIntAST _       -> ty
        RefTypeAST   t     -> RefTypeAST   (q t)
        ArrayTypeAST t     -> ArrayTypeAST (q t)
        TupleTypeAST types -> TupleTypeAST (map q types)
        FnTypeAST s t cc cs-> FnTypeAST   (q s) (q t) cc cs -- TODO unify calling convention?
        CoroTypeAST s t    -> CoroTypeAST (q s) (q t)
        ForAllAST ktvs rho ->
                let prvNextPairs' = prvNextPairs `assocFilterOut`
                                                 [TyVarAST tv | (tv, _) <- ktvs]
                in  ForAllAST ktvs (parSubstTy prvNextPairs' rho)

-- Replaces types for meta type variables (unification variables)
-- according to the given type substitution.
tySubst :: TypeSubst -> TypeAST -> TypeAST
tySubst subst ty =
    let q = tySubst subst in
    case ty of
        MetaTyVar (Meta u _tyref _) -> Map.findWithDefault ty u subst
        PrimIntAST   {}             -> ty
        TyVarAST     {}             -> ty
        TyConAppAST  nm tys         -> TyConAppAST  nm (map q tys)
        RefTypeAST    t             -> RefTypeAST   (q t)
        ArrayTypeAST  t             -> ArrayTypeAST (q t)
        TupleTypeAST types          -> TupleTypeAST (map q types)
        FnTypeAST s t cc cs         -> FnTypeAST   (q s) (q t) cc cs
        CoroTypeAST s t             -> CoroTypeAST (q s) (q t)
        ForAllAST tvs rho           -> ForAllAST tvs (q rho)

-------------------------------------------------

tcUnifyTypes :: TypeAST -> TypeAST -> Tc UnifySoln
tcUnifyTypes t1 t2 = tcUnify [TypeConstrEq t1 t2]
  where
    tcUnify :: [TypeConstraint] -> Tc UnifySoln
    tcUnify constraints = tcUnifyLoop constraints emptyTypeSubst

tcUnifyMoreTypes tys1 tys2 constraints tysub =
 tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints) tysub

tcUnifyLoop :: [TypeConstraint] -> TypeSubst -> Tc UnifySoln
tcUnifyLoop [] tysub = return $ Just tysub
tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub = do
  case (t1, t2) of
    ((PrimIntAST n1), (PrimIntAST n2)) ->
      if n1 == n2 then tcUnifyLoop constraints tysub
                  else tcFails [out $ "Unable to unify different primitive types: "
                                  ++ show n1 ++ " vs " ++ show n2]

    ((TyVarAST tv1), (TyVarAST tv2)) ->
       if tv1 == tv2 then tcUnifyLoop constraints tysub
                     else tcFails [out $ "Unable to unify different type variables: "
                                     ++ show tv1 ++ " vs " ++ show tv2]

    ((TyConAppAST nm1 tys1), (TyConAppAST nm2 tys2)) ->
      if nm1 == nm2
        then tcUnifyMoreTypes tys1 tys2 constraints tysub
        else tcFails [out $ "Unable to unify different type constructors: "
                                  ++ nm1 ++ " vs " ++ nm2]

    ((TupleTypeAST tys1), (TupleTypeAST tys2)) ->
        if List.length tys1 /= List.length tys2
          then tcFails [out $ "Unable to unify tuples of different lengths!"]
          else tcUnifyMoreTypes tys1 tys2 constraints tysub

    -- Mismatches between unitary tuple types probably indicate
    -- parsing/function argument handling mismatch.

    ((FnTypeAST a1 a2 _cc1 _), (FnTypeAST b1 b2 _cc2 _)) ->
        tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub

    ((CoroTypeAST a1 a2), (CoroTypeAST b1 b2)) ->
        tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub

    ((ForAllAST ktyvars1 rho1), (ForAllAST ktyvars2 rho2)) ->
        let (tyvars1, kinds1) = unzip ktyvars1 in
        let (tyvars2, kinds2) = unzip ktyvars2 in
        if List.length tyvars1 /= List.length tyvars2
         then tcFails [out $ "Unable to unify foralls of different arity!"]
         else if kinds1 /= kinds2
          then tcFails [out $ "Unable to unify foralls with differently-kinded type variables"]
          else let t1 = rho1 in
               let tySubst = zip (map TyVarAST tyvars2)
                                 (map TyVarAST tyvars1) in
               let t2 = parSubstTy tySubst rho2 in
               tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((MetaTyVar m), ty) ->
        tcUnifyVar m ty tysub constraints
    (ty, (MetaTyVar m)) ->
        tcUnifyVar m ty tysub constraints

    ((RefTypeAST t1), (RefTypeAST t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((ArrayTypeAST t1), (ArrayTypeAST t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    _otherwise ->
        tcFails [out $ "Unable to unify\n\t" ++ show t1 ++ "\nand\n\t" ++ show t2
                ,out $ "t1::", showStructure t1, out $ "t2::", showStructure t2]

tcUnifyVar :: MetaTyVar -> TypeAST -> TypeSubst -> [TypeConstraint] -> Tc UnifySoln
tcUnifyVar (Meta uniq _tyref _) ty tysub constraints =
    let tysub' = (Map.insert uniq ty tysub) in
    tcUnifyLoop (tySubstConstraints constraints (Map.singleton uniq ty)) tysub'
      where
        tySubstConstraints constraints tysub = map tySub constraints
          where q = tySubst tysub
                tySub (TypeConstrEq t1 t2) = TypeConstrEq (q t1) (q t2)

