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

extractSubstTypes :: [MetaTyVar] -> TypeSubst -> [TypeAST]
extractSubstTypes metaVars tysub =
    let keys = [u | (Meta u _ _) <- metaVars] in
    map (\k -> fromMaybe (error $ "Subst map missing key " ++ show k)
                         (Map.lookup k tysub)) keys

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
        DataTypeAST _  -> fromMaybe ty $ List.lookup ty prvNextPairs
        TyVarAST   {}  -> fromMaybe ty $ List.lookup ty prvNextPairs
        MetaTyVar  {}  -> fromMaybe ty $ List.lookup ty prvNextPairs
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
        DataTypeAST  {}             -> ty
        TyVarAST     {}             -> ty
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

tcUnifyLoop :: [TypeConstraint] -> TypeSubst -> Tc UnifySoln
tcUnifyLoop [] tysub = return $ Just tysub
tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub = do
  if typesEqual t1 t2
    then tcUnifyLoop constraints tysub
    else case (t1, t2) of
              ((PrimIntAST n1), (PrimIntAST n2)) ->
                if n1 == n2 then tcUnifyLoop constraints tysub
                            else tcFails [out $ "Unable to unify different primitive types: "
                                            ++ show n1 ++ " vs " ++ show n2]

              ((DataTypeAST n1), (DataTypeAST n2)) ->
                if n1 == n2 then tcUnifyLoop constraints tysub
                            else tcFails [out $ "Unable to unify different named types: "
                                            ++ n1 ++ " vs " ++ n2]

              ((TupleTypeAST tys1), (TupleTypeAST tys2)) ->
                  if List.length tys1 /= List.length tys2
                    then tcFails [out $ "Unable to unify tuples of different lengths!"]
                    else tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints) tysub

              ((FnTypeAST a1 a2 _cc1 _), (FnTypeAST b1 b2 _cc2 _)) ->
                  tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub

              ((CoroTypeAST a1 a2), (CoroTypeAST b1 b2)) ->
                  tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub

              -- TODO: ForAllAST: alpha-equivalence?
              -- TODO: T_TyVar -- alpha equivalence?

              ((MetaTyVar m), ty) ->
                  tcUnifyVar m ty tysub constraints
              (ty, (MetaTyVar m)) ->
                  tcUnifyVar m ty tysub constraints

              ((RefTypeAST t1), (RefTypeAST t2)) ->
                  tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

              ((ArrayTypeAST t1), (ArrayTypeAST t2)) ->
                  tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

              _otherwise ->
                  tcFails [out $ "Unable to unify " ++ show t1 ++ " and " ++ show t2]

tcUnifyVar :: MetaTyVar -> TypeAST -> TypeSubst -> [TypeConstraint] -> Tc UnifySoln
tcUnifyVar (Meta uniq _tyref _) ty tysub constraints =
    let tysub' = (Map.insert uniq ty tysub) in
    tcUnifyLoop (tySubstConstraints constraints (Map.singleton uniq ty)) tysub'
      where
        tySubstConstraints constraints tysub = map tySub constraints
          where q = tySubst tysub
                tySub (TypeConstrEq t1 t2) = TypeConstrEq (q t1) (q t2)

