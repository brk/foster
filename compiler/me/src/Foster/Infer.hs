module Foster.Infer where

import Data.Map(Map)
import qualified Data.Map as Map
import List(length, elem, lookup)
import Data.Maybe(fromMaybe, fromJust)
import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Foster.Base
import Foster.TypeAST
import Foster.ExprAST
import Foster.Context

----------------------

type TypeSubst = Map Uniq TypeAST

type UnifySoln = Maybe TypeSubst

data TypeConstraint = TypeConstrEq TypeAST TypeAST

emptyTypeConstraintSet = Map.empty

extractSubstTypes :: [MetaTyVar] -> TypeSubst -> [TypeAST]
extractSubstTypes metaVars tysub =
    let keys = [u | (Meta u _) <- metaVars] in
    map (\k -> fromJust $ Map.lookup k tysub) keys

assocListWithoutKeys :: (Eq a) => [(a,b)] -> [a] -> [(a,b)]
assocListWithoutKeys lst keys =
    [(a,b) | (a,b) <- lst, not(List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt;
-- unlike tySubst, this replaces arbitrary types with other types.
parSubstTy :: [(TypeAST, TypeAST)] -> TypeAST -> TypeAST
parSubstTy prvNextPairs ty =
    case ty of
        (MissingTypeAST s)   -> fromMaybe ty $ List.lookup ty prvNextPairs
        (NamedTypeAST s)     -> fromMaybe ty $ List.lookup ty prvNextPairs
        (TupleTypeAST types) -> (TupleTypeAST [parSubstTy prvNextPairs t | t <- types])
        (FnTypeAST s t cs)   -> (FnTypeAST (parSubstTy prvNextPairs s) (parSubstTy prvNextPairs t) cs)
        (CoroType s t)   -> (CoroType (parSubstTy prvNextPairs s) (parSubstTy prvNextPairs t))
        (ForAll tvs rho) -> let prvNextPairs' = assocListWithoutKeys
                                                    prvNextPairs
                                                    [T_TyVar tv | tv <- tvs] in
                            (ForAll tvs (parSubstTy prvNextPairs' rho))
        (T_TyVar tv)     -> fromMaybe ty $ List.lookup ty prvNextPairs
        (MetaTyVar mtv)  -> fromMaybe ty $ List.lookup ty prvNextPairs

-- Replaces types for meta type variables (unification variables)
-- according to the given type substitution.
tySubst :: TypeAST -> TypeSubst -> TypeAST
tySubst ty subst =
    case ty of
        (MissingTypeAST s)   -> ty
        (NamedTypeAST s)     -> ty
        (TupleTypeAST types) -> (TupleTypeAST [tySubst t subst | t <- types])
        (FnTypeAST s t cs)   -> (FnTypeAST (tySubst s subst) (tySubst t subst) cs)
        (CoroType s t)   -> (CoroType (tySubst s subst) (tySubst t subst))
        (ForAll tvs rho) -> (ForAll tvs (tySubst rho subst))
        (T_TyVar tv)     -> ty
        (MetaTyVar (Meta u tyref))  -> Map.findWithDefault ty u subst

tyEnvSubst :: Context -> TypeSubst -> Context
tyEnvSubst ctx tysub =
    let newBindings = map (\bind ->
                  case bind of
                    TermVarBinding str (AnnVar ty id) ->
                        TermVarBinding str (AnnVar (tySubst ty tysub) id))
                  ctx in
    ctx-- { contextBindings = newBindings }

tySubstConstraints constraints tysub =
    [TypeConstrEq (tySubst t1 tysub) (tySubst t2 tysub) | TypeConstrEq t1 t2 <- constraints]

unifyTypes t1 t2 = unify [TypeConstrEq t1 t2]

unify :: [TypeConstraint] -> UnifySoln
unify constraints = unifyLoop constraints emptyTypeConstraintSet

unifyLoop :: [TypeConstraint] -> TypeSubst -> UnifySoln
unifyLoop [] tysub = Just tysub
unifyLoop ((TypeConstrEq t1 t2):constraints) tysub =
    if typesEqual t1 t2
      then unifyLoop constraints tysub
      else case (t1, t2) of
                ((FnTypeAST a1 a2 _), (FnTypeAST b1 b2 _)) ->
                    unifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub
                ((CoroType a1 a2), (CoroType b1 b2)) ->
                    unifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub
                ((TupleTypeAST tys1), (TupleTypeAST tys2)) ->
                    if List.length tys1 /= List.length tys2
                      then error $ "Unable to unify tuples of different lengths!"
                      else unifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints) tysub
                ((MetaTyVar m), ty) ->
                    unifyVar m ty tysub constraints
                (ty, (MetaTyVar m)) ->
                    unifyVar m ty tysub constraints
                otherwise ->
                    error $ "Unable to unify " ++ show t1 ++ " and " ++ show t2

unifyVar :: MetaTyVar -> TypeAST -> TypeSubst -> [TypeConstraint] -> UnifySoln
unifyVar (Meta uniq tyref) ty tysub constraints =
    let tysub' = (Map.insert uniq ty tysub) in
    unifyLoop (tySubstConstraints constraints (Map.singleton uniq ty)) tysub'
