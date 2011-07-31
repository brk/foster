module Foster.Infer(
    tcUnifyTypes
  , parSubstTy
  , tySubst
  , extractSubstTypes
) where

import Data.Map(Map)
import qualified Data.Map as Map
import List(length, elem, lookup)
import Data.Maybe(fromMaybe)

import Foster.Base
import Foster.TypeAST
import Foster.Context

----------------------

type TypeSubst = Map Uniq TypeAST

type UnifySoln = Maybe TypeSubst

data TypeConstraint = TypeConstrEq TypeAST TypeAST

emptyTypeConstraintSet = Map.empty

extractSubstTypes :: [MetaTyVar] -> TypeSubst -> [TypeAST]
extractSubstTypes metaVars tysub =
    let keys = [u | (Meta u _ _) <- metaVars] in
    map (\k -> fromMaybe (error $ "Subst map missing key " ++ show k)
                         (Map.lookup k tysub)) keys

instance Eq TypeAST where
    t1 == t2 = typesEqual t1 t2

assocFilterOut :: (Eq a) => [(a,b)] -> [a] -> [(a,b)]
assocFilterOut lst keys =
    [(a,b) | (a,b) <- lst, not(List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt;
-- unlike tySubst, this replaces arbitrary types with other types.
parSubstTy :: [(TypeAST, TypeAST)] -> TypeAST -> TypeAST
parSubstTy prvNextPairs ty =
    let q = parSubstTy prvNextPairs in
    case ty of
        (NamedTypeAST _) -> fromMaybe ty $ List.lookup ty prvNextPairs
        (TyVarAST tv)    -> fromMaybe ty $ List.lookup ty prvNextPairs
        (MetaTyVar mtv)  -> fromMaybe ty $ List.lookup ty prvNextPairs

        (RefTypeAST   t)     -> RefTypeAST   (q t)
        (ArrayTypeAST t)     -> ArrayTypeAST (q t)
        (TupleTypeAST types) -> TupleTypeAST (map q types)
        (FnTypeAST s t cc cs)-> FnTypeAST (q s) (q t) cc cs -- TODO unify calling convention?
        (CoroTypeAST s t)    -> CoroTypeAST (q s) (q t)
        (ForAllAST tvs rho)  ->
                let prvNextPairs' = prvNextPairs `assocFilterOut`
                                                   [TyVarAST tv | tv <- tvs]
                in  ForAllAST tvs (parSubstTy prvNextPairs' rho)

-- Replaces types for meta type variables (unification variables)
-- according to the given type substitution.
tySubst :: TypeSubst -> TypeAST -> TypeAST
tySubst subst ty =
    let q = tySubst subst in
    case ty of
        (NamedTypeAST s)     -> ty
        (RefTypeAST    t)    -> RefTypeAST   (q t)
        (ArrayTypeAST  t)    -> ArrayTypeAST (q t)
        (TupleTypeAST types) -> TupleTypeAST (map q types)
        (FnTypeAST s t cc cs)-> FnTypeAST (q s) (q t) cc cs
        (CoroTypeAST s t)    -> CoroTypeAST (q s) (q t)
        (ForAllAST tvs rho)  -> ForAllAST tvs (q rho)
        (TyVarAST tv)        -> ty
        (MetaTyVar (Meta u tyref _))  -> Map.findWithDefault ty u subst

tyEnvSubst :: Context TypeAST -> TypeSubst -> Context TypeAST
tyEnvSubst ctx tysub =
    let newBindings = map (\bind ->
                  case bind of
                    TermVarBinding str (TypedId ty id) ->
                        TermVarBinding str (TypedId (tySubst tysub ty) id))
                  (contextBindings ctx) in
    ctx { contextBindings = newBindings }

tySubstConstraints constraints tysub =
    map tySub constraints
      where q = tySubst tysub
            tySub (TypeConstrEq t1 t2) = TypeConstrEq (q t1) (q t2)

-------------------------------------------------

tcUnifyTypes :: TypeAST -> TypeAST -> Tc UnifySoln
tcUnifyTypes t1 t2 = tcUnify [TypeConstrEq t1 t2]

tcUnify :: [TypeConstraint] -> Tc UnifySoln
tcUnify constraints = tcUnifyLoop constraints emptyTypeConstraintSet

tcUnifyLoop :: [TypeConstraint] -> TypeSubst -> Tc UnifySoln
tcUnifyLoop [] tysub = return $ Just tysub
tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub = do
    if typesEqual t1 t2
      then tcUnifyLoop constraints tysub
      else case (t1, t2) of
                ((NamedTypeAST n1), (NamedTypeAST n2)) ->
                  if n1 == n2 then tcUnifyLoop constraints tysub
                              else tcFails [out $ "Unable to unify different named types: "
                                              ++ n1 ++ " vs " ++ n2]

                ((TupleTypeAST tys1), (TupleTypeAST tys2)) ->
                    if List.length tys1 /= List.length tys2
                      then tcFails [out $ "Unable to unify tuples of different lengths!"]
                      else tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints) tysub

                ((FnTypeAST a1 a2 cc1 _), (FnTypeAST b1 b2 cc2 _)) ->
                  if cc1 == cc2 || (cc1 == FastCC && cc2 == CCC) then
                    -- We can implicitly convert a CCC to a FastCC
                    -- (but not the other way 'round) using implicitly-inserted
                    -- coercions during lowering to LLVM.
                    tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub
                  else tcFails [out $ "Cannot unify function types with different calling conventions: "
                                    ++ show cc1 ++ " vs " ++ show cc2]

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

                otherwise ->
                    tcFails [out $ "Unable to unify " ++ show t1 ++ " and " ++ show t2]

tcUnifyVar :: MetaTyVar -> TypeAST -> TypeSubst -> [TypeConstraint] -> Tc UnifySoln
tcUnifyVar (Meta uniq tyref _) ty tysub constraints =
    let tysub' = (Map.insert uniq ty tysub) in
    tcUnifyLoop (tySubstConstraints constraints (Map.singleton uniq ty)) tysub'

