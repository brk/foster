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
    case ty of
        (NamedTypeAST _)     -> fromMaybe ty $ List.lookup ty prvNextPairs
        (PtrTypeAST   _)     -> fromMaybe ty $ List.lookup ty prvNextPairs
        (RefType      _)     -> fromMaybe ty $ List.lookup ty prvNextPairs
        (ArrayType    _)     -> fromMaybe ty $ List.lookup ty prvNextPairs
        (TupleTypeAST types) -> (TupleTypeAST [parSubstTy prvNextPairs t | t <- types])
        (FnTypeAST s t cc cs)-> (FnTypeAST (parSubstTy prvNextPairs s)
                                           (parSubstTy prvNextPairs t)
                                           cc cs) -- TODO unify calling convention?
        (CoroType s t)   -> (CoroType (parSubstTy prvNextPairs s) (parSubstTy prvNextPairs t))
        (ForAll tvs rho) -> let prvNextPairs' = prvNextPairs `assocFilterOut`
                                                     [T_TyVar tv | tv <- tvs] in
                            (ForAll tvs (parSubstTy prvNextPairs' rho))
        (T_TyVar tv)     -> fromMaybe ty $ List.lookup ty prvNextPairs
        (MetaTyVar mtv)  -> fromMaybe ty $ List.lookup ty prvNextPairs


-- Replaces types for meta type variables (unification variables)
-- according to the given type substitution.
tySubst :: TypeAST -> TypeSubst -> TypeAST
tySubst ty subst =
    case ty of
        (NamedTypeAST s)     -> ty
        (RefType    t)       -> RefType    (tySubst t subst)
        (ArrayType  t)       -> ArrayType  (tySubst t subst)
        (PtrTypeAST t)       -> PtrTypeAST (tySubst t subst)
        (TupleTypeAST types) -> (TupleTypeAST [tySubst t subst | t <- types])
        (FnTypeAST s t cc cs)-> (FnTypeAST (tySubst s subst)
                                           (tySubst t subst)
                                           cc cs)
        (CoroType s t)   -> (CoroType (tySubst s subst) (tySubst t subst))
        (ForAll tvs rho) -> (ForAll tvs (tySubst rho subst))
        (T_TyVar tv)     -> ty
        (MetaTyVar (Meta u tyref _))  -> Map.findWithDefault ty u subst

tyEnvSubst :: Context -> TypeSubst -> Context
tyEnvSubst ctx tysub =
    let newBindings = map (\bind ->
                  case bind of
                    TermVarBinding str (AnnVar ty id) ->
                        TermVarBinding str (AnnVar (tySubst ty tysub) id))
                  (contextBindings ctx) in
    ctx { contextBindings = newBindings }

tySubstConstraints constraints tysub =
    [TypeConstrEq (tySubst t1 tysub) (tySubst t2 tysub) | TypeConstrEq t1 t2 <- constraints]

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
                              else tcFails (out $ "Unable to unify different named types: "
                                              ++ n1 ++ " vs " ++ n2)

                ((TupleTypeAST tys1), (TupleTypeAST tys2)) ->
                    if List.length tys1 /= List.length tys2
                      then tcFails $ out "Unable to unify tuples of different lengths!"
                      else tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints) tysub

                ((FnTypeAST a1 a2 cc1 _), (FnTypeAST b1 b2 cc2 _)) ->
                  if cc1 == cc2 || (cc1 == FastCC && cc2 == CCC) then
                    -- We can implicitly convert a CCC to a FastCC
                    -- (but not the other way 'round) using implicitly-inserted
                    -- coercions during lowering to LLVM.
                    tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub
                  else tcFails (out $ "Cannot unify function types with different calling conventions: "
                                    ++ show cc1 ++ " vs " ++ show cc2)

                ((CoroType a1 a2), (CoroType b1 b2)) ->
                    tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub

                -- TODO: ForAll: alpha-equivalence?
                -- TODO: T_TyVar -- alpha equivalence?

                ((MetaTyVar m), ty) ->
                    tcUnifyVar m ty tysub constraints
                (ty, (MetaTyVar m)) ->
                    tcUnifyVar m ty tysub constraints

                ((RefType t1), (RefType t2)) ->
                    tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

                ((PtrTypeAST t1), (PtrTypeAST t2)) ->
                    tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

                otherwise ->
                    tcFails $ out ("Unable to unify " ++ show t1 ++ " and " ++ show t2)

tcUnifyVar :: MetaTyVar -> TypeAST -> TypeSubst -> [TypeConstraint] -> Tc UnifySoln
tcUnifyVar (Meta uniq tyref _) ty tysub constraints =
    let tysub' = (Map.insert uniq ty tysub) in
    tcUnifyLoop (tySubstConstraints constraints (Map.singleton uniq ty)) tysub'

