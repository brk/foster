module Foster.Infer(
    tcUnifyTypes
  , parSubstTy
  , tySubst
  , extractSubstTypes
) where

import Data.Map(Map)
import qualified Data.Map as Map(lookup, empty, insert, findWithDefault, singleton)
import qualified Data.List as List(length, elem, lookup)
import Data.Maybe(fromMaybe)
import Text.PrettyPrint.ANSI.Leijen

import Foster.Base
import Foster.TypeAST
import Foster.Context

----------------------

type TypeSubst = Map Uniq TypeAST

type UnifySoln = Maybe TypeSubst

data TypeConstraint = TypeConstrEq TypeAST TypeAST

emptyTypeSubst = Map.empty

----------------------

extractSubstTypes :: [MetaTyVar TypeAST] -> TypeSubst -> Tc [TypeAST]
extractSubstTypes metaVars tysub = do
    mapM lookup metaVars where
         lookup m =
               fromMaybe (return $ MetaTyVar m)
                         (fmap return $ Map.lookup (mtvUniq m) tysub)

assocFilterOut :: Eq a => [(a,b)] -> [a] -> [(a,b)]
assocFilterOut lst keys = [(a,b) | (a,b) <- lst, not(List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt.
parSubstTy :: [(TyVar, TypeAST)] -> TypeAST -> TypeAST
parSubstTy prvNextPairs ty =
    let q = parSubstTy prvNextPairs in
    case ty of
        TyVarAST tv          -> fromMaybe ty $ List.lookup tv prvNextPairs
        MetaTyVar  {}        -> ty
        PrimIntAST _         -> ty
        PrimFloat64AST       -> ty
        TyConAppAST nm tys   -> TyConAppAST nm (map q tys)
        TupleTypeAST types   -> TupleTypeAST (map q types)
        RefTypeAST   t       -> RefTypeAST   (q t)
        ArrayTypeAST t       -> ArrayTypeAST (q t)
        FnTypeAST ss t p cc cs -> FnTypeAST    (map q ss) (q t) p cc cs -- TODO unify calling convention?
        CoroTypeAST s t      -> CoroTypeAST (q s) (q t)
        ForAllAST ktvs rho   ->
                let prvNextPairs' = prvNextPairs `assocFilterOut` (map fst ktvs)
                in  ForAllAST ktvs (parSubstTy prvNextPairs' rho)

-- Replaces types for meta type variables (unification variables)
-- according to the given type substitution.
tySubst :: TypeSubst -> TypeAST -> TypeAST
tySubst subst ty =
    let q = tySubst subst in
    case ty of
        MetaTyVar m            -> Map.findWithDefault ty (mtvUniq m) subst
        PrimIntAST   {}        -> ty
        PrimFloat64AST         -> ty
        TyVarAST     {}        -> ty
        TyConAppAST  nm tys    -> TyConAppAST  nm (map q tys)
        RefTypeAST    t        -> RefTypeAST   (q t)
        ArrayTypeAST  t        -> ArrayTypeAST (q t)
        TupleTypeAST types     -> TupleTypeAST (map q types)
        FnTypeAST ss t p cc cs -> FnTypeAST    (map q ss) (q t) p cc cs
        CoroTypeAST s t        -> CoroTypeAST (q s) (q t)
        ForAllAST tvs rho      -> ForAllAST tvs (q rho)

-------------------------------------------------
illegal (TyVarAST (BoundTyVar _)) = True
illegal (ForAllAST {})            = True
illegal _                        = False
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

tcUnifyLoop ((TypeConstrEq (PrimIntAST I32) (PrimIntAST I32)):constraints) tysub
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
    (PrimFloat64AST, PrimFloat64AST) -> tcUnifyLoop constraints tysub
    ((PrimIntAST n1), (PrimIntAST n2)) ->
      if n1 == n2 then tcUnifyLoop constraints tysub
                  else do msg <- getStructureContextMessage
                          tcFailsMore [text $ "Unable to unify different primitive types: "
                                       ++ show n1 ++ " vs " ++ show n2
                                       , msg]

    ((TyVarAST tv1), (TyVarAST tv2)) ->
       if tv1 == tv2 then tcUnifyLoop constraints tysub
                     else tcFailsMore [text $ "Unable to unify different type variables: "
                                       ++ show tv1 ++ " vs " ++ show tv2]

    ((TyConAppAST nm1 tys1), (TyConAppAST nm2 tys2)) ->
      if nm1 == nm2
        then tcUnifyMoreTypes tys1 tys2 constraints tysub
        else do msg <- getStructureContextMessage
                tcFailsMore [text $ "Unable to unify different type constructors: "
                                  ++ nm1 ++ " vs " ++ nm2,
                             msg]

    ((TupleTypeAST tys1), (TupleTypeAST tys2)) ->
        if List.length tys1 /= List.length tys2
          then tcFailsMore [text $ "Unable to unify tuples of different lengths"
                           ++ " ("   ++ show (List.length tys1)
                           ++ " vs " ++ show (List.length tys2)
                           ++ ")."]
          else tcUnifyMoreTypes tys1 tys2 constraints tysub

    -- Mismatches between unitary tuple types probably indicate
    -- parsing/function argument handling mismatch.

    ((FnTypeAST as1 a1 p1 _cc1 _), (FnTypeAST as2 a2 p2 _cc2 _)) -> do
        case (p1, p2) of
          (Nothing, Nothing) -> return ()
          _ -> tcLift $ do putStrLn $ "TODO: type inference `unifying' preconditions"
                           putStrLn $ "\t" ++ show p1
                           putStrLn $ "and"
                           putStrLn $ "\t" ++ show p2
        if List.length as1 /= List.length as2
          then tcFailsMore [string "Unable to unify functions of different arity!\n"
                           <> pretty as1 <> string "\nvs\n" <> pretty as2]
          else tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip as1 as2]
                         ++ (TypeConstrEq a1 a2):constraints) tysub

    ((CoroTypeAST a1 a2), (CoroTypeAST b1 b2)) ->
        tcUnifyLoop ((TypeConstrEq a1 b1):(TypeConstrEq a2 b2):constraints) tysub

    ((ForAllAST ktyvars1 rho1), (ForAllAST ktyvars2 rho2)) ->
        let (tyvars1, kinds1) = unzip ktyvars1 in
        let (tyvars2, kinds2) = unzip ktyvars2 in
        if List.length tyvars1 /= List.length tyvars2
         then tcFails [string "Unable to unify foralls of different arity!\n" <> pretty t1 <> string "\nvs\n" <> pretty t2]
         else if kinds1 /= kinds2
          then tcFails [text $ "Unable to unify foralls with differently-kinded type variables"]
          else let t1 = rho1 in
               let tySubst = zip tyvars2 (map (\(tv,_) -> TyVarAST tv) ktyvars1) in
               let t2 = parSubstTy tySubst rho2 in
               tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((MetaTyVar m), ty) -> tcUnifyVar m ty tysub constraints
    (ty, (MetaTyVar m)) -> tcUnifyVar m ty tysub constraints

    ((RefTypeAST t1), (RefTypeAST t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    ((ArrayTypeAST t1), (ArrayTypeAST t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints) tysub

    _otherwise -> do
      msg <- getStructureContextMessage
      tcFailsMore
        [string "Unable to unify\n\t" <> pretty t1 <> string "\nand\n\t" <> pretty t2
        ,text "t1::", showStructure t1, text "t2::", showStructure t2
        ,msg]

instance Show TypeAST where show t = show (pretty t)
instance Show (Wrapped_ExprAST) where show (Wrapped_ExprAST e) = show e

tcUnifyVar :: MetaTyVar TypeAST -> TypeAST -> TypeSubst -> [TypeConstraint] -> Tc UnifySoln

-- Ignore attempts to unify a meta type variable with itself.
tcUnifyVar m1 (MetaTyVar m2) tysub constraints | m1 == m2
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

