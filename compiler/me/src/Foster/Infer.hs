{-# LANGUAGE Strict #-}
module Foster.Infer(
    tcUnifyTypes, tcUnifyFT, tcUnifyCC, tcUnifyKinds
  , parSubstTcTy
  , tySubst
  , unify, collectUnboundUnificationVars, zonkType
) where

import Prelude hiding ((<$>))

import Data.Map(Map)
import qualified Data.Map as Map(findWithDefault)
import qualified Data.List as List(length, elem, lookup, nub, sortBy)
import qualified Data.Set as Set
import Data.Maybe(fromMaybe)
import Text.PrettyPrint.ANSI.Leijen
import Data.UnionFind.IO(descriptor, setDescriptor, equivalent, union)

import Control.Monad(liftM, liftM, liftM2, when)
import Data.IORef(readIORef,writeIORef)

import Foster.Base
import Foster.TypeTC
import Foster.Context
import Foster.Config (OrdRef(ordRef))
import Foster.Output (putDocLn)

----------------------

type TypeSubst = Map Uniq TypeTC

data TypeConstraint = TypeConstrEq TypeTC TypeTC

----------------------

assocFilterOut :: Eq a => [(a,b)] -> [a] -> [(a,b)]
assocFilterOut lst keys = [(a,b) | (a,b) <- lst, not(List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt.
parSubstTcTy :: [(TyVar, TypeTC)] -> TypeTC -> TypeTC
parSubstTcTy prvNextPairs ty =
    let q = parSubstTcTy prvNextPairs in
    case ty of
        TyVarTC  tv _mbk     -> fromMaybe ty $ List.lookup tv prvNextPairs
        MetaTyVarTC   {}     -> ty
        PrimIntTC     {}     -> ty
        TyConTC       {}     -> ty
        TyAppTC     con tys  -> TyAppTC (q con) (map q tys)
        TupleTypeTC k  types -> TupleTypeTC k  (map q types)
        RefTypeTC    t       -> RefTypeTC    (q t)
        ArrayTypeTC  t       -> ArrayTypeTC  (q t)
        FnTypeTC  ss t fx cc cs levels -> FnTypeTC     (map q ss) (q t) (q fx) cc cs levels -- TODO unify calling convention?
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
        TyVarTC       {}       -> ty
        TyConTC       {}       -> ty
        TyAppTC con tys        -> TyAppTC (q con) (map q tys)
        RefTypeTC     t        -> RefTypeTC    (q t)
        ArrayTypeTC   t        -> ArrayTypeTC  (q t)
        TupleTypeTC k types    -> TupleTypeTC k (map q types)
        FnTypeTC  ss t fx cc cs levels -> FnTypeTC     (map q ss) (q t) (q fx) cc cs levels
        ForAllTC  tvs rho      -> ForAllTC  tvs (q rho)
        RefinedTypeTC v e args -> RefinedTypeTC (fmap q v) e args

-------------------------------------------------
illegal (TyVarTC (BoundTyVar {}) _) = True
illegal (ForAllTC {})               = True
illegal _                           = False
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
     (\_ _ -> tcFails [text "Unable to unify disparate proc/func annotations" <> line])

-- Likewise, code like ``run-it read_i32`` will cause a CCC/FastCC mismatch,
-- which will be papered over with a proc wrapper.
tcUnifyCC ucc1 ucc2 = tcUnifyThings ucc1 ucc2
     (\_ _ -> tcWhenVerbose $
        tcLift $ putDoc $ text "WARNING: unable to unify disparate calling conventions" <> line)

tcUnifyKinds uk1 uk2 = tcUnifyThings uk1 uk2
     (\k1 k2 -> tcFails [text "Unable to unify kinds " <> pretty k1 <+> text "and" <+> pretty k2])

-------------------------------------------------

tcUnifyTypes :: TypeTC -> TypeTC -> Tc ()
tcUnifyTypes t1 t2 = tcUnifyLoop [TypeConstrEq t1 t2]

tcUnifyMoreTypes tys1 tys2 constraints =
 tcUnifyLoop ([TypeConstrEq a b | (a, b) <- zip tys1 tys2] ++ constraints)

-------------------------------------------------
tcUnifyLoop :: [TypeConstraint] -> Tc ()
tcUnifyLoop [] = return ()

tcUnifyLoop ((TypeConstrEq t1'0 t2'0):constraints) = do
 t1 <- repr t1'0
 t2 <- repr t2'0

 --tcLift $ putStrLn ("tcUnifyLoop: t1 = " ++ show t1 ++ "; t2 = " ++ show t2)
 if illegal t1 || illegal t2
  then tcFailsMore
        [text "Bound type variables and/or polymorphic types cannot be unified! Unable to unify"
        ,text "\t" <> pretty t1 <> string "\nand\n\t" <> pretty t2
        ,text "t1::", showStructure t1, text "t2::", showStructure t2]
  else do
   case (t1, t2) of
       ((TyAppTC (TyConTC nm1) _tys1), (TyAppTC (TyConTC nm2) _tys2))
          | isEffect nm1 && isEffect nm2 && not (isEffectEmpty t1 && isEffectEmpty t2) -> do
                tcLift $ putDocLn $ text "Unifying effects:"
                                 <$> indent 4 (pretty t1)
                                 <$> indent 4 (pretty t2)
       _ -> return ()
   case (t1, t2) of
    ((PrimIntTC  n1), (PrimIntTC  n2)) ->
          if n1 == n2 then do tcUnifyLoop constraints
            else tcFailsMore [text $ "Unable to unify different primitive types: "
                             ,indent 2 $ pretty n1 <> text " vs " <> pretty n2
                             ]

    ((TyVarTC  tv1 kind1), (TyVarTC  tv2 kind2)) ->
       if tv1 == tv2 then do tcUnifyKinds kind1 kind2
                             tcUnifyLoop constraints
                     else tcFailsMore [text $ "Unable to unify different type variables: "
                                       ++ show tv1 ++ " vs " ++ show tv2]

    (t1@(TyAppTC (TyConTC _nm1) _tys1), t2@(MetaTyVarTC {}))
          | isEffectEmpty t1 -> do
      tcWarn [text "permitting effect subsumption of empty effect and type metavariable " <> pretty t2]
      tcUnifyLoop constraints

    (t1@(TyAppTC (TyConTC _nm1) _tys1), t2@(TyAppTC (TyConTC nm2) _tys2))
          | isEffectEmpty t1 && isEffectExtend nm2 -> do
      tcWarn [text "permitting effect subsumption of empty effect and " <> pretty t2]
      tcUnifyLoop constraints

    ((TyAppTC (TyConTC nm1) _tys1), (TyAppTC (TyConTC nm2) _tys2))
          | isEffectExtend nm1 && isEffectExtend nm2 -> do
      tcUnifyEffects t1 t2 constraints

    ((TyConTC  nam1), (TyConTC  nam2)) ->
      if nam1 == nam2 then do tcUnifyLoop constraints
        else do msg <- getStructureContextMessage
                tcFailsMore [text $ "Unable to unify different type constructors: "
                                  ++ nam1 ++ " vs " ++ nam2,
                             msg]

    ((TyAppTC  con1 tys1), (TyAppTC  con2 tys2)) ->
      tcUnifyMoreTypes (con1:tys1) (con2:tys2) constraints

    ((TupleTypeTC kind1 tys1), (TupleTypeTC kind2 tys2)) ->
        if List.length tys1 /= List.length tys2
          then tcFailsMore [text $ "Unable to unify tuples of different lengths"
                           ++ " ("   ++ show (List.length tys1)
                           ++ " vs " ++ show (List.length tys2)
                           ++ ")."]
          else do tcUnifyKinds kind1 kind2
                  tcUnifyMoreTypes tys1 tys2 constraints

    -- Mismatches between unitary tuple types probably indicate
    -- parsing/function argument handling mismatch.

    ((FnTypeTC  as1 a1 fx1 cc1 ft1 levels1), (FnTypeTC  as2 a2 fx2 cc2 ft2 levels2)) -> do
      (_, lnew1) <- tcReadLevels levels1
      (_, lnew2) <- tcReadLevels levels2
      case () of
        _ | List.length as1 /= List.length as2 ->
          tcFailsMore [string "Unable to unify functions of different arity!\n"
                           <> pretty as1 <> string "\nvs\n" <> pretty as2]

        _ | lnew1 == markedLevel || lnew2 == markedLevel ->
          tcFailsMore [string "Occurs check failed when unifying function types"]

        _ -> do let nu = min lnew1 lnew2
                withTemporaryMarkedLevels levels1 levels2 nu $ do 
                    tcUnifyCC cc1 cc2
                    tcUnifyFT ft1 ft2
                    fx1' <- repr fx1
                    a1'  <- repr a1
                    as1' <- mapM repr as1
                    mapM_ (updateLevel nu) (fx1' : a1' : as1')
                    tcUnifyMoreTypes (fx1' : a1' : as1') (fx2 : a2 : as2) []
                tcUnifyLoop constraints

    ((ForAllTC  ktyvars1 rho1), (ForAllTC  ktyvars2 rho2)) ->
        let (tyvars1, kinds1) = unzip ktyvars1 in
        let (tyvars2, kinds2) = unzip ktyvars2 in
        if List.length tyvars1 /= List.length tyvars2
         then tcFails [string "Unable to unify foralls of different arity!\n" <> pretty t1 <> string "\nvs\n" <> pretty t2]
         else if kinds1 /= kinds2
          then tcFails [text $ "Unable to unify foralls with differently-kinded type variables"]
          else let t1 = rho1 in
               let tySubst = zip tyvars2 (map (\(tv,k) -> TyVarTC  tv (UniConst k)) ktyvars1) in
               let t2 = parSubstTcTy tySubst rho2 in
               tcUnifyLoop ((TypeConstrEq t1 t2):constraints)

    ((RefinedTypeTC (TypedId t1 _n1) _e1 _), (RefinedTypeTC (TypedId t2 _n2) _e2 _)) ->
      -- TODO make sure that n/e match...
      tcUnifyLoop ((TypeConstrEq t1 t2):constraints)

    ((MetaTyVarTC m), ty) -> tcUnifyVar m ty constraints
    (ty, (MetaTyVarTC m)) -> tcUnifyVar m ty constraints

    ((RefTypeTC  t1), (RefTypeTC  t2)) ->
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints)

    ((ArrayTypeTC  t1), (ArrayTypeTC  t2)) -> do
        tcUnifyLoop ((TypeConstrEq t1 t2):constraints)

    ((RefinedTypeTC v _ _), ty) -> do
      tcUnifyLoop ((TypeConstrEq (tidType v) ty):constraints)

    (ty, (RefinedTypeTC v _ _)) -> do
      tcUnifyLoop ((TypeConstrEq ty (tidType v)):constraints)

    _otherwise -> do
      msg <- getStructureContextMessage
      tcFailsMore
        [string "Unable to unify\n\t" <> pretty t1 <> string "\nand\n\t" <> pretty t2
        ,text "t1::", showStructure t1, text "t2::", showStructure t2
        ,msg]

tcUnifyVar :: MetaTyVar TypeTC  -> TypeTC  -> [TypeConstraint] -> Tc ()

tcUnifyVar m1 (MetaTyVarTC m2) constraints =
  if m1 == m2
    then
      -- Ignore attempts to unify a meta type variable with itself.
      tcUnifyLoop constraints
    else do
      tvar1 <- readTcMeta m1
      tvar2 <- readTcMeta m2
      case (tvar1, tvar2) of
        (Unbound lev1, Unbound lev2) -> do
          --tcLift $ putStrLn $ "================ Unifying meta var {" ++ show lev1 ++ "} " ++ show (pretty $ MetaTyVarTC m1)
          --              ++ "\n============================= with {" ++ show lev2 ++ "} " ++ show (pretty $ MetaTyVarTC m2)
          if lev1 > lev2
            then writeTcMetaTC m1 (MetaTyVarTC m2)
            else writeTcMetaTC m2 (MetaTyVarTC m1)
          tcUnifyLoop constraints
        _ -> tcFailsMore [text "Invariant violated! repr returned a bound metavariable!?"]

-- Invariant: ty is not a meta type variable.
tcUnifyVar m ty constraints = do
    {-do
      tcm <- readTcMeta m
      tcLift $ putStrLn $ "================ Unifying meta var " ++ show (pretty $ MetaTyVarTC m) ++ " :: " ++ show (pretty tcm)
                     ++ "\n============================= with " ++ show (pretty $ ty)
    -}
    tvar <- readTcMeta m
    case tvar of
      Unbound level -> do
                       updateLevel level ty
                       writeTcMetaTC m ty
                       tcUnifyLoop (                     constraints)
      BoundTo _ -> do tcFails [text "tcUnifyVar INVARIANT VIOLATED: m was not Unbound"]

instance Pretty ty => Pretty (TVar ty) where
  pretty tvar = case tvar of
                  Unbound _ -> text "Unbound"
                  BoundTo ty -> text "(BoundTo " <> pretty ty <> text " )"

effectExtendTc eff row = TyAppTC (TyConTC "effect.Extend") [eff, row]

-- Once we get type synonyms, this function should have a special case
-- for          (extends SYN empty) ~~> SYN
effectExtendsTc labels eff
  = foldr effectExtendTc eff labels

-- This code was adapted from the Apache-2-licensed implementation of Koka.
-- See https://koka.codeplex.com/license
tcUnifyEffects t1 t2 constraints = do
      (ls1, tl1) <- extractOrderedEffect t1
      (ls2, tl2) <- extractOrderedEffect t2
      (ds1, ds2, labconstraints) <- unifyLabels ls1 ls2 []

      case ({-expandSyn-} tl1, {-expandSyn-} tl2) of
         (MetaTyVarTC m1, MetaTyVarTC m2) | (mtvUniq m1 == mtvUniq m2) && not (null ds1 && null ds2)
             -> do -- trace ("unifyEffect: unification of " ++ show (tp1,tp2) ++ " is infinite") $ return ()
                   tcFails [text "Effect unification produced infinite loop"]
         _   -> do 
                   let unifyTail1 ds tl desc = do
                       tcLift $ putDocLn $ text "unifyTail1 " <> pretty ds <+> pretty tl
                       if null ds then return (tl, [])
                                  else do tv <- newTcUnificationVarEffect desc
                                          return (tv, [TypeConstrEq tl (effectExtendsTc ds tv)] )
                   let unifyTail2 ds tl desc = do
                       tcLift $ putDocLn $ text "unifyTail2 " <> pretty ds <+> pretty tl
                       if null ds then return (tl, [])
                                  else do tv <- newTcUnificationVarEffect desc
                                          return (tv, [TypeConstrEq (effectExtendsTc ds tv) tl] )

                   (tail1, c1) <- unifyTail1 ds1 tl1 "fx.tail1"
                   (tail2, c2) <- unifyTail2 ds2 tl2 "fx.tail2"

                   let c3 = [TypeConstrEq tail1 tail2]

                   tcUnifyLoop (labconstraints ++ c1 ++ c2 ++ c3 ++ constraints)


-- | Unify lists of ordered labels; return the differences.
--unifyLabels :: [Tau] -> [Tau] -> [TypeConstraint] -> Unify ([Tau],[Tau],TypeConstraint)
unifyLabels ls1 ls2 constraints =
   case (ls1,ls2) of
      ([],[])   -> return ([],[],constraints)
      (_ ,[])   -> return ([],ls1,constraints)
      ([],_ )   -> return (ls2,[],constraints)
      (l1:ll1, l2:ll2) ->
        case compare (labelName "unifyLabels.L1" l1) (labelName "unifyLabels.L2" l2) of
          LT -> do (ds1, ds2, cs) <- unifyLabels ll1 ls2 constraints
                   return (ds1, l1:ds2, cs)
          GT -> do (ds1, ds2, cs) <- unifyLabels ls1 ll2 constraints
                   return (l2:ds1, ds2, cs)
          EQ -> do -- TODO what's the difference between unify-then-subst
                   --      versus subst-then-unify?
                   --unify l1 l2  -- for heap effects and kind checks
                   --ll1' <- subst ll1
                   --ll2' <- subst ll2
                   unifyLabels ll1 ll2 (TypeConstrEq l1 l2 : constraints)

isEffectExtend nm = nm == "effect.Extend"
isEffect nm = nm == "effect.Empty" || isEffectExtend nm

isEffectEmpty (TyAppTC (TyConTC nm) _) = nm == "effect.Empty"
isEffectEmpty _ = False

labelName :: String -> TypeTC -> String
labelName _ (TyAppTC (TyConTC nm) _) = nm
labelName msg ty = error $ "labelName(" ++ msg ++ ") used on non-ctor type " ++ show ty

extractEffectExtend :: TypeTC -> Tc ([TypeTC],TypeTC)
extractEffectExtend t
  = case {-expandSyn-} t of
      TyAppTC (TyConTC nm) [l, e] | isEffectExtend nm
        -> do (ls, tl) <- extractEffectExtend e
              ls0 <- extractLabel l
              return (ls0 ++ ls, tl)
      _ -> return ([],t)
  where
    extractLabel :: TypeTC -> Tc [TypeTC]
    extractLabel l
      = case {-expandSyn-} l of
          --TApp (TCon tc) [_,e] | typeConName tc == nameEffectExtend
          TyAppTC (TyConTC nm) [_, _e] | isEffectExtend nm
            -> do (ls,tl) <- extractEffectExtend l
                  sanityCheck (isEmptyEffect tl) $ "Found an embedded open effect type..."
                  return ls
          _ -> return [l]

--extractOrderedEffect :: TypeTC -> Tc ([TypeTC],TypeTC)
extractOrderedEffect tp = do
  (labs,tl) <- extractEffectExtend tp
  labss <- concatMapM expand labs
  let slabs = List.nub $ (List.sortBy (\l1 l2 -> compare (labelName "extractOrderedEffect" l1)
                                                         (labelName "extractOrderedEffect" l2)) labss)
  return (slabs,tl)
  where
    expand l = do
      (ls,tl) <- extractEffectExtend l
      return $
         if isEffectEmpty tl && not (null ls)
            then ls
            else [l]

tcWriteLevelNew ZeroLevels _nu = return () -- no need!
tcWriteLevelNew (Levels _old new) nu = do
  tcLift $ writeIORef (ordRef new) nu

updateLevel :: Level -> TypeTC -> Tc ()
updateLevel level typ = do
  let go = updateLevel level
  case typ of
    PrimIntTC {}            -> return ()
    TyConTC   {}            -> return ()
    TyVarTC   {}            -> return ()
    TyAppTC  con types      -> mapM_ go (con:types)
    TupleTypeTC _k  types   -> mapM_ go types
    ForAllTC  _tvs rho      -> go rho
    MetaTyVarTC   m         -> do
      tvar <- readTcMeta m
      case tvar of
        Unbound unlev ->
          if unlev == genericLevel
            then tcFails [text "Update level applied to generic type variable!"]
            else if level < unlev
                   then do tcLift $ putStrLn $ "updateLevel overwriting " ++  show unlev ++ " with " ++ show level ++ " for " ++ show typ
                           tcLift $ writeIORef (mtvRef m) (Unbound level)
                   else return ()
        BoundTo _ -> do t' <- repr typ
                        --tcLift $ putStrLn $ "updateLevel peeked through repr " ++ show m ++ " to get " ++ show t'
                        go t'
        
                                      {-
        BoundTo _t -> tcFailsMore [text "Update level applied to bound meta type variable!",
                                   text (show m),
                                   pretty _t]
                                   -}
        --BoundTo _ -> return ()

    RefTypeTC     ty        -> go ty
    ArrayTypeTC   ty        -> go ty
    RefinedTypeTC v _ _     -> go (tidType v)
    FnTypeTC  ss r fx _ _ levels -> do
      (lold, lnew) <- tcReadLevels levels
      case () of
        _ | lnew == genericLevel -> tcFails [text "Escaped generic level..."]
        _ | lnew == markedLevel  -> tcFails [text "Type checking encountered a circular type..."]
        _ | lnew <= level -> return () -- No adjustment needed
        _ -> do
          when (lnew == lold) $ tcNeedsLevelAdjustment typ
          tcWriteLevelNew levels level
      --concatMap go (r:fx:ss)

withTemporaryMarkedLevels levels1 levels2 newlevel action = do
  tcWriteLevelNew levels1 markedLevel
  tcWriteLevelNew levels2 markedLevel

  rv <- action

  tcWriteLevelNew levels1 newlevel
  tcWriteLevelNew levels2 newlevel

  return rv

collectUnboundUnificationVars :: [TypeTC] -> Tc [MetaTyVar TypeTC]
collectUnboundUnificationVars xs = do
  xs' <- mapM zonkType xs
  --xs' <- mapM repr xs -- causes 'Inconsistent effects at call sites' on test-range
  return $ [m | m <- collectAllUnificationVars xs' , not $ isForIntLit m]
    where isForIntLit m = mtvDesc m == "int-lit"

collectAllUnificationVars :: [TypeTC] -> [MetaTyVar TypeTC]
collectAllUnificationVars xs = Set.toList (Set.fromList (concatMap go xs))
  where go x =
          case x of
            PrimIntTC  _            -> []
            TyConTC  {}             -> []
            TyAppTC  con types      -> concatMap go (con:types)
            TupleTypeTC _k  types   -> concatMap go types
            FnTypeTC  ss r fx _ _ _ -> concatMap go (r:fx:ss)
            ForAllTC  _tvs rho      -> go rho
            TyVarTC       {}        -> []
            MetaTyVarTC   m         -> [m]
            RefTypeTC     ty        -> go ty
            ArrayTypeTC   ty        -> go ty
            RefinedTypeTC v _ _     -> go (tidType v)

-- As in the paper, zonking recursively eliminates indirections
-- from instantiated meta type variables.
zonkType :: TypeTC -> Tc TypeTC
-- {{{
zonkType x = do
    case x of
        MetaTyVarTC m -> do mty <- readTcMeta m
                            case mty of
                              Unbound _ -> do --debugDoc $ string "unable to zonk meta " <> pretty x
                                              return x
                              BoundTo ty -> do ty' <- zonkType ty >>= return
                                               writeTcMetaTC m ty'
                                               return ty'
        PrimIntTC     {}        -> return x
        TyVarTC       {}        -> return x
        TyConTC  nm             -> return $ TyConTC nm
        TyAppTC  con types      -> liftM2 TyAppTC (zonkType con) (mapM zonkType types)
        TupleTypeTC k  types    -> liftM  (TupleTypeTC k) (mapM zonkType types)
        ForAllTC    tvs  rho    -> liftM  (ForAllTC tvs ) (zonkType rho)
        RefTypeTC       ty      -> liftM  (RefTypeTC    ) (zonkType ty)
        ArrayTypeTC     ty      -> do --debug $ "zonking array ty: " ++ show ty
                                      liftM (ArrayTypeTC  ) (zonkType ty)
        RefinedTypeTC (TypedId ty id) e __args   -> liftM (\t -> RefinedTypeTC (TypedId t id) e __args) (zonkType ty)
        FnTypeTC ss r fx cc cs levels -> do
                                      ss' <- mapM zonkType ss
                                      r' <- zonkType r
                                      fx' <- zonkType fx
                                      return $ FnTypeTC ss' r' fx' cc cs levels
-- }}}

-- {{{ Unification driver
-- If unification fails, the provided error message (if any)
-- is printed along with the unification failure error message.
-- If unification succeeds, each unification variable in the two
-- types is updated according to the unification solution.
unify :: TypeTC -> TypeTC -> [Doc] -> Tc ()
unify t1 t2 msgs = do tcOnError msgs (tcUnifyTypes t1 t2) return
                            {-
  where
     occurdCheck m t = do b <- zonkType (MetaTyVarTC m)
                          tcFailsMore $ [text $ "Occurs check for"
                               ,indent 8 (pretty (MetaTyVarTC m))
                               ,text "which is bound to"
                               ,indent 8 (pretty b)
                               ,text "failed in"
                               ,indent 8 (pretty t)
                               ] ++ msgs ++
                               [text "This type error generally arises when different parts of your"
                               ,text "program disagree about whether they are dealing with a polymorphic"
                               ,text "type such as `List a` or just `a`."
                               ,text "This is sometimes caused by swapped function arguments..."
                               ,text "Less commonly, it arises from use of"
                               ,text "polymorphic recursion, which usually needs an explicit annotation"
                               ,text "on both the recursive call site and the recursive function definition."
                               ,indent 4 (text "(Incidentally, in case you're curious, the reason"
                                      <$> text " this is a problem the compiler can't just solve for you"
                                      <$> text " is that it requires higher-order unification, which is"
                                      <$> text " undecidable in theory. And that's not great because it"
                                      <$> text " would make the compiler slow(er) and fragile(r)...)")]
                                      -}
-- }}}
