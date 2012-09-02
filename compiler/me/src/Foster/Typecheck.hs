-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.Typecheck(tcSigmaToplevel, tcContext) where

import qualified Data.List as List(length, zip)
import Data.List(foldl', (\\))
import Control.Monad(liftM, forM_, forM, liftM, liftM2, when)

import qualified Data.Text as T(Text, unpack)
import qualified Data.Map as Map(lookup, insert, elems, toList, null)
import qualified Data.Set as Set(toList, fromList)
import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Foster.Base
import Foster.TypeAST
import Foster.ExprAST
import Foster.AnnExpr
import Foster.Infer
import Foster.Context
import Foster.TypecheckInt(sanityCheck, typecheckInt, typecheckRat)
import Foster.Output(out, OutputOr(Errors))
import Foster.Output(outCS, runOutput)
import System.Console.ANSI

data TCWanted = TCSigma | TCRho deriving Show

-----------------------------------------------------------------------
-- The type inference algorithm implemented here is based on the one
-- presented by Peyton Jones, Vytiniotis, Weirich, and Shields in the
-- paper ``Practical type inference for arbitrary-rank types.''
--
-- A few quick notes:
--   * A type may be polymorphic or monomorphic, depending on whether it
--     contains any foralls (ForAllAST).
--
--   * Polymorphic types are further (conceptually) divided into
--     those which may begin with a forall (sigma types), and those
--     which never have a forall as the topmost type constructor (rho types).
--
--   * Type checking can proceed in "rho mode" or "sigma mode."
--     For example, when checking the type of `e` in the expression
--     `(prim deref e)`, we operate in rho mode because a correct program
--     will never give `e` a type beginning with a forall.
--     The only place in the algorithm where the mode makes a difference is
--     for variables, where rho-mode induces an instantiation after inferring
--     a polymorphic type.
--
--   * The type inference algorithm is bidirectional. In the paper,
--     bidirectionality is achieved by passing in either an expected type, or
--     a mutable reference variable serving as an "output parameter."
--     We don't need the output parameter aspect, because we're doing type-
--     directed translation along with inference, but we keep it regardless
--     because it's a cheap sanity check for not ignoring the expected type.
--
--   * To force an expression to be typechecked in pure inference mode,
--     try the following construct: case INFER of _ -> ... end.
--
--   * To force an expression to be checked against a meta type variable,
--     the easiest approach is to use a reference store operation: METATY >^ r.
--
--   * To force an expression to be checked against a particular type,
--     write { f : { T => () }   =>   f EXPR }
--
--   * See the rule for typechecking boolean constants for an example of
--     how the expected type can be used to improve error messages.
--
--   * Unlike the language from the paper, we allow programmers to explicitly
--     instantiate polymorphic types. This provides a nice way of supporting
--     impredicative instantiation and polymorphic recursion.
--

-----------------------------------------------------------------------

tcSigmaToplevel (TermVarBinding txt tid) ctx ast = do
-- {{{
    -- Make sure the (potentially user-supplied) type annotation is well-formed.
    tcTypeWellFormed ("in the type declaration for " ++ T.unpack txt)
                     ctx (tidType tid)

    debug $ "tcSigmaToplevel deferring to checkSigmaDirect with expected type " ++ show (tidType tid)
    e <- checkSigmaDirect ctx ast (tidType tid)
    debug $ "tcSigmaToplevel returned expression with type " ++ show (typeAST e)

    return e
-- }}}

inferSigma :: Context TypeAST -> Term -> String -> Tc (AnnExpr Sigma)
-- {{{
-- Special-case variables and function literals
-- to avoid a redundant instantation + generalization
inferSigma ctx (E_VarAST rng v) _msg = tcSigmaVar ctx rng (evarName v)
inferSigma ctx (E_FnAST f)       msg = do r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                                          tcSigmaFn  ctx f (Infer r)
inferSigma ctx (E_CallAST   rng base argtup) msg = do
                r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                tcSigmaCall     ctx rng   base argtup (Infer r)
inferSigma ctx e msg = do
    debug $ "inferSigma " ++ highlightFirstLine (rangeOf e)
    debug $ "inferSigma deferring to inferRho"
    e' <- inferRho ctx e msg
    debug $ "inferSigma inferred :: " ++ show (typeAST e')
    env_tys <- getEnvTypes ctx
    env_tvs <- collectUnboundUnificationVars env_tys
    res_tvs <- collectUnboundUnificationVars [typeAST e']
    let forall_tvs = res_tvs \\ env_tvs
    case forall_tvs of
      [] -> return ()
      _ -> tcFails [out $ "inferSigma ought to quantify over the escaping meta type variables " ++ show (map MetaTyVar forall_tvs)]
    return e'
-- }}}

checkSigma :: Context TypeAST -> Term -> Sigma -> Tc (AnnExpr Sigma)
-- {{{
checkSigma ctx e sigma = do
    (skol_tvs, rho) <- skolemize sigma
    debug $ "checkSigma " ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show sigma
    debug $ "checkSigma used " ++ show skol_tvs ++ " to skolemize " ++ show sigma ++ " to " ++ show rho
    debug $ "checkSigma deferring to checkRho for: " ++ highlightFirstLine (rangeOf e)

    ann <- checkRho ctx e rho
    env_tys <- getEnvTypes ctx
    esc_tvs <- getFreeTyVars (sigma : env_tys)
    let bad_tvs = filter (`elem` esc_tvs) skol_tvs
    debug $ "checkSigma escaping types from were " ++ show esc_tvs ++ "; bad tvs were " ++ show bad_tvs ++ highlightFirstLine (rangeOf e)
    sanityCheck (null bad_tvs)
                ("Type not polymorphic enough")
    return ann
-- }}}


checkSigmaDirect :: Context TypeAST -> Term -> Sigma -> Tc (AnnExpr Sigma)
-- {{{
checkSigmaDirect ctx (E_FnAST fn) sigma@(ForAllAST {}) = do
    tcSigmaFn ctx fn (Check sigma)

checkSigmaDirect _ctx _ (ForAllAST {}) =
    tcFails [out $ "checkSigmaDirect: can't check a sigma type against an "
                ++ "arbitrary expression"]

checkSigmaDirect ctx e rho = checkRho ctx e rho
-- }}}

checkRho :: Context Sigma -> Term -> Rho -> Tc (AnnExpr Rho)
-- Invariant: the Rho is always in weak-prenex form
-- {{{
checkRho ctx e ty = do
    debug $ "checkRho " ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show ty
    debug $ "checkRho deferring to tcRho"
    tcRho ctx e (Check ty)
-- }}}

inferRho :: Context Sigma -> Term -> String -> Tc (AnnExpr Rho)
-- {{{
inferRho ctx e msg = do
    ref <- newTcRef (error $ "inferRho: empty result: " ++ msg)
    debug $ "inferRho " ++ highlightFirstLine (rangeOf e)
    debug $ "inferRho deferring to tcRho"
    a <- tcRho ctx e (Infer ref)
    a <- inst a "inferRho"
    debug $ "tcRho (" ++ msg ++") finished, reading inferred type from ref"
    debug $ "tcRho (" ++ msg ++"): " ++ highlightFirstLine (rangeOf e)
    ty <- tcLift $ readIORef ref
    debug $ "inferRho (" ++ msg ++")" ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show ty
    debug $ "inferRho (" ++ msg ++")" ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show (typeAST a)
    sanityCheck (isRho $ typeAST a) ("inferRho wound up with a sigma type!" ++ highlightFirstLine (rangeOf a))
    return a

-- }}}

tcRho :: Context Sigma -> Term -> Expected Rho -> Tc (AnnExpr Rho)
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
tcRho ctx expr expTy = do
  when tcVERBOSE $ do
    tcLift $ runOutput $ outCS Green ("typecheck: ") ++ textOf expr 0 ++ out (" <=? " ++ show expTy)
    tcLift $ putStrLn ""
  tcWithScope expr $ do
    case expr of
      E_VarAST    rng v              -> tcRhoVar      ctx rng (evarName v) expTy
      E_IntAST    rng txt -> (typecheckInt rng txt (expMaybe expTy)) >>= (\v -> matchExp expTy v "tcInt")
      E_RatAST    rng txt -> (typecheckRat rng txt (expMaybe expTy)) >>= (\v -> matchExp expTy v "tcRat")
      E_BoolAST   rng b              -> tcRhoBool         rng   b          expTy
      E_StringAST rng txt            -> tcRhoText         rng   txt        expTy
      E_CallAST   rng base argtup    -> tcRhoCall     ctx rng   base argtup expTy
      E_TupleAST (TupleAST rng exps) -> tcRhoTuple    ctx rng   exps       expTy
      E_IfAST   rng a b c            -> tcRhoIf       ctx rng   a b c      expTy
      E_FnAST f                      -> tcRhoFn       ctx       f          expTy
      E_LetRec rng bindings e        -> tcRhoLetRec   ctx rng   bindings e expTy
      E_LetAST rng binding  e        -> tcRhoLet      ctx rng   binding  e expTy
      E_TyApp  rng e types           -> tcRhoTyApp    ctx rng   e types    expTy
      E_Case   rng a branches        -> tcRhoCase     ctx rng   a branches expTy
      E_AllocAST rng a rgn           -> tcRhoAlloc    ctx rng   a rgn      expTy
      E_StoreAST rng e1 e2           -> tcRhoStore    ctx rng   e1 e2      expTy
      E_DerefAST rng e1              -> tcRhoDeref    ctx rng   e1         expTy
      E_SeqAST rng a b               -> tcRhoSeq      ctx rng   a b        expTy
      E_UntilAST rng cond body       -> tcRhoUntil    ctx rng   cond body  expTy
      E_ArrayRead rng (ArrayIndex a b _ s) -> do -- a[b]
              ta <- inferRho ctx a "array read base"
              tb <- inferRho ctx b "array read index"
              tcRhoArrayRead rng s ta tb expTy
      E_ArrayPoke rng (ArrayIndex b c _ s) a -> do -- a >^ b[c]
              ta <- inferRho ctx a "array poke val"
              tb <- checkRho ctx b (ArrayTypeAST (typeAST ta))
              tc <- inferRho ctx c "array poke idx"
              tcRhoArrayPoke rng s ta tb tc expTy
      E_CompilesAST rng maybe_expr -> do
          result <- case maybe_expr of
                      Nothing -> return $ Errors [out $ "parse error"]
                      Just  e -> tcIntrospect (inferSigma ctx e "compiles")
          -- Note: we infer a sigma, not a rho, because we don't want to
          -- instantiate a sigma with meta vars and then never bind them.
          matchExp expTy (AnnCompiles rng (CompilesResult result)) "compiles"
      E_KillProcess rng (E_StringAST _ msg) -> do
          tau <- case expTy of
             (Check t) -> return t
             (Infer _) -> newTcUnificationVarTau $ "kill-process"
          matchExp expTy (AnnKillProcess rng tau msg) "kill-process"
      E_KillProcess _rng _ -> tcFails [out $ "prim kill-process requires a string literal"]

matchExp expTy ann msg =
     case expTy of
         Check s@(ForAllAST {}) -> do
                       debug $ "matchExp[Check]("++msg++") deferring to subsCheck"
                       subsCheck ann s msg
         Check t -> do debug $ "matchExp[Check]("++msg++") deferring to subsCheckRho"
                       subsCheckRho ann t
         Infer r -> do update r (return ann)

-- First, an interesting pair of rules for variables:
--
--
--  G contains v ::: s             G has v as primitive
--  ------------------     or      -----------------------
--  G |- v ~~> v ::: s             G |- v ~~> prim v ::: s
tcSigmaVar ctx rng name = do
  tcLift $ runOutput $ outCS Green "typecheckVar (sigma): " ++ out (T.unpack name ++ "...\n")
  -- Resolve the given name as either a variable or a primitive reference.
  let query m = termVarLookup name m
  case (query (contextBindings ctx), query (primitiveBindings ctx)) of
    (Just avar, _        ) -> return $ E_AnnVar     rng avar
    (Nothing  , Just avar) -> return $ AnnPrimitive rng avar
    (Nothing, Nothing) -> do
         msg <- getStructureContextMessage
         tcFails [out $ "Unknown variable " ++ T.unpack name
                  ++ showSourceRange rng
                  ++ "ctx: "++ unlines (map show (Map.toList $ contextBindings ctx))
                  ++ "\nhist: " , msg]

-- To get a rho-type from a variable with a forall type,
-- we wrap it in a type application and infer the type parameters.
-- Variables with non-forall types are left alone.
--
--  G |- v ::: forall x, r
--  -----------------------------
--  G |- v ~~> v:[~t] ::: r[~t/x]
--
--  G |- v ::: r
--  ------------------
--  G |- v ~~> v ::: r
tcRhoVar ctx rng name expTy = do
     when tcVERBOSE $ do
         tcLift $ runOutput $ outCS Green "typecheckVar (rho): " ++ out (T.unpack name ++ " :?: " ++ show expTy)
         tcLift $ putStrLn ""
     v_sigma <- tcSigmaVar ctx rng name
     ann_var <- inst v_sigma "tcRhoVar"
     when tcVERBOSE $ do
         tcLift $ runOutput $ outCS Green "typecheckVar v_sigma: " ++ out (T.unpack name) ++ out " :: " ++ out (show (typeAST v_sigma))
         tcLift $ putStrLn ""
         tcLift $ runOutput $ outCS Green "typecheckVar ann_var: " ++ out (T.unpack name) ++ out " :: " ++ out (show (typeAST ann_var))
         tcLift $ putStrLn ""
     matchExp expTy ann_var "var"

-- Now, a bunch of straightforward rules:

--  -----------------------------------------
--  G |- true :: Bool      G |- false :: Bool
tcRhoBool rng b expTy = do
-- {{{
    let ab = AnnBool rng b
    case expTy of
         Infer  r               -> update r (return ab)
         Check  (PrimIntAST I1) -> return ab
         Check  m@MetaTyVar {}  -> do unify m (PrimIntAST I1) "bool literal"
                                      return ab
         Check  t -> tcFails [out $ "Unable to check Bool constant in context"
                                ++ " expecting non-Bool type " ++ show t
                                ++ showSourceRange rng]
-- }}}

--  ------------------
--  G |- "..." :: Text
tcRhoText rng b expTy = do
-- {{{
    let ab = AnnString rng b
    case expTy of
         Infer r                        -> update r (return ab)
         Check  (TyConAppAST "Text" []) -> return ab
         Check  m@MetaTyVar {} -> do unify m (TyConAppAST "Text" []) "text literal"
                                     return ab
         Check  t -> tcFails [out $ "Unable to check Text constant in context"
                                ++ " expecting non-Text type " ++ show t
                                ++ showSourceRange rng]
-- }}}


--  G |- e1 ::: tau    (should perhaps later change to ())
--  G |- e2 ::: t2
--  -------------------
--  G |- e1 ; e2 ::: t2
-- {{{
tcRhoSeq ctx rng a b expTy = do
    ea <- inferRho ctx a "seq" --(Check $ TupleTypeAST [])
    id <- tcFresh ".seq"
    eb <- tcRho ctx b expTy
    -- Temporary hack to avoid unbound type variables but permit
    -- sequencing of arbitrary types.
    zt <- zonkType (typeAST ea)
    case zt of
      m@MetaTyVar {} -> unify m (TupleTypeAST []) "seq-unit"
      _              -> return ()
    return (AnnLetVar rng id ea eb)
-- }}}


--  G |- e1 ::: tau
--  G |- e2 ::: Ref tau
--  --------------------
--  G |- e1 >^ e2 ::: ()
tcRhoStore ctx rng e1 e2 expTy = do
-- {{{
    a1 <- inferRho ctx e1 "store"
    a2 <- checkRho ctx e2 (RefTypeAST (typeAST a1))
    matchExp expTy (AnnStore rng a1 a2) "store"
-- }}}


--  G |- e   ::: Ref tau
--  --------------------
--  G |- e ^ :::     tau
tcRhoDeref ctx rng e1 expTy = do
-- {{{
    tau <- case expTy of
             (Check t) -> return t
             (Infer _) -> newTcUnificationVarTau $ "deref_type"
    a1 <- tcRho ctx e1 (Check $ RefTypeAST tau)
    case typeAST a1 of
      RefTypeAST {} -> return ()
      MetaTyVar  {} -> return ()
      other -> tcFails [out $ "Expected deref-ed expr "
                           ++ "to have ref type, had " ++ show other ++ highlightFirstLine rng]
    matchExp expTy (AnnDeref rng tau a1) "deref"
-- }}}

--  G |-       e1 :::     tau
--  -------------------------
--  G |- ref_l e1 ::: Ref tau
tcRhoAlloc ctx rng e1 rgn expTy = do
-- {{{
    ea <- case expTy of Check (RefTypeAST t) -> tcRho ctx e1 (Check t)
                        _                    -> inferRho ctx e1 "alloc"
    matchExp expTy (AnnAlloc rng ea rgn) "alloc"
-- }}}

--  G |- e1 ::: t1
--  G |-  .......
--  G |- en ::: tn
--  ------------------------------------
--  G |- (e1, ..., en) ::: (t1, ..., tn)
tcRhoTuple :: Context Sigma -> SourceRange -> [Term] -> Expected TypeAST -> Tc (AnnExpr Rho)
-- {{{
tcRhoTuple ctx rng exprs expTy = do
   tup <- case expTy of
     Infer _                 -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
     Check (TupleTypeAST ts) -> tcTuple ctx rng exprs [Just t  | t <- ts]
     Check (MetaTyVar {}   ) -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
     Check ty -> tcFails [out $ "typecheck: tuple (" ++ show exprs ++ ") "
                             ++ "cannot check against non-tuple type " ++ show ty]
   matchExp expTy tup (highlightFirstLine rng)
  where
    tcTuple ctx rng exps typs = do
        exprs <- typecheckExprsTogether ctx exps typs
        return $ AnnTuple (E_AnnTuple rng exprs)

    -- Typechecks each expression in the same context
    typecheckExprsTogether ctx exprs expectedTypes = do
        sanityCheck (eqLen exprs expectedTypes)
            ("typecheckExprsTogether: had different number of values ("
               ++ (show $ length exprs)
               ++ ") and expected types (" ++ (show $ length expectedTypes)
               ++ ")\nThis might be caused by a missing semicolon!\n"
               ++ show exprs ++ " versus \n" ++ show expectedTypes)
        mapM (\(e,mt) -> case mt of
                          Nothing -> inferRho ctx e "tuple subexpr"
                          Just t  -> checkRho ctx e t)
             (List.zip exprs expectedTypes)
-- }}}

-----------------------------------------------------------------------

-- G |- e1 ::: Array t
-- ---------------------  e2 ::: t2 where t2 is a word-like type
-- G |- e1 [ e2 ]  ::: t
tcRhoArrayRead :: SourceRange -> SafetyGuarantee -> AnnExpr Sigma -> AnnExpr Sigma -> Expected TypeAST -> Tc (AnnExpr Rho)
-- {{{
tcRhoArrayRead rng s base aiexpr expTy = do
  case typeAST base of
    (ArrayTypeAST t) -> do
        -- TODO check aiexpr type is compatible with Word
        unify (PrimIntAST I32) (typeAST aiexpr) "arrayread idx type"
        unify (ArrayTypeAST t) (typeAST base)   "arrayread type"
        let expr = AnnArrayRead rng t (ArrayIndex base aiexpr rng s)
        matchExp expTy expr "arrayread"
    (TupleTypeAST _) ->
        tcFails [out $ "ArrayReading tuples is not allowed; use"
                   ++ " pattern matching instead!" ++ highlightFirstLine rng]
    _ ->
        tcFails [out $ "Unable to arrayread expression of type " ++ show (typeAST base)
                    ++ " (context expected type " ++ show expTy ++ ")"
                    ++ highlightFirstLine rng]
-- }}}

-----------------------------------------------------------------------

-- G |-  v   ::: t
-- G |- b[i] ::: Array t
-- ---------------------
-- G |- v >^ b[i] ::: ()
tcRhoArrayPoke rng s v b i expTy = do
-- {{{
  case typeAST b of
    ArrayTypeAST t -> do
      -- TODO check aiexpr type is compatible with Word
      unify t (typeAST v) "arraypoke type"
      let expr = AnnArrayPoke rng t (ArrayIndex b i rng s) v
      matchExp expTy expr "arraypoke"
    baseType ->
      tcFails [out $ "Unable to arraypoke expression of type " ++ show baseType
                  ++ " (context expected type " ++ show expTy ++ ")"
                  ++ highlightFirstLine rng]
-- }}}

-----------------------------------------------------------------------

--  G |- e1 ::: Bool
--  G |- e2 ::: t2
--  G |- e3 ::: t3
--              t3 <= t2         t2 <= t3
--  -------------------------------------
--  G |- if e1 then e2 else e3 end ::: t2
-- {{{
tcRhoIf ctx rng a b c expTy = do
    ea <- tcRho ctx a (Check fosBoolType)
    eb <- tcRho ctx b expTy
    ec <- tcRho ctx c expTy
    unify (typeAST eb) (typeAST ec) "IfAST: types of branches didn't match"
    -- TODO use subsumption instead of unification?
    return (AnnIf rng (typeAST eb) ea eb ec)
-- }}}

--  G |- cond ::: Bool
--  G |- body ::: sigma
--  ------------------------------------
--  G |- until cond then body end ::: ()
-- {{{
tcRhoUntil ctx rng cond body expTy = do
      acond <- tcRho ctx cond (Check fosBoolType)
      abody <- inferSigma ctx body "until"
      matchExp expTy (AnnUntil rng (TupleTypeAST []) acond abody) "until"
-- }}}

--  G         |- e1 ::: t1
--  G{x:::t1} |- e2 ::: t2
--  ----------------------------
--  G |- let x = e1 in e2 ::: t2
tcRhoLet ctx rng (TermBinding v e1) e2 mt = do
-- {{{
    sanityCheck (not $ isRecursiveFunction boundName e1) errMsg
    id <- tcFreshT boundName
    a1 <- case maybeVarType of
                 Nothing -> inferSigma ctx e1 "let"
                 Just  t -> checkSigma ctx e1 t
    let ctx' = prependContextBindings ctx [bindingForVar $ TypedId (typeAST a1) id]
    a2 <- tcRho ctx' e2 mt
    return (AnnLetVar rng id a1 a2)
  where
    boundName    = evarName v
    maybeVarType = evarMaybeType v
    isRecursiveFunction boundName expr =
                       (boundName `elem` freeVars expr && isFnAST expr)
                  where   isFnAST (E_FnAST _) = True
                          isFnAST _           = False
    -- We'll only warn about recursive function bindings;
    -- shadowing is permissible, and erroneous definitions like
    --     let x = x; in x end
    -- will be caught by the usual variable scoping rules.
    errMsg = "Recursive bindings should use 'rec', not 'let':"
           ++ highlightFirstLine rng
-- }}}

{-
  rec a = body_a;
      b = body_b;
      ...;
   in e end
-}
-- {{{
tcRhoLetRec :: Context Sigma -> SourceRange -> [TermBinding TypeAST]
                -> Term -> Expected TypeAST -> Tc (AnnExpr Rho)
tcRhoLetRec ctx0 rng recBindings e mt = do
    -- Generate unification variables for the overall type of
    -- each binding.
    unificationVars <- sequence [newTcUnificationVarTau $ T.unpack $
                                  "letrec_" `prependedTo` (evarName v)
                                | (TermBinding v _) <- recBindings]
    ids <- sequence [tcFreshT (evarName v) | (TermBinding v _) <- recBindings]
    -- Create an extended context for typechecking the bindings
    let ctxBindings = map (uncurry varbind) (zip ids unificationVars)
    let ctx = prependContextBindings ctx0 ctxBindings
    verifyNonOverlappingBindings rng "rec" ctxBindings

    -- Typecheck each binding
    tcbodies <- forM (zip unificationVars recBindings) $
       (\(u, TermBinding v b) -> do
           vExpTy <- case evarMaybeType v of
             Nothing -> do r <- tcLift $ newIORef (error "case branch")
                           return (Infer r)
             Just  t -> do return (Check t)
           b' <- tcRho ctx b vExpTy
           unify u (typeAST b') ("recursive binding " ++ T.unpack (evarName v))
           return b'
       )

    -- Typecheck the body as well
    e' <- tcRho ctx e mt

    let fns = [f { fnIsRec = Just True } | (E_AnnFn f) <- tcbodies]
    let nonfns = filter notAnnFn tcbodies
                  where notAnnFn (E_AnnFn _) = False
                        notAnnFn _           = True
    sanityCheck (null nonfns) "Recursive bindings should only contain functions!"
    return $ AnnLetFuns rng ids fns e'
-- }}}

-- G |- e ::: forall a1::k1..an::kn, rho
-- G |- t_n <::: k_n                          (checked later)
-- ------------------------------------------
-- G |- e :[ t1..tn ]  ::: rho{t1..tn/a1..an}
tcRhoTyApp ctx rng e t1tn expTy = do
-- {{{
    debug $ "ty app: inferring sigma type for base..."
    aeSigma <- inferSigma ctx e "tyapp"
    debug $ "ty app: base has type " ++ show (typeAST aeSigma)
    case (t1tn, typeAST aeSigma) of
      ([]  , _           ) -> matchExp expTy aeSigma "empty-tyapp"
      (t1tn, ForAllAST {}) -> do let resolve = resolveType rng (localTypeBindings ctx)
                                 tcLift $ putStrLn $ "local type bindings: " ++ show (localTypeBindings ctx)
                                 tcLift $ putStrLn $ "********raw type arguments: " ++ show t1tn
                                 types <- mapM resolve t1tn
                                 expr <- instWith rng aeSigma types
                                 matchExp expTy expr "tyapp"
      (_        , MetaTyVar _ ) -> do
        tcFails [out $ "Cannot instantiate unknown type of term:"
                ,out $ highlightFirstLine $ rangeOf aeSigma
                ,out $ "Try adding an explicit type annotation."
                ]
      (_        , othertype   ) -> do
        tcFails [out $ "Cannot apply type args to expression of"
                   ++ " non-ForAll type: " ++ show othertype
                ,out $ highlightFirstLine $ rangeOf e]
-- }}}

-- G |- b  ~~> f ::: ((s1 ... sn) -> sr)
-- G |- e1 ~~> a1 ::: t1     t1 <= s1
-- G |-  .......
-- G |- en ~~> an ::: tn     tn <= sn
-- ------------------------------------------
-- G |- b e1 ... en ~~> f a1 ... an ::: sr
-- {{{
tcRhoCall :: Context Sigma -> SourceRange
              -> ExprAST TypeAST -> (TupleAST TypeAST)
              -> Expected TypeAST -> Tc (AnnExpr Rho)
tcRhoCall ctx rng base argstup exp_ty = do
   -- TODO think harder about when it's safe to push exp_ty down
   debug $ "tcRhoCall " ++ show exp_ty
   r <- newTcRef (error $ "tcRho>SigmaCall: empty result: ")
   app <- tcSigmaCall ctx rng base argstup (Infer r)
   instSigma app exp_ty

tryGetVarName (E_VarAST _ v) = T.unpack $ evarName v
tryGetVarName _ = ""

tcSigmaCall ctx rng base argstup exp_ty = do
        annbase <- inferRho ctx base "called base"
        let fun_ty = typeAST annbase
        let argexprs = tupleAstExprs argstup
        debug $ "call: fn type is " ++ show fun_ty
        (args_ty, res_ty) <- unifyFun fun_ty argexprs ("tSC("++tryGetVarName base++")")
        debug $ "call: fn args ty is " ++ show args_ty
        debug $ "call: arg exprs are " ++ show argexprs
        sanityCheck (eqLen argexprs args_ty) $
                "tcSigmaCall expected equal # of arguments! Had "
                ++ (show $ List.length argexprs) ++ "; expected "
                ++ (show $ List.length args_ty)
                ++ highlightFirstLine rng
        annargs <- sequence [checkSigma ctx arg ty | (arg, ty) <- zip argexprs args_ty]
        let args = E_AnnTuple (tupleAstRange argstup) annargs
        debug $ "call: annargs: "
        tcLift $ runOutput $ showStructure (AnnTuple args)
        debug $ "call: res_ty is " ++ show res_ty
        debug $ "call: exp_ty is " ++ show exp_ty
        debug $ "tcRhoCall deferring to instSigma"
        let app = AnnCall rng res_ty annbase args
        debug $ "call: overall ty is " ++ show (typeAST app)
        matchExp exp_ty app "tcSigmaCall"

unifyFun :: Rho -> [a] -> String -> Tc ([Sigma], Rho)
unifyFun (FnTypeAST args res _cc _cs) _args _msg = return (args, res)
unifyFun (ForAllAST {}) _ _ = tcFails [out $ "invariant violated: sigma passed to unifyFun!"]
unifyFun tau args msg = do
        arg_tys <- mapM (\_ -> newTcUnificationVarTau "fn args ty") args
        res_ty <- newTcUnificationVarTau ("fn res ty:" ++ msg)
        unify tau (FnTypeAST arg_tys res_ty FastCC FT_Func) "unifyFun"
        return (arg_tys, res_ty)
-- }}}

-- G{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { x1 : t1 => ... => xn : tn => e } ::: { t1 => ... => tn => tb }
--
-- {{{
tcRhoFn ctx f expTy = do
  sigma <- tcSigmaFn ctx f expTy
  debug $ "tcRhoFn instantiating " ++ show (typeAST sigma)
  inst sigma "tcRhoFn"
-- }}}

-- G{a1:k1}...{an:kn}{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { forall a1:k1, ..., an:kn, x1 : t1 => ... => xn : tn => e } :::
--        forall a1:k1, ..., an:kn,    { t1 => ... =>      tn => tb }
-- {{{
tcSigmaFn ctx f expTy = do
  case (fnTyFormals f) of
    []        -> tcRhoFnHelper ctx f expTy
    tyformals -> do
        let rng = fnAstRange f
        let ktvs = map convertTyFormal tyformals
        taus <- genTauUnificationVarsLike ktvs (\n -> "fn type parameter " ++ show n ++ " for " ++ T.unpack (fnAstName f))

        -- Extend the type environment with the forall-bound variables.
        let extendTypeBindingsWith ktvs =
              foldl' ins (localTypeBindings ctx) (zip taus ktvs)
               where ins m (mtv, (BoundTyVar nm, _k)) = Map.insert nm mtv m
                     ins _ (_ ,  (SkolemTyVar {}, _))= error "ForAll bound a skolem!"

        let extTyCtx = ctx { localTypeBindings = extendTypeBindingsWith ktvs }

        -- While we're munging, we'll also make sure the names are all distinct.
        uniquelyNamedFormals0 <- getUniquelyNamedFormals rng (fnFormals f) (fnAstName f)
        uniquelyNamedFormals <- mapM
                          (retypeTID (resolveType rng $ localTypeBindings extTyCtx))
                          uniquelyNamedFormals0

        -- Extend the variable environment with the function arg's types.
        let extCtx = extendContext extTyCtx uniquelyNamedFormals

        -- Check or infer the type of the body.
        debug $ "inferring type of body of polymorphic function"
        debug $ "\tafter generating meta ty vars for type formals: " ++ show (zip taus ktvs)
        annbody <- case expTy of
           Check (ForAllAST exp_ktvs exp_rho) -> do
            -- Suppose we have something like
            -- f ::  forall a:Boxed, { List a }
            -- f =  { forall b:Boxed,   Nil ! }
            -- Here, we need the expected type to get the right type for
            -- the instantiation of Nil, but we can't use the type variable 'a
            -- in the expression, because only 'b is in scope.
            -- So, we must rewrite rho in terms of the function's type variables
            sanityCheck (eqLen ktvs exp_ktvs)
                       ("tcSigmaFn: expected same number of formals for "
                        ++ show ktvs ++ " and " ++ show exp_ktvs)
            exp_rho' <- resolveType rng (extendTypeBindingsWith exp_ktvs) exp_rho
            let var_tys = map tidType uniquelyNamedFormals
            (arg_tys, body_ty) <- unifyFun exp_rho' var_tys "poly-fn-lit"
            debug $ "calling checkRho for function body..."
            debug $ "checking body against type: " ++ show body_ty
            body <- checkRho extCtx (fnAstBody f) body_ty
            debug $ "called checkRho for function body:"
            tcLift $ runOutput $ showStructure body
            debug $ "\ntype: "
            tcLift $ runOutput $ showStructure (typeAST body)
            return body

            {-
            tcFails [out $ "checking function body against expected sigma type"
                    ,out $ "exp_sigma = " ++ show exp_sigma
                    ,out $ "exp_rho   = " ++ show exp_rho
                    ,out $ "exp_rho'  = " ++ show exp_rho']
                    -}
           Check _      -> inferSigma extCtx (fnAstBody f) "poly-fn body"
           Infer _      -> inferSigma extCtx (fnAstBody f) "poly-fn body"
           {-
             -- TODO: if we permitted functions with un-annotated parameters,
             -- we'd want to use the expected function type to guide their types.

             if isRho ckfnty
              then do
                  let var_tys = map tidType uniquelyNamedFormals
                  (arg_tys, body_ty) <- unifyFun ckfnty var_tys "poly-fn-lit"
                  vartys1 <- mapM shallowZonk var_tys
                  debug $ "&&&& before: " ++ show (zip arg_tys vartys1)
                  _ <- sequence [subsCheckTy argty varty "poly-fn-arg" |
                                          (argty, varty) <- zip arg_tys var_tys]
                  vartys2 <- mapM shallowZonk var_tys
                  debug $ "&&&& after: " ++ show (zip arg_tys vartys2)
                  -- TODO is there an arg translation?
                  checkSigma extCtx (fnAstBody f) body_ty
              else
                 -- Can't call unifyFun because ckfnty may be polymorphic.
                 tcFails [out $ "not yet checking poly fn literals against polymorphic types"
                         ,out $ "expected type is:"
                         ,showStructure ckfnty]
         -}

        debug $ "inferred raw type of body of polymorphic function: " ++ show (typeAST annbody)

        let fnty0 = ForAllAST ktvs $
                fnTypeTemplate f argtys (typeAST annbody) FastCC
                 where argtys = map tidType uniquelyNamedFormals

        -- The function type is expressed in terms of meta type variables,
        -- which have now served their purpose and must be replaced by
        -- bound type variables. We'll do the replacement by first making sure
        -- that nothing has been unified with them so far, and then writing
        -- the appropriate bound type variable to the ref.
        _ <- mapM (\(t, (tv, _)) -> do
                     t' <- shallowZonk t
                     case t' of
                       (MetaTyVar m) -> do
                            debug $ "zonked " ++ show t ++ " to " ++ show t ++ "; writing " ++ show tv
                            writeTcMeta m (TyVarAST tv)
                       y -> tcFails [out $ "expected ty param metavar to be un-unified, instead had " ++ show y]
                  ) (zip taus ktvs)
        -- Zonk the type to ensure that the meta vars are completely gone.
        debug $ "inferred raw overall type of polymorphic function: " ++ show fnty0
        debug $ "zonking; (meta)/tyvars were " ++ show (zip taus ktvs)
        fnty <- zonkType fnty0
        debug $ "inferred overall type of body of polymorphic function: " ++ show fnty

        -- We also need to zonk the expected type, which might have wound up
        -- getting some of its meta type variables unified with taus that now
        -- refer to bound type variables.
        expTy' <- case expTy of
                    Check t -> liftM Check (zonkType t)
                    Infer _ -> return expTy

        -- Note we collect free vars in the old context, since we can't possibly
        -- capture the function's arguments from the environment!
        let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol $ fnAstName f))
                              uniquelyNamedFormals annbody Nothing rng
        debug $ "tcSigmaFn calling matchExp  expTy  = " ++ show expTy
        debug $ "tcSigmaFn calling matchExp, expTy' = " ++ show expTy'
        matchExp expTy' fn "tcSigmaFn"
-- }}}


-- G{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { x1 : t1 => ... => xn : tn => e } ::: { t1 => ... => tn => tb }
-- {{{
tcRhoFnHelper ctx f expTy = do
    let rng = fnAstRange f
    -- While we're munging, we'll also make sure the names are all distinct.
    uniquelyNamedFormals0 <- getUniquelyNamedFormals rng (fnFormals f) (fnAstName f)
    uniquelyNamedFormals <- mapM
                      (retypeTID (resolveType rng $ localTypeBindings ctx))
                      uniquelyNamedFormals0

    -- Extend the variable environment with the function arg's types.
    let extCtx = extendContext ctx uniquelyNamedFormals

    -- Check or infer the type of the body.
    annbody <- case expTy of
      Infer _    -> do inferSigma extCtx (fnAstBody f) "mono-fn body"
      Check fnty -> do let var_tys = map tidType uniquelyNamedFormals
                       (arg_tys, body_ty) <- unifyFun fnty var_tys "@"
                       _ <- sequence [subsCheckTy argty varty "mono-fn-arg" |
                                       (argty, varty) <- zip arg_tys var_tys]
                       -- TODO is there an arg translation?
                       checkRho extCtx (fnAstBody f) body_ty

    let fnty = fnTypeTemplate f argtys (typeAST annbody) FastCC
                where argtys = map tidType uniquelyNamedFormals

    -- Note we collect free vars in the old context, since we can't possibly
    -- capture the function's arguments from the environment!
    let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol $ fnAstName f))
                          uniquelyNamedFormals annbody Nothing rng
    matchExp expTy fn "tcRhoFn"
-- }}}

-- {{{ Helpers for type-checking function literals.
extendContext :: Context Sigma -> [AnnVar] -> Context Sigma
extendContext ctx protoFormals =
                 prependContextBindings ctx (map bindingForVar protoFormals)

fnTypeTemplate f argtypes retty cc =
  -- Compute "base" function type, ignoring any type parameters.
  let procOrFunc = if fnWasToplevel f then FT_Proc else FT_Func in
  FnTypeAST argtypes retty cc procOrFunc

-- | Verify that the given formals have distinct names,
-- | and return unique'd versions of each.
getUniquelyNamedFormals rng rawFormals fnProtoName = do
    verifyNonOverlappingBindings rng (T.unpack fnProtoName)
     [TermVarBinding (identPrefix $ tidIdent v) undefined | v <- rawFormals]
    mapM uniquelyName rawFormals
  where
    uniquelyName :: TypedId t -> Tc (TypedId t)
    uniquelyName (TypedId ty id) = do
        uniq <- newTcUniq
        newid <- rename id uniq
        return (TypedId ty newid)
      where
        rename :: Ident -> Uniq -> Tc Ident
        rename (Ident p _) u = return (Ident p u)
        rename (GlobalSymbol name) _u =
                tcFails [out $ "Cannot rename global symbol " ++ show name]

-- }}}


-- {{{ CASE scrutinee OF branches END
tcRhoCase ctx rng scrutinee branches expTy = do
  -- (A) The expected type applies to the branches,
  --     not to the scrutinee.
  -- (B) Each pattern must check against the scrutinee type.
  -- (C) Each branch must check against the expected type,
  --     as well as successfully unify against the overall type.

  ascrutinee <- inferRho ctx scrutinee "scrutinee"
  u <- newTcUnificationVarTau "case"
  debug $ "case scrutinee has type " ++ show (typeAST ascrutinee)
  debug $ "metavar for overall type of case is " ++ show u
  debug $ " exp ty is " ++ show expTy
  let checkBranch (pat, body) = do
      p <- checkPattern ctx pat (typeAST ascrutinee)
      debug $ "case branch pat: " ++ show p
      let bindings = extractPatternBindings p
      debug $ "case branch generated bindings: " ++ show bindings
      let ctxbindings = [varbind id ty | (TypedId ty id) <- bindings]
      verifyNonOverlappingBindings rng "case" ctxbindings
      abody <- tcRho (prependContextBindings ctx ctxbindings) body expTy
      unify u (typeAST abody) ("Failed to unify all branches of case " ++ show rng)
      return ((p, bindings), abody)
  abranches <- forM branches checkBranch
  matchExp expTy (AnnCase rng u ascrutinee abranches) "case"
 where
    checkPattern :: Context Sigma -> EPattern TypeAST -> TypeAST -> Tc (Pattern TypeAST)
    -- Make sure that each pattern has the proper arity,
    -- and record its type given a known type for the context in which
    -- the pattern appears.
    checkPattern ctx pattern ctxTy = case pattern of
      EP_Wildcard r       -> do return $ P_Wildcard r ctxTy
      EP_Variable r v     -> do checkSuspiciousPatternVariable r v
                                id <- tcFreshT (evarName v)
                                return $ P_Variable r (TypedId ctxTy id)
      EP_Bool     r b     -> do annbool <- tcRho ctx (E_BoolAST r b) (Check ctxTy)
                                return $ P_Bool r (typeAST annbool) b
      EP_Int      r str   -> do annint <- typecheckInt r str (Just ctxTy)
                                return $ P_Int r (aintType annint) (aintLit annint)

      EP_Ctor     r eps s -> do
        info@(CtorInfo cid (DataCtor _ _ tyformals types)) <- getCtorInfoForCtor ctx s
        sanityCheck (ctorArity cid == List.length eps) $
              "Incorrect pattern arity: expected " ++
              (show $ ctorArity cid) ++ " pattern(s), but got "
              ++ (show $ List.length eps) ++ showSourceRange r
        sanityCheck (ctorArity cid == List.length types) $
              "Invariant violated: constructor arity did not match # types!"
              ++ showSourceRange r

        ty@(TyConAppAST _ metas) <-
                            generateTypeSchemaForDataType ctx (ctorTypeName cid)
        let ktvs = map convertTyFormal tyformals
        ts <- mapM (\ty -> instSigmaWith ktvs ty metas) types
        ps <- sequence [checkPattern ctx p t | (p, t) <- zip eps ts]
        tcLift $ putStrLn $ "checkPattern for " ++ show pattern
        tcLift $ putStrLn $ "*** P_Ctor -  ty   " ++ show ty
        tcLift $ putStrLn $ "*** P_Ctor -  ty   " ++ show ctxTy
        tcLift $ putStrLn $ "*** P_Ctor - metas " ++ show metas
        tcLift $ putStrLn $ "*** P_Ctor - sgmas " ++ show ts

        unify ty ctxTy ("checkPattern:P_Ctor " ++ show cid)
        return $ P_Ctor r ty ps info

      EP_Tuple     r eps  -> do
        ts <- case ctxTy of
                TupleTypeAST ts -> return ts
                _ -> do ts <- sequence [newTcUnificationVarTau "tup" | _ <- eps]
                        unify ctxTy (TupleTypeAST ts) "tuple-pattern"
                        return ts
        sanityCheck (eqLen eps ts) $
                "Cannot match pattern against tuple type of "
             ++ "different length." ++ showSourceRange r
        ps <- sequence [checkPattern ctx p t | (p, t) <- zip eps ts]
        return $ P_Tuple r (TupleTypeAST ts) ps
    -----------------------------------------------------------------------
    getCtorInfoForCtor :: Context Sigma -> T.Text -> Tc (CtorInfo Sigma)
    getCtorInfoForCtor ctx ctorName = do
      let ctorInfos = contextCtorInfo ctx
      case Map.lookup ctorName ctorInfos of
        Just [info] -> return info
        elsewise -> tcFails [out $ "Typecheck.getCtorInfoForCtor: Too many or"
                                    ++ " too few definitions for $" ++ T.unpack ctorName
                                    ++ "\n\t" ++ show elsewise]

    generateTypeSchemaForDataType :: Context Sigma -> DataTypeName -> Tc TypeAST
    generateTypeSchemaForDataType ctx typeName = do
      case Map.lookup typeName (contextDataTypes ctx) of
        Just [dt] -> do
          formals <- mapM (\_ -> newTcUnificationVarTau "dt-tyformal") (dataTypeTyFormals dt)
          return $ TyConAppAST typeName formals
        other -> tcFails [out $ "Typecheck.generateTypeSchemaForDataType: Too many or"
                            ++ " too few definitions for $" ++ typeName
                            ++ "\n\t" ++ show other]

    extractPatternBindings :: Pattern TypeAST -> [TypedId Sigma]
    extractPatternBindings (P_Wildcard    {}) = []
    extractPatternBindings (P_Bool        {}) = []
    extractPatternBindings (P_Int         {}) = []
    extractPatternBindings (P_Variable _ tid) = [tid]
    extractPatternBindings (P_Ctor _ _ ps _)  = concatMap extractPatternBindings ps
    extractPatternBindings (P_Tuple _ _ ps)   = concatMap extractPatternBindings ps

    checkSuspiciousPatternVariable rng var =
      if T.unpack (evarName var) `elem` ["true", "false"]
       then tcFails [out $ "Error: this matches a variable, not a boolean constant!"
                      ++ highlightFirstLine rng]
       else return ()
-- }}}

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

subsCheckTy :: Sigma -> Sigma -> String -> Tc ()
-- {{{
subsCheckTy sigma1 sigma2@(ForAllAST {}) msg = do
  (skols, rho) <- skolemize sigma2
  debug $ "subsCheckTy deferring to subsCheckRhoTy"
  subsCheckRhoTy sigma1 rho
  esc_tvs <- getFreeTyVars [sigma1, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skols
  sanityCheck (null bad_tvs) ("subsCheck(" ++ msg ++ "): Type\n" ++ show sigma1 ++
                       " not as polymorphic as\n" ++ show sigma2 ++
                       "\nbad type variables: " ++ show bad_tvs)
  return ()

subsCheckTy sigma1 rho2 _msg = subsCheckRhoTy sigma1 rho2

subsCheckRhoTy :: Sigma -> Rho -> Tc ()
subsCheckRhoTy (ForAllAST ktvs rho) rho2 = do -- Rule SPEC
             taus <- genTauUnificationVarsLike ktvs (\n -> "instSigma type parameter " ++ show n)
             rho1 <- instSigmaWith ktvs rho taus
             subsCheckRhoTy rho1 rho2
subsCheckRhoTy rho1 (FnTypeAST as2 r2 _ _) = unifyFun rho1 as2 "!" >>= \(as1, r1) -> subsCheckFunTy as1 r1 as2 r2
subsCheckRhoTy (FnTypeAST as1 r1 _ _) rho2 = unifyFun rho2 as1 "!" >>= \(as2, r2) -> subsCheckFunTy as1 r1 as2 r2
subsCheckRhoTy tau1 tau2 -- Rule MONO
     = unify tau1 tau2 "subsCheckRho" -- Revert to ordinary unification
-- }}}

subsCheck :: (AnnExpr Sigma) -> Sigma -> String -> Tc (AnnExpr Sigma)
-- {{{
subsCheck esigma sigma2@(ForAllAST {}) msg = do
  (skols, rho) <- skolemize sigma2
  debug $ "subsCheck skolemized sigma to " ++ show rho ++ " via " ++ show skols
                                            ++ ", now deferring to subsCheckRho"
  _ <- subsCheckRho esigma rho
  esc_tvs <- getFreeTyVars [typeAST esigma, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skols
  sanityCheck (null bad_tvs) ("subsCheck(" ++ msg ++ "): Type\n" ++ show (typeAST esigma) ++
                       " not as polymorphic as\n" ++ show sigma2 ++
                       "\nbad type variables: " ++ show bad_tvs)
  return esigma

subsCheck _esigma _rho2 _msg = tcFails [out $ "rho passed to subsCheck!"]

subsCheckRho :: AnnExpr Sigma -> Rho -> Tc (AnnExpr Rho)
subsCheckRho esigma rho2 = do
  case (typeAST esigma, rho2) of
    (_, ForAllAST {}) -> do tcFails [out $ "violated invariant: sigma passed to subsCheckRho"]
    (ForAllAST {}, _) -> do -- Rule SPEC
        debug $ "subsCheckRho instantiating " ++ show (typeAST esigma)
        erho <- inst esigma "subsCheckRho"
        debug $ "subsCheckRho instantiated to " ++ show (typeAST erho)
        debug $ "subsCheckRho inst. type against " ++ show rho2
        subsCheckRho erho rho2

    (rho1, FnTypeAST as2 r2 _ _) -> do debug $ "subsCheckRho fn 1"
                                       (as1, r1) <- unifyFun rho1 as2 "sCR1"
                                       subsCheckFunTy as1 r1 as2 r2
                                       return esigma
    (FnTypeAST as1 r1 _ _, _)    -> do debug "subsCheckRho fn 2"
                                       (as2, r2) <- unifyFun rho2 as1 "sCR2"
                                       debug $ "&&&&&& r1: " ++ show r1
                                       debug $ "&&&&&& r2: " ++ show r2
                                       subsCheckFunTy as1 r1 as2 r2
                                       return esigma
    -- Elide the two FUN rules and subsCheckFun because we're using
    -- shallow, not deep, skolemization due to being a strict language.

    (rho1, _) -> do -- Rule MONO
        unify rho1 rho2 "subsCheckRho" -- Revert to ordinary unification
        return esigma
-- }}}

-- {{{ Helper functions for subsCheckRho to peek inside type constructors
subsCheckFunTy as1 r1 as2 r2 = do
        sanityCheck (eqLen as1 as2) "Function types must have equal-length argument lists"
        debug $ "subsCheckFunTy arg: " ++ show as2 ++ " ?<=? " ++ show as1
        mapM_ (\(a2, a1) -> subsCheckTy a2 a1 "sCFTa") (zip as2 as1)
        debug $ "subsCheckFunTy res: " ++ show r1 ++ " ?<=? " ++ show r2
        subsCheckTy r1 r2 "sCFTr"
        return ()
-- }}}

instSigma :: AnnExpr Sigma -> Expected Rho -> Tc (AnnExpr Rho)
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
instSigma e1 (Check t2) = do {
                             ; debug $ "instSigma " ++ show (typeAST e1) ++ " :?: " ++ show t2
                             ; debug $ "instSigma deferring to subsCheckRho"
                             ; subsCheckRho e1 t2
                             }
instSigma e1 (Infer r)  = do { e <- inst e1 "instSigma"
                             ; debug $ "instSigma " ++ show (typeAST e1) ++ " -inst-> " ++ show (typeAST e)
                             ; tcLift $ writeIORef r (typeAST e)
                             ; return e }

inst :: AnnExpr Sigma -> String -> Tc (AnnExpr Rho)
-- Transform a Sigma type into a Rho type by instantiating the ForAll's
-- type parameters with unification variables.
-- {{{
inst base msg = do
  --zonked <- shallowZonk (typeAST base)
  zonked <- return (typeAST base)
  case zonked of
     ForAllAST ktvs _rho -> do
       taus <- genTauUnificationVarsLike ktvs (\n -> "inst("++msg++") type parameter " ++ vname base n)
       instWith (rangeOf base) base taus
     _rho -> return base

instWith :: SourceRange -> AnnExpr Sigma -> [Tau] -> Tc (AnnExpr Rho)
instWith _          aexpSigma [] = do
        sanityCheck (isRho $ typeAST aexpSigma)
                     "Tried to instantiate a sigma with no types!"
        return aexpSigma

instWith rng aexpSigma taus = do
    instRho <- tryInstSigmaWith (typeAST aexpSigma) taus
    return $ E_AnnTyApp rng instRho aexpSigma taus

tryInstSigmaWith sigma taus = do
  --zonked <- shallowZonk sigma
  zonked <- return sigma
  case zonked of
     ForAllAST ktvs rho -> instSigmaWith ktvs rho taus
     rho                -> return rho

instSigmaWith ktvs rho taus = do
    sanityCheck (eqLen taus ktvs)
                ("Arity mismatch in instSigma: can't instantiate"
                ++ show (List.length ktvs) ++ " type variables with "
                ++ show (List.length taus) ++ " types!")
    let tyvarsAndTys = List.zip (tyvarsOf ktvs) taus
    zonked <- zonkType rho -- Do a deep zonk to ensure we don't miss any vars.
    return $ parSubstTy tyvarsAndTys zonked
-- }}}

-- {{{
resolveType rng subst x =
  let q = resolveType rng subst in
  case x of
    PrimIntAST  _                  -> return x
    PrimFloat64AST                 -> return x
    MetaTyVar   _                  -> return x
    TyVarAST (SkolemTyVar _ _ _)   -> return x
    TyVarAST (BoundTyVar name)     -> case Map.lookup name subst of
                                         Nothing -> tcFails [out $ "Typecheck.hs: ill-formed type with free bound variable " ++ name,
                                                             out $ highlightFirstLine rng]
                                         Just ty -> return ty
    RefTypeAST    ty               -> liftM RefTypeAST   (q ty)
    ArrayTypeAST  ty               -> liftM ArrayTypeAST (q ty)
    FnTypeAST   ss t cc cs         -> do (t':ss') <- mapM q (t:ss)
                                         return $ FnTypeAST ss' t' cc cs
    CoroTypeAST  s t               -> liftM2 CoroTypeAST (q s) (q t)
    TyConAppAST   tc  types        -> liftM (TyConAppAST tc) (mapM q types)
    TupleTypeAST      types        -> liftM  TupleTypeAST    (mapM q types)
    ForAllAST     ktvs rho         -> liftM (ForAllAST ktvs) (resolveType rng subst' rho)
                                       where
                                        subst' = foldl' ins subst ktvs
                                        ins m (tv@(BoundTyVar nm), _k) = Map.insert nm (TyVarAST tv) m
                                        ins _     (SkolemTyVar {}, _k) = error "ForAll bound a skolem!"
-- }}}

-- Turns a type like (forall t, T1 t -> T2 t) into (T1 ~s) -> (T2 ~s)
-- where ~s denotes a skolem type variable. Also returns the generated tyvars.
skolemize :: TypeAST -> Tc ([TyVar], Rho)
-- {{{
skolemize (ForAllAST ktvs rho) = do
     skolems <- mapM newTcSkolem ktvs
     let tyvarsAndTys = List.zip (tyvarsOf ktvs)
                                 (map TyVarAST skolems)
     return (skolems, parSubstTy tyvarsAndTys rho)
skolemize ty = return ([], ty)
-- }}}

getFreeTyVars :: [TypeAST] -> Tc [TyVar]
-- {{{
getFreeTyVars xs = do zs <- mapM zonkType xs
                      return $ Set.toList (Set.fromList $ concatMap (go []) zs)
                 where
  go :: [TyVar] -> Sigma -> [TyVar]
  go bound x =
    case x of
        PrimIntAST _          -> []
        PrimFloat64AST        -> []
        TyConAppAST _nm types -> concatMap (go bound) types
        TupleTypeAST types    -> concatMap (go bound) types
        FnTypeAST ss r _ _    -> concatMap (go bound) (r:ss)
        CoroTypeAST s r       -> concatMap (go bound) [s,r]
        ForAllAST  tvs rho    -> go (tyvarsOf tvs ++ bound) rho
        TyVarAST   tv         -> if tv `elem` bound then [] else [tv]
        MetaTyVar     {}      -> []
        RefTypeAST    ty      -> (go bound) ty
        ArrayTypeAST  ty      -> (go bound) ty
-- }}}

-- As in the paper, zonking recursively eliminates indirections
-- from instantiated meta type variables.
zonkType :: TypeAST -> Tc TypeAST
-- {{{
zonkType x = do
    case x of
        MetaTyVar m -> do mty <- readTcMeta m
                          case mty of
                            Nothing -> return x
                            Just ty -> do ty' <- zonkType ty
                                          writeTcMeta m ty'
                                          return ty'
        PrimIntAST     {}     -> return x
        PrimFloat64AST        -> return x
        TyVarAST       {}     -> return x
        TyConAppAST  nm types -> liftM (TyConAppAST nm) (mapM zonkType types)
        TupleTypeAST    types -> liftM (TupleTypeAST  ) (mapM zonkType types)
        ForAllAST    tvs  rho -> liftM (ForAllAST tvs ) (zonkType rho)
        RefTypeAST       ty   -> liftM (RefTypeAST    ) (zonkType ty)
        ArrayTypeAST     ty   -> do debug $ "zonking array ty: " ++ show ty
                                    liftM (ArrayTypeAST  ) (zonkType ty)
        CoroTypeAST s r       -> liftM2 (CoroTypeAST  ) (zonkType s) (zonkType r)
        FnTypeAST ss r cc cs  -> do ss' <- mapM zonkType ss ; r' <- zonkType r
                                    return $ FnTypeAST ss' r' cc cs

-- We also provide a "shallow" alternative which only peeks at the topmost tycon
shallowZonk :: TypeAST -> Tc TypeAST
shallowZonk (MetaTyVar m) = do
         mty <- readTcMeta m
         case mty of
             Nothing -> return (MetaTyVar m)
             Just ty -> do ty' <- shallowZonk ty
                           writeTcMeta m ty'
                           return ty'
shallowZonk t = return t
-- }}}

-- {{{ Unification driver
-- If unification fails, the provided error message (if any)
-- is printed along with the unification failure error message.
-- If unification succeeds, each unification variable in the two
-- types is updated according to the unification solution.
unify :: TypeAST -> TypeAST -> String -> Tc ()
unify t1 t2 msg = do
  when tcVERBOSE $ do
    tcLift $ runOutput $ outCS Green $ "unify " ++ show t1 ++ " ?==? " ++ show t2 ++ " (" ++ msg ++ ")"
    tcLift $ putStrLn ""
  tcOnError (liftM out (Just msg)) (tcUnifyTypes t1 t2) $ \(Just soln) -> do
     let univars = collectAllUnificationVars [t1, t2]
     forM_ univars $ \m -> do
       mt1 <- readTcMeta m
       case (mt1, Map.lookup (mtvUniq m) soln) of
         (_,       Nothing)          -> return () -- no type to update to.
         (Just x1, Just x2)          -> do unify x1 x2 msg
         -- The unification var m1 has no bound type, but it's being
         -- associated with var m2, so we'll peek through m2.
         (Nothing, Just (MetaTyVar m2)) -> do
                         mt2 <- readTcMeta m2
                         case mt2 of
                             Just x2 -> unify (MetaTyVar m) x2 msg
                             Nothing -> writeTcMeta m (MetaTyVar m2)
         (Nothing, Just x2) -> do unbounds <- collectUnboundUnificationVars [x2]
                                  case m `elem` unbounds of
                                     False   -> writeTcMeta m x2
                                     True    -> occurdCheck m x2
  where
     occurdCheck m t = tcFails [out $ "Occurs check for " ++ show (MetaTyVar m)
                                   ++ " failed in " ++ show t]
-- }}}

-- {{{ Well-formedness checks
-- The judgement   G |- T
tcTypeWellFormed :: String -> Context TypeAST -> TypeAST -> Tc ()
tcTypeWellFormed msg ctx typ = do
  let q = tcTypeWellFormed msg ctx
  case typ of
        PrimIntAST _          -> return ()
        PrimFloat64AST        -> return ()
        MetaTyVar     _       -> return ()
        TyConAppAST nm types  -> case Map.lookup nm (contextDataTypes ctx) of
                                   Just  _ -> mapM_ q types
                                   Nothing -> tcFails [out $ "Unknown type "
                                                        ++ nm ++ " " ++ msg]
        TupleTypeAST types    -> mapM_ q types
        FnTypeAST ss r _ _    -> mapM_ q (r:ss)
        CoroTypeAST s r       -> mapM_ q [s,r]
        RefTypeAST    ty      -> q ty
        ArrayTypeAST  ty      -> q ty
        ForAllAST  tvs rho    -> tcTypeWellFormed msg (extendTyCtx ctx tvs) rho
        TyVarAST (SkolemTyVar {}) -> return ()
        TyVarAST tv@(BoundTyVar _) ->
                 case Prelude.lookup tv (contextTypeBindings ctx) of
                   Nothing -> tcFails [out $ "Unbound type variable "
                                           ++ show tv ++ " " ++ msg]
                   Just  _ -> return ()

tcContext :: Context TypeAST -> Tc ()
tcContext ctx = do
  sanityCheck (Map.null $ localTypeBindings ctx)
        "Expected to start typechecking with an empty lexical type environment"
  sanityCheck (null $ contextTypeBindings ctx)
        "Expected to start typechecking with an empty lexical type environment"
  --
  -- For now, we disallow mutually recursive data types
  let checkDataType (nm,dts) = do {
    case dts of
      [dt] -> do
         sanityCheck (nm == dataTypeName dt) ("Data type name mismatch for " ++ nm)
         let tyformals = dataTypeTyFormals dt
         let extctx = extendTyCtx ctx (map convertTyFormal tyformals)
         case detectDuplicates (map dataCtorName (dataTypeCtors dt)) of
           []   -> mapM_ (tcDataCtor nm extctx) (dataTypeCtors dt)
           dups -> tcFails [out $ "Duplicate constructor names " ++ show dups
                                ++ " in definition of data type " ++ nm]
      _ -> tcFails [out $ "Data type name " ++ nm
                       ++ " didn't map to a single data type!"]
  }
  mapM_ checkDataType (Map.toList $ contextDataTypes ctx)

tcDataCtor dtname ctx dc = do
  let msg = "in field of data constructor " ++ T.unpack (dataCtorName dc)
        ++ " of type " ++ dtname
  mapM_ (tcTypeWellFormed msg ctx) (dataCtorTypes dc)
-- }}}

-- {{{ Miscellaneous helpers.
collectUnboundUnificationVars :: [TypeAST] -> Tc [MetaTyVar TypeAST]
collectUnboundUnificationVars xs = mapM zonkType xs >>= (return . collectAllUnificationVars)

collectAllUnificationVars :: [TypeAST] -> [MetaTyVar TypeAST]
collectAllUnificationVars xs = Set.toList (Set.fromList (concatMap go xs))
  where go x =
          case x of
            PrimIntAST _          -> []
            PrimFloat64AST        -> []
            TyConAppAST _nm types -> concatMap go types
            TupleTypeAST types    -> concatMap go types
            FnTypeAST ss r _ _    -> concatMap go (r:ss)
            CoroTypeAST s r       -> concatMap go [s,r]
            ForAllAST _tvs rho    -> go rho
            TyVarAST  _tv         -> []
            MetaTyVar     m       -> [m]
            RefTypeAST    ty      -> go ty
            ArrayTypeAST  ty      -> go ty

instance Ord (MetaTyVar TypeAST) where
  compare m1 m2 = compare (mtvUniq m1) (mtvUniq m2)

vname (E_AnnVar _rng av) n = show n ++ " for " ++ T.unpack (identPrefix $ tidIdent av)
vname _                  n = show n

varbind id ty = TermVarBinding (identPrefix id) (TypedId ty id)

genTauUnificationVarsLike :: [a] -> (Int -> String) -> Tc [TypeAST]
genTauUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVarTau (namegen n) | (_, n) <- zip spine [1..]]

  {-
genSigmaUnificationVarsLike :: [a] -> (Int -> String) -> Tc [TypeAST]
genSigmaUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVarSigma (namegen n) | (_, n) <- zip spine [1..]]
-}


verifyNonOverlappingBindings :: SourceRange -> String -> [ContextBinding ty] -> Tc ()
verifyNonOverlappingBindings rng name binders = do
    case detectDuplicates [name | (TermVarBinding name _) <- binders] of
        []   -> return ()
        dups -> tcFails [out $ "Error when checking " ++ name ++ ": "
                              ++ "had duplicated bindings: " ++ show dups
                              ++ highlightFirstLine rng]

bindingForVar v = TermVarBinding (identPrefix $ tidIdent v) v

tyvarsOf ktyvars = map (\(tv,_k) -> tv) ktyvars

isRho (ForAllAST _ _) = False
isRho _               = True

instance Show a => Show (Expected a) where
  show (Infer _) = "<infer>"
  show (Check a) = show a

retypeTID :: (t1 -> Tc t2) -> TypedId t1 -> Tc (TypedId t2)
retypeTID f (TypedId t1 id) = f t1 >>= \t2 -> return (TypedId t2 id)

eqLen a b = List.length a == List.length b

getEnvTypes ctx = return (map tidType $ Map.elems (contextBindings ctx))

expMaybe (Infer _) = Nothing
expMaybe (Check t) = Just t

update r e_action = do e <- e_action
                       tcLift $ writeIORef r (typeAST e)
                       return e

type Term = ExprAST TypeAST

-- In contrast to meta type variables, the IORef for inferred types
-- can contain a sigma, not just a tau.
data Expected t = Infer (IORef t) | Check t

tcVERBOSE = True

debug s = do when tcVERBOSE (tcLift $ putStrLn s)

typeAST :: AnnExpr TypeAST -> TypeAST
typeAST = typeOf
-- }}}
