-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.Typecheck(tcSigmaToplevel) where

import qualified Data.List as List(length, zip)
import Data.List(foldl', (\\))
import Control.Monad(liftM, forM_, forM, liftM, liftM2, when)

import qualified Data.Text as T(Text, unpack)
import qualified Data.Map as Map(lookup, insert, elems, toList)
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
--   * Polymorphic types are further (conceptually) divided into
--     those which may begin with a forall (sigma types), and those
--     which never have a forall as the topmost type constructor (rho types).
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
--     We instead use (Maybe TypeAST) as the signature, to determine whether
--     the algorithm should run in inference or checking mode.
--     Checking mode is strictly more powerful, at the cost of increased
--     programmer annotation burden.
--       (TODO: document how and where the algorithm switches between
--              checking and inference modes for some simple examples)
--   * See the rule for typechecking boolean constants for an example of
--     how the expected type can be used to improve error messages.
--   * Unlike the language from the paper, we allow programmers to explicitly
--     instantiate polymorphic types. This provides a nice way of supporting
--     impredicative instantiation and polymorphic recursion.
--
--   * There are two core helper functions for driving type inference:
--     `unify` and `subsumedBy`.
--     `unify` takes two *tau* types, and unifies them by side effect.
--       They are taus because unify proceeds recursively, so there's no
--       effective difference between a rho and a sigma.
--     `subsumedBy` takes a type-checked expression annotated with a sigma type,
--     and another sigma type, and verifies (via `unify`, after appropriate
--     type-massaging) that the expression can be viewed as having the provided
--     sigma type.
--
--   * To force an expression to be typechecked in pure inference mode,
--     try the following construct: case INFER of _ -> ... end.
--   * To force an expression to be checked against a meta type variable,
--     the easiest approach is to use a reference store operation: METATY >^ r.
-----------------------------------------------------------------------

type Term = ExprAST TypeAST

-- In contrast to meta type variables, the IORef for inferred types
-- can contain a sigma, not just a tau.
data Expected t = Infer (IORef t) | Check t

tcSigmaToplevel (TermVarBinding txt tid) ctx ast = do
        -- TODO need to push this into the typechecking algorithm
        -- so it is applied before codifying the result in an expression.
        --zonkType ty
        -- We don't use checkSigma because we don't want the check
        -- for escaping type variables.
        e <- inferSigma ctx ast "toplevel"

        (_skol_tvs, rho) <- skolemize (tidType tid)
        debug $ "tcSigmaToplevel deferring to subsCheckRho"
        debug $ "tcSigmaToplevel " ++ show tid
        debug $ "tcSigmaTopLevel " ++ "    =skol=> "
        tcLift $ runOutput $ showStructure rho
        debug $ "tcSigmaTopLevel " ++ show txt ++ " :: " ++ show (typeAST e)
        _ <- subsCheckRho e rho

        return e

debug s = do when tcVERBOSE (tcLift $ putStrLn s)

getEnvTypes ctx = return (map tidType $ Map.elems (contextBindings ctx))

inferSigma :: Context TypeAST -> Term -> String -> Tc (AnnExpr Sigma)
-- Special-case variables and function literals
-- to avoid a redundant instantation + generalization
inferSigma ctx (E_VarAST rng v) _msg = tcSigmaVar ctx rng (evarName v)
inferSigma ctx (E_FnAST f)       msg = do r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                                          tcSigmaFn  ctx f (Infer r)
inferSigma ctx (E_CallAST   rng base argtup) msg = do
                r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                tcSigmaCall     ctx rng   base argtup (Infer r)
inferSigma ctx e msg
   = do {
        ; debug $ "inferSigma " ++ highlightFirstLine (rangeOf e)
        ; debug $ "inferSigma deferring to inferRho"
        ; e' <- inferRho ctx e msg
        ; debug $ "inferSigma inferred :: " ++ show (typeAST e')
        ; env_tys <- getEnvTypes ctx
        ; env_tvs <- collectUnboundUnificationVars env_tys
        ; res_tvs <- collectUnboundUnificationVars [typeAST e']
        ; let forall_tvs = res_tvs \\ env_tvs
        ; case forall_tvs of
            [] -> return ()
            _ -> tcFails [out $ "inferSigma ought to quantify over the escaping meta type variables " ++ show (map MetaTyVar forall_tvs)]
        ; return e'
        }
        {-
        ; ty <- quantify forall_tvs
        ; debug $ "inferSigma quantifying over " ++ show (map MetaTv forall_tvs) ++ " to get " ++ show ty
	; return ty
        -}

checkSigma :: Context TypeAST -> Term -> Sigma -> Tc (AnnExpr Sigma)
checkSigma ctx e sigma = do
       { (skol_tvs, rho) <- skolemize sigma
       ; debug $ "checkSigma " ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show sigma
       ; debug $ "checkSigma used " ++ show skol_tvs ++ " to skolemize " ++ show sigma ++ " to " ++ show rho
       ; debug $ "checkSigma deferring to checkRho"
       ; ann <- checkRho ctx e rho
       ; env_tys <- getEnvTypes ctx
       ; esc_tvs <- getFreeTyVars (sigma : env_tys)
       ; debug $ "checkSigma escaping types were " ++ show esc_tvs
       ; let bad_tvs = filter (`elem` esc_tvs) skol_tvs
       ; sanityCheck (null bad_tvs)
                     ("Type not polymorphic enough")
       ; return ann
       }

checkRho :: Context Sigma -> Term -> Rho -> Tc (AnnExpr Rho)
-- Invariant: the Rho is always in weak-prenex form
checkRho ctx e ty = do
   debug $ "checkRho " ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show ty
   debug $ "checkRho deferring to tcRho"
   tcRho ctx e (Check ty)

inferRho :: Context Sigma -> Term -> String -> Tc (AnnExpr Rho)
inferRho ctx e msg
  = do { ref <- newTcRef (error $ "inferRho: empty result: " ++ msg)
       ; debug $ "inferRho " ++ highlightFirstLine (rangeOf e)
       ; debug $ "inferRho deferring to tcRho"
       ; a <- tcRho ctx e (Infer ref)
       ; a <- inst a
       ; debug $ "tcRho (" ++ msg ++") finished, reading inferred type from ref"
       ; debug $ "tcRho (" ++ msg ++"): " ++ highlightFirstLine (rangeOf e)
       ; ty <- tcLift $ readIORef ref
       ; debug $ "inferRho (" ++ msg ++")" ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show ty
       ; debug $ "inferRho (" ++ msg ++")" ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show (typeAST a)
       ; sanityCheck (isRho $ typeAST a) ("inferRho wound up with a sigma type!" ++ highlightFirstLine (rangeOf a))
       ; return a
       }

tcVERBOSE = True

expMaybe (Infer _) = Nothing
expMaybe (Check t) = Just t

update r e_action = do e <- e_action
                       tcLift $ writeIORef r (typeAST e)
                       return e

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
      -- a[b]
      E_ArrayRead rng (ArrayIndex a b _ s) -> do
              ta <- inferRho ctx a "array read base"
              tb <- inferRho ctx b "array read index"
              tcRhoArrayRead rng s ta tb expTy
      -- a >^ b[c]
      E_ArrayPoke rng (ArrayIndex b c _ s) a -> do
              ta <- inferRho ctx a "array poke val"
              tb <- checkRho ctx b (ArrayTypeAST (typeAST ta))
              tc <- inferRho ctx c "array poke idx"
              tcRhoArrayPoke rng s ta tb tc expTy
      E_CompilesAST rng Nothing ->
          matchExp expTy (AnnCompiles rng (CompilesResult $ Errors
                                        [out $ "parse error"])) "compiles-error"
      E_CompilesAST rng (Just e) -> do
          -- Note: we infer a sigma, not a rho, because we don't want to
          -- instantiate a sigma with meta vars and then never bind them.
          outputOrE <- tcIntrospect (inferSigma ctx e "compiles")
          matchExp expTy (AnnCompiles rng (CompilesResult outputOrE)) "compiles"


-- First, an interesting pair of rules for variables:
--
--
--  G contains v ::: s             G has v as primitive
--  ------------------     or      -----------------------
--  G |- v ~~> v ::: s             G |- v ~~> prim v ::: s
tcSigmaVar ctx rng name = do
  tcLift $ runOutput $ outCS Green "typecheckVar (sigma): " ++ out (T.unpack name ++ "...")
  debug ""

  -- Resolve the given name as either a variable or a primitive reference.
  case termVarLookup name (contextBindings ctx) of
    Just (TypedId sigma id) -> do
         return $ E_AnnVar rng (TypedId sigma id)
    Nothing   ->
      case termVarLookup name (primitiveBindings ctx) of
        Just avar -> return $ AnnPrimitive rng avar
        Nothing   -> do msg <- getStructureContextMessage
                        tcFails [out $ "Unknown variable " ++ T.unpack name
                                 ++ showSourceRange rng
                                 ++ "ctx: "++ unlines (map show (Map.toList $ contextBindings ctx))
                                 ++ "\nhist: " , msg]


matchExp expTy ann msg =
     case expTy of
         Check s@(ForAllAST {}) -> do
                       subsCheck ann s msg
         Check t -> do debug $ "matchExp[Check]("++msg++") deferring to subsCheckRho"
                       subsCheckRho ann t
         Infer r -> do update r (return ann)

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
     ann_var <- inst v_sigma
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
         (Infer r)                   -> update r (return ab)
         Check  (PrimIntAST I1)      -> return ab
         Check  m@MetaTyVar {}       -> do unify m (PrimIntAST I1) (Just $ "bool literal")
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
         (Infer r)                      -> update r (return ab)
         Check  (TyConAppAST "Text" []) -> return ab
         Check  m@MetaTyVar {} -> do unify m (TyConAppAST "Text" []) (Just $ "text literal")
                                     return ab
         Check  t -> tcFails [out $ "Unable to check Text constant in context"
                                ++ " expecting non-Text type " ++ show t
                                ++ showSourceRange rng]
-- }}}


--  G |- e1 ::: ()
--  G |- e2 ::: t2
--  -------------------
--  G |- e1 ; e2 ::: t2
-- {{{
tcRhoSeq ctx rng a b expTy = do
    ea <- inferRho ctx a "seq" --(Check $ TupleTypeAST [])
    id <- tcFresh ".seq"
    eb <- tcRho ctx b expTy
    debug $ "seq; exp ty = " ++ show expTy ++ "; t2 = " ++ show (typeAST eb)
    matchExp expTy (AnnLetVar rng id ea eb) "seq"
-- }}}


--  G |- e1 ::: tau
--  G |- e2 ::: Ref tau
--  --------------------
--  G |- e1 >^ e2 ::: ()
tcRhoStore ctx rng e1 e2 expTy = do
-- {{{
    u_slot <- newTcUnificationVarTau $ "slot_type"
    u_expr <- newTcUnificationVarTau $ "expr_type"
    a2 <- tcRho ctx e2 (Check $ RefTypeAST u_slot)
    a1 <- tcRho ctx e1 (Check $            u_expr)
    unify           u_slot                    u_expr    (Just "Store expression")
    unify        (typeAST a2) (RefTypeAST (typeAST a1)) (Just "Store expression")
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
    let t1 = typeAST a1
    case t1 of
      RefTypeAST {} -> return ()
      MetaTyVar  {} -> return ()
      other -> tcFails [out $ "Expected deref-ed expr "
                           ++ "to have ref type, had " ++ show other ++ highlightFirstLine rng]
    unify t1 (RefTypeAST tau) (Just $ "Deref expression: " ++ highlightFirstLine rng
                                   ++ " was expected to have type " ++ show (RefTypeAST tau)
                                   ++ " but actually had type " ++ show t1)
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
  case expTy of
     Infer r                 -> update r (tcTuple ctx rng exprs [Nothing | _ <- exprs])
     Check (TupleTypeAST ts) ->           tcTuple ctx rng exprs [Just t  | t <- ts]
     Check m@MetaTyVar {}    -> do
        tctup <-                          tcTuple ctx rng exprs [Nothing | _ <- exprs]
        unify m (typeAST tctup) (Just $ highlightFirstLine rng)
        return tctup
     Check ty -> tcFails [out $ "typecheck: tuple (" ++ show exprs ++ ") "
                             ++ "cannot check against non-tuple type " ++ show ty]
  where
    tcTuple ctx rng exps typs = do
        exprs <- typecheckExprsTogether ctx exps typs
        return $ AnnTuple (E_AnnTuple rng exprs)

    -- Typechecks each expression in the same context
    typecheckExprsTogether ctx exprs expectedTypes = do
        sanityCheck (length exprs == length expectedTypes)
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
        unify (PrimIntAST I32) (typeAST aiexpr) (Just "arrayread idx type")
        unify (ArrayTypeAST t) (typeAST base) (Just "arrayread type")
        let expr = AnnArrayRead rng t (ArrayIndex base aiexpr rng s)
        case expTy of
          Infer r -> do update r (return expr)
          Check c -> do unify t c (Just $ "arrayread expected type: " ++ show c)
                        return expr

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
      unify t (typeAST v) (Just "arraypoke type")
      let expr = AnnArrayPoke rng t (ArrayIndex b i rng s) v
      case expTy of
        Infer r -> do update r (return expr)
        Check c -> do unify t c (Just $ "arraypoke expected type: " ++ show c)
                      return expr
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

    unify (typeAST ea) fosBoolType  (Just "IfAST: type of conditional wasn't boolean")
    unify (typeAST eb) (typeAST ec) (Just "IfAST: types of branches didn't match")

    return (AnnIf rng (typeAST eb) ea eb ec)
    --TODO
    --ea' <- subsumedBy ea fosBoolType  (Just "IfAST: type of conditional wasn't boolean")
    --eb' <- subsumedBy eb (typeAST ec) (Just "IfAST: types of branches didn't match")
    --ec' <- subsumedBy ec (typeAST eb) (Just "IfAST: types of branches didn't match")
    --return (AnnIf rng (typeAST eb') ea' eb' ec')
-- }}}

--  G |- cond ::: Bool
--  G |- body ::: t2
--  ------------------------------------
--  G |- until cond then body end ::: ()
-- {{{
tcRhoUntil ctx rng cond body expTy = do
      acond <- tcRho ctx cond (Check fosBoolType)
      abody <- inferRho ctx body "until"
      unify (typeAST acond) fosBoolType
            (Just "E_Until: type of until conditional wasn't boolean")
      matchExp expTy (AnnUntil rng (TupleTypeAST []) acond abody) "until"
-- }}}


--  G         |- e1 ::: t1
--  G{x:::t1} |- e2 ::: t2
--  ----------------------------
--  G |- let x = e1 in e2 ::: t2
tcRhoLet ctx0 rng (TermBinding v e1) e2 mt = do
-- {{{
    sanityCheck (notRecursive boundName e1) errMsg
    id     <- tcFreshT boundName
    a1 <- case maybeVarType of
                 Nothing -> inferSigma ctx0 e1 "let"
                 Just  t -> checkSigma ctx0 e1 t
    let v   = TypedId (typeAST a1) id
    let ctx = prependContextBindings ctx0 [bindingForVar v]
    a2     <- tcRho ctx  e2 mt
    return (AnnLetVar rng id a1 a2)
  where
    boundName    = evarName v
    maybeVarType = evarMaybeType v
    notRecursive boundName expr =
            not (boundName `elem` freeVars expr && isFnAST expr)
                  where   isFnAST (E_FnAST _) = True
                          isFnAST _           = False
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
           unify u (typeAST b')
                       (Just $ "recursive binding " ++ T.unpack (evarName v))
           return b'
       )

    -- Typecheck the body as well
    e' <- tcRho ctx e mt

    let fns = [f | (E_AnnFn f) <- tcbodies]
    let nonfns = filter notAnnFn tcbodies
    sanityCheck (null nonfns) "Recursive bindings should only contain functions!"
    return $ AnnLetFuns rng ids fns e'
-- }}}

notAnnFn (E_AnnFn _) = False
notAnnFn _           = True

-- G |- e ::: forall a1::k1..an::kn, rho
-- G |- t_n <::: k_n                          (checked later)
-- ------------------------------------------
-- G |- e :[ t1..tn ]  ::: rho{t1..tn/a1..an}
tcRhoTyApp ctx rng e t1tn expTy = do
-- {{{
    debug $ "ty app: inferring sigma type for base..."
    aeSigma <- inferSigma ctx e "tyapp"
    debug $ "ty app: base has type " ++ show (typeAST aeSigma)
    tbase <- return (typeAST aeSigma)
    --tbase <- shallowZonk (typeAST aeSigma)
    case (t1tn, tbase) of
      ([]  , _           ) -> return aeSigma
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
tcRhoCall :: Context Sigma -> SourceRange
              -> ExprAST TypeAST -> (TupleAST TypeAST)
              -> Expected TypeAST -> Tc (AnnExpr Rho)
tcRhoCall ctx rng base argstup exp_ty = do
   -- TODO think harder about when it's safe to push exp_ty down
   debug $ "tcRhoCall " ++ show exp_ty
   r <- newTcRef (error $ "tcRho>SigmaCall: empty result: ")
   app <- tcSigmaCall ctx rng base argstup (Infer r)
   instSigma app exp_ty

tcSigmaCall ctx rng base argstup exp_ty = do
        annbase <- inferRho ctx base "called base"
        let fun_ty = typeAST annbase
        let argexprs = tupleAstExprs argstup
        debug $ "call: fn type is " ++ show fun_ty
        (args_ty, res_ty) <- unifyFun fun_ty argexprs
        debug $ "call: fn args ty is " ++ show args_ty
        debug $ "call: arg exprs are " ++ show argexprs
        sanityCheck (eqLen argexprs args_ty) "tcSigmaCall expected equal # of arguments!"
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

unifyFun :: Rho -> [a] -> Tc ([Sigma], Rho)
unifyFun (FnTypeAST args res _cc _cs) _args = return (args, res)
unifyFun (ForAllAST {}) _ = tcFails [out $ "invariant violated: sigma passed to unifyFun!"]
unifyFun tau args = do
        arg_tys <- mapM (\_ -> newTcUnificationVarTau "fn args ty") args
        res_ty <- newTcUnificationVarTau "fn res  ty"
        unify tau (FnTypeAST arg_tys res_ty FastCC FT_Func) (Just "unifyFun")
        return (arg_tys, res_ty)

-- G{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { x1 : t1 => ... => xn : tn => e } ::: { t1 => ... => tn => tb }
--
-- {{{
tcRhoFn ctx f expTy = do
  sigma <- tcSigmaFn ctx f expTy
  debug $ "tcRhoFn instantiating " ++ show (typeAST sigma)
  inst sigma
-- }}}

-- G{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { x1 : t1 => ... => xn : tn => e } ::: { t1 => ... => tn => tb }
--
-- or
--
-- G{a1:k1}...{an:kn}{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { forall a1:k1, ..., an:kn, x1 : t1 => ... => xn : tn => e } :::
--        forall a1:k1, ..., an:kn,    { t1 => ... =>      tn => tb }
-- {{{
tcSigmaFn ctx f expTy = do
  case (fnTyFormals f, expTy) of
    ([], Check fnty) -> helper (Just fnty) Nothing
    ([], Infer r   ) -> helper Nothing     (Just r)
    (tyformals, Infer r) -> do
        let rng = fnAstRange f
        let ktvs = map convertTyFormal tyformals
        taus <- genTauUnificationVarsLike ktvs (\n -> "fn type parameter " ++ show n ++ " for " ++ T.unpack (fnAstName f))
        -- Extend the type environment with the forall-bound variables.
        let extTyCtx =
             let tybindmap = localTypeBindings ctx in
             ctx { localTypeBindings = foldl' ins tybindmap (zip taus ktvs) }
               where ins m (mtv, (BoundTyVar nm, _k)) = Map.insert nm mtv m
                     ins _ (_ ,  (SkolemTyVar {}, _))= error "ForAll bound a skolem!"

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
        annbody <- case Nothing of
          Nothing   -> do inferSigma extCtx (fnAstBody f) "poly-fn body"
          Just _fnty -> do tcFails [out $ "TODO: check polymorphic types"]
          {-
                          (arg_ty, body_ty) <- unifyFun fnty
                          let vars_ty = map tidType uniquelyNamedFormals
                          subsCheck arg_ty (TupleTypeAST vars_ty)
                          checkRho ctx (fnAstBody f) body_ty
        -}
        debug $ "inferred raw type of body of polymorphic function: " ++ show (typeAST annbody)

        -- Note we collect free vars in the old context, since we can't possibly
        -- capture the function's arguments from the environment!
        freeVars <- computeFreeFnVars uniquelyNamedFormals annbody rng ctx

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
                       (MetaTyVar m) -> writeTcMeta m (TyVarAST tv)
                       y -> tcFails [out $ "expected ty param metavar to be un-unified, instead had " ++ show y]
                  ) (zip taus ktvs)
        -- Zonk the type to ensure that the meta vars are completely gone.
        debug $ "inferred raw type of body of polymorphic function: " ++ show fnty0
        debug $ "zonking; tyvars were " ++ show (zip taus ktvs)
        fnty <- zonkType fnty0
        debug $ "inferred overall type of body of polymorphic function: " ++ show fnty
        let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol $ fnAstName f))
                               uniquelyNamedFormals annbody freeVars rng

        -- Update the Infer ref, if we were given one, and return the fn.
        case (Just r) of
          Nothing -> return fn
          Just r -> update r (return fn)

    (_tyformals, _) -> do
        tcFails [out $ "tcRhoPolyFn :?: " ++ show expTy]
  where
    helper mb_exp_fnty mb_infer_ref = do
        let rng = fnAstRange f
        -- While we're munging, we'll also make sure the names are all distinct.
        uniquelyNamedFormals <- getUniquelyNamedFormals rng (fnFormals f) (fnAstName f)

        -- Extend the variable environment with the function arg's types.
        let extCtx = extendContext ctx uniquelyNamedFormals
        -- Check or infer the type of the body.
        annbody <- case mb_exp_fnty of
          Nothing   -> do inferSigma extCtx (fnAstBody f) "mono-fn body"
          Just fnty -> do let var_tys = map tidType uniquelyNamedFormals
                          (arg_tys, body_ty) <- unifyFun fnty var_tys
                          _ <- sequence [subsCheckTy argty varty "mono-fn-arg" |
                                          (argty, varty) <- zip arg_tys var_tys]
                          -- TODO is there an arg translation?
                          checkRho extCtx (fnAstBody f) body_ty

        -- Note we collect free vars in the old context, since we can't possibly
        -- capture the function's arguments from the environment!
        freeVars <- computeFreeFnVars uniquelyNamedFormals annbody rng ctx

        let fnty = fnTypeTemplate f argtys (typeAST annbody) FastCC
                    where argtys = map tidType uniquelyNamedFormals

        let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol $ fnAstName f))
                               uniquelyNamedFormals annbody freeVars rng

        -- Update the Infer ref, if we were given one, and return the fn.
        case mb_infer_ref of
          Nothing -> return fn
          Just r -> update r (return fn)
-- }}}

extendContext :: Context Sigma -> [AnnVar] -> Context Sigma
extendContext ctx protoFormals =
                 prependContextBindings ctx (map bindingForVar protoFormals)

fnTypeTemplate f argtypes retty cc =
  -- Compute "base" function type, ignoring any type parameters.
  let procOrFunc = if fnWasToplevel f then FT_Proc else FT_Func in
  FnTypeAST argtypes retty cc procOrFunc

computeFreeFnVars uniquelyNamedFormals annbody rng ctx = do
    let identsFree = bodyvars `butnot` (boundvars ++ globalvars)
                     where
                     bodyvars   = freeIdents annbody
                     boundvars  = map tidIdent uniquelyNamedFormals
                     globalvars = concatMap tmBindingId (globalBindings ctx)
                     tmBindingId (TermVarBinding _ tid) = [tidIdent tid]
    freeAnns <- mapM (\id -> tcSigmaVar ctx rng (identPrefix id))
                     identsFree
    return $ [tid | E_AnnVar _ tid <- freeAnns]

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


-- {{{ case scrutinee of branches end
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
      unify u (typeAST abody)
                   (Just $ "Failed to unify all branches of case " ++ show rng)
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

        unify ty ctxTy (Just $ "checkPattern:P_Ctor " ++ show cid)
        return $ P_Ctor r ty ps info

      EP_Tuple     r eps  -> do
        ts <- case ctxTy of
                TupleTypeAST ts -> return ts
                _ -> do ts <- sequence [newTcUnificationVarTau "tup" | _ <- eps]
                        unify ctxTy (TupleTypeAST ts) (Just "tuple-pattern")
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

-- {{{
subsCheckTy :: Sigma -> Sigma -> String -> Tc ()
subsCheckTy sigma1 sigma2@(ForAllAST {}) msg = do
  (skols, rho) <- skolemize sigma2
  debug $ "subsCheckTy deferring to subsCheckRhoTy"
  subsCheckRhoTy sigma1 rho
  esc_tvs <- getFreeTyVars [sigma1, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skols
  --sanityCheck (null bad_tvs) ("subsCheck(" ++ msg ++ "): Type\n" ++ show sigma1 ++
  --                     " not as polymorphic as\n" ++ show sigma2 ++
  --                     "\nbad type variables: " ++ show bad_tvs)
  return ()

subsCheckTy sigma1 rho2 _msg = subsCheckRhoTy sigma1 rho2

subsCheckRhoTy :: Sigma -> Rho -> Tc ()
subsCheckRhoTy (ForAllAST ktvs rho) rho2 = do -- Rule SPEC
             taus <- genTauUnificationVarsLike ktvs (\n -> "instSigma type parameter " ++ show n)
             rho1 <- instSigmaWith ktvs rho taus
             subsCheckRhoTy rho1 rho2
subsCheckRhoTy rho1 (FnTypeAST as2 r2 _ _) = unifyFun rho1 as2 >>= \(as1, r1) -> subsCheckFunTy as1 r1 as2 r2
subsCheckRhoTy (FnTypeAST as1 r1 _ _) rho2 = unifyFun rho2 as1 >>= \(as2, r2) -> subsCheckFunTy as1 r1 as2 r2
subsCheckRhoTy tau1 tau2 -- Rule MONO
     = unify tau1 tau2 (Just "subsCheckRho") -- Revert to ordinary unification
-- }}}

-- {{{
subsCheck :: (AnnExpr Sigma) -> Sigma -> String -> Tc (AnnExpr Sigma)
subsCheck esigma sigma2@(ForAllAST {}) msg = do
  (skols, rho) <- skolemize sigma2
  debug $ "subsCheck deferring to subsCheckRho"
  _ <- subsCheckRho esigma rho
  esc_tvs <- getFreeTyVars [typeAST esigma, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skols
  --sanityCheck (null bad_tvs) ("subsCheck(" ++ msg ++ "): Type\n" ++ show sigma1 ++
  --                     " not as polymorphic as\n" ++ show sigma2 ++
  --                     "\nbad type variables: " ++ show bad_tvs)
  return esigma

subsCheck esigma rho2 _msg = subsCheckRho esigma rho2

subsCheckRho :: AnnExpr Sigma -> Rho -> Tc (AnnExpr Rho)
subsCheckRho esigma rho2 = do
  case (typeAST esigma, rho2) of
    (_, ForAllAST {}) -> do tcFails [out $ "violated invariant: sigma passed to subsCheckRho"]
    (ForAllAST {}, _) -> do -- Rule SPEC
        debug $ "subsCheckRho instantiating " ++ show (typeAST esigma)
        erho <- inst esigma
        subsCheckRho erho rho2
        {-
        taus <- genTauUnificationVarsLike ktvs (\n -> "instSigma type parameter " ++ show n)
        rho1 <- instSigmaWith ktvs rho taus
        subsCheckRho rho1 rho2
        -}

        {-
    (rho1, TupleTypeAST {})     -> do tcFails [out $ "subsCheckRho tuple 1"]
                                      (ts1, ts2) <- unifyTuple rho1 rho2
                                      mapM_ (\(t1, t2) -> subsCheckRhoTy t1 t2) (zip ts1 ts2)
                                      return esigma
    (rho1@(TupleTypeAST {}), _) -> do tcFails [out $ "subsCheckRho tuple 2"]
                                      (ts1, ts2) <- unifyTuple rho1 rho2
                                      mapM_ (\(t1, t2) -> subsCheckRhoTy t1 t2) (zip ts1 ts2)
                                      return esigma
                                      -}
    (rho1, FnTypeAST as2 r2 _ _) -> do debug $ "subsCheckRho fn 1"
                                       (as1, r1) <- unifyFun rho1 as2
                                       subsCheckFunTy as1 r1 as2 r2
                                       return esigma
    (FnTypeAST as1 r1 _ _, _)    -> do debug "subsCheckRho fn 2"
                                       (as2, r2) <- unifyFun rho2 as1
                                       subsCheckFunTy as1 r1 as2 r2
                                       return esigma
    -- Elide the two FUN rules and subsCheckFun because we're using
    -- shallow, not deep, skolemization due to being a strict language.

    (rho1, _) -> do -- Rule MONO
        unify rho1 rho2 (Just "subsCheckRho") -- Revert to ordinary unification
        return esigma
-- }}}

-- {{{ Helper functions for subsCheckRho to peek inside type constructors
unifyTuple rho1 (TupleTypeAST ts2) = do
  metas <- mapM (\_ -> newTcUnificationVarTau "utup") ts2
  unify rho1 (TupleTypeAST metas) (Just "unifyTuple1")
  unify rho1 (TupleTypeAST ts2)   (Just "unifyTuple2")
  return (metas, ts2)

unifyTuple (TupleTypeAST ts1) rho2 = do
  metas <- mapM (\_ -> newTcUnificationVarTau "utup") ts1
  unify (TupleTypeAST metas) rho2 (Just "unifyTuple3")
  unify (TupleTypeAST ts1)   rho2 (Just "unifyTuple4")
  return (ts1, metas)

unifyTuple _ _ = tcFails [out $ "violated invariant: unifyTuple called with no tuple arguments"]

subsCheckFunTy as1 r1 as2 r2 = do
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
instSigma e1 (Infer r)  = do { e <- inst e1
                             ; debug $ "instSigma " ++ show (typeAST e1) ++ " -inst-> " ++ show (typeAST e)
                             ; tcLift $ writeIORef r (typeAST e)
                             ; return e }
{-
instantiate :: Sigma -> Tc Rho
-- Instantiate the topmost for-alls of the argument type
-- with flexible type variables
instantiate (ForAllAST ktvs rho) = do
     mtvs <- genTauUnificationVarsLike ktvs (\n -> "itype parameter " ++ show n)
     instSigmaWith ktvs rho mtvs
instantiate ty = return ty
-}

inst :: AnnExpr Sigma -> Tc (AnnExpr Rho)
-- Transform a Sigma type into a Rho type by instantiating the ForAll's
-- type parameters with unification variables.
-- {{{
inst base = do
  --zonked <- shallowZonk (typeAST base)
  zonked <- return (typeAST base)
  case zonked of
     ForAllAST ktvs _rho -> do
       taus <- genTauUnificationVarsLike ktvs (\n -> "inst type parameter " ++ vname base n)
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
    PrimFloat64                    -> return x
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
        PrimFloat64           -> []
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
                          debug $ "zonking MTV: " ++ show mty
                          case mty of
                            Nothing -> return x
                            Just ty -> do ty' <- zonkType ty
                                          writeTcMeta m ty'
                                          return ty'
        PrimIntAST     {}     -> return x
        PrimFloat64           -> return x
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
-- }}}

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


-- If unification fails, the provided error message (if any)
-- is printed along with the unification failure error message.
-- If unification succeeds, each unification variable in the two
-- types is updated according to the unification solution.
unify :: TypeAST -> TypeAST -> Maybe String -> Tc ()
unify t1 t2 msg = do
  let msg' = case msg of Nothing -> "(<no msg>)" ; Just m -> " (" ++ m ++ ")"
  when tcVERBOSE $ do
    tcLift $ runOutput $ outCS Green $ "unify " ++ show t1 ++ " ?==? " ++ show t2 ++ msg'
    tcLift $ putStrLn ""
  tcOnError (liftM out msg) (tcUnifyTypes t1 t2) $ \(Just soln) -> do
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


collectUnboundUnificationVars :: [TypeAST] -> Tc [MetaTyVar TypeAST]
collectUnboundUnificationVars xs = mapM zonkType xs >>= (return . collectAllUnificationVars)

collectAllUnificationVars :: [TypeAST] -> [MetaTyVar TypeAST]
collectAllUnificationVars xs = Set.toList (Set.fromList (concatMap go xs))
  where go x =
          case x of
            PrimIntAST _          -> []
            PrimFloat64           -> []
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
