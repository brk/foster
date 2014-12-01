-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.Typecheck(tcSigmaToplevel, tcContext, tcType) where

import qualified Data.List as List(length, zip)
import Data.List(foldl', (\\))
import Control.Monad(liftM, forM_, forM, liftM, liftM2, when)

import qualified Data.Text as T(Text, pack, unpack)
import Data.Map(Map)
import qualified Data.Map as Map(lookup, insert, elems, toList, fromList, null)
import qualified Data.Set as Set(toList, fromList)
import Data.IORef(newIORef,readIORef,writeIORef)
import Data.UnionFind.IO(fresh)

import Foster.Base
import Foster.TypeAST
import Foster.TypeTC
import Foster.ExprAST
import Foster.AnnExpr
import Foster.Infer
import Foster.Context
import Foster.TypecheckInt(typecheckInt, typecheckRat)
import Foster.Output(OutputOr(Errors), putDocLn)
import Foster.PrettyAnnExpr()
import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace(trace)

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
--   * We opportunistically eta-contract calls to data constructors
--     so that, later on, compilation of letrec can directly see what data
--     constructor (& thus, what representation) it needs to pre-allocate.
--     OCaml avoids this by making constructors second-class;
--     SML   avoids this by disallowing constructors on the RHS of letrec.
--
--   * matchExp calls either subsCheck or subsCheckRho as appropriate.
--      subsCheck
--          skolemize
--          subsCheckRho
--      subsCheckRho
--          inst -> subsCheckRho
--
--          unifyFun -> subsCheckFunTy
--
--          unify
--
--      subsCheckRhoTy
--          unifyFun
--          subsCheckFunTy
--          unify
--      subsCheckFunTy
--          subsCheckTy
--      subsCheckTy
--          skolemize -> subsCheckRhoTy
--          subsCheckRhoTy
--      instSigma
--      inst
--      instWith
--      tryInstSigmaWith
--      instSigmaWith

-----------------------------------------------------------------------

tcSigmaToplevel :: ContextBinding TypeTC -> Context TypeTC -> Term -> Tc (AnnExpr SigmaTC)
tcSigmaToplevel (TermVarBinding _txt (tid, _)) ctx ast = do
-- {{{
    -- Make sure the (potentially user-supplied) type annotation is well-formed.
    {- TODO
    tcTypeWellFormed ("in the type declaration for " ++ T.unpack txt)
                     ctx (tidType tid)
                     -}

    debugDoc $ text "tcSigmaToplevel deferring to checkSigmaDirect with expected type"
            <$> (pretty (tidType tid)) <> line
    e <- checkSigmaDirect ctx ast (tidType tid)
    debugDoc $ text "tcSigmaToplevel returned expression with type " <> pretty (typeTC e)

    return e
-- }}}

inferSigma :: Context SigmaTC -> Term -> String -> Tc (AnnExpr SigmaTC)
-- {{{
-- Special-case variables and function literals
-- to avoid a redundant instantation + generalization
inferSigma ctx (E_VarAST rng v) _msg = tcSigmaVar ctx rng (evarName v)
inferSigma ctx (E_FnAST _rng f)  msg = do r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                                          tcSigmaFn  ctx f (Infer r)
inferSigma ctx (E_CallAST   rng base argtup) msg = do
                r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                tcSigmaCall     ctx rng   base argtup (Infer r)
inferSigma ctx e msg = do
    debug $ "inferSigma " ++ highlightFirstLine (rangeOf e)
    debug $ "inferSigma deferring to inferRho"
    e' <- inferRho ctx e msg
    doQuantificationCheck e' ctx
    return e'
-- }}}

checkSigma :: Context SigmaTC -> Term -> SigmaTC -> Tc (AnnExpr SigmaTC)
-- {{{
checkSigma ctx e sigma = do
    (skol_tvs, rho) <- skolemize sigma
    debug $ "checkSigma " ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show sigma
    debug $ "checkSigma used " ++ show skol_tvs ++ " to skolemize " ++ show sigma ++ " to " ++ show rho
    debug $ "checkSigma deferring to checkRho for: " ++ highlightFirstLine (rangeOf e)

    ann <- checkRho ctx e rho
    checkForEscapingTypeVariables e ann ctx sigma skol_tvs
    return ann
-- }}}

-- {{{
doQuantificationCheck :: AnnExpr SigmaTC -> Context SigmaTC -> Tc ()
doQuantificationCheck e' ctx = do
    debug $ "inferSigma inferred :: " ++ show (typeTC e')
    env_tys <- getEnvTypes ctx
    env_tvs <- collectUnboundUnificationVars env_tys
    res_tvs <- collectUnboundUnificationVars [typeTC e']
    let forall_tvs = res_tvs \\ env_tvs
    sanityCheck (null forall_tvs || not (isValue e' )) $
        "inferSigma ought to quantify over the escaping meta type variables " ++ show (map MetaTyVarTC forall_tvs)

isValue e = case e of
  AnnLiteral      {} -> True
  E_AnnFn         {} -> True
  AnnCompiles     {} -> True
  E_AnnTyApp _ _ a _ -> isValue a
  AnnAppCtor _ _ _ exprs -> all isValue exprs
  AnnTuple   _ _   exprs -> all isValue exprs
  _ -> False

checkForEscapingTypeVariables _ _    _   _     [] = return ()
checkForEscapingTypeVariables e _ann ctx sigma skol_tvs = do
    env_tys <- getEnvTypes ctx
    esc_tvs <- getFreeTyVars (sigma : env_tys)
    tcLift $ putStrLn $ "esc-chk: |env| = " ++ show (List.length env_tys)
                            ++ "\t|tvs| = " ++ show (List.length esc_tvs)
                            ++ "\t|skz| = " ++ show (List.length skol_tvs)

    let bad_tvs = filter (`elem` esc_tvs) skol_tvs
    debug $ "checkSigma escaping types from were " ++ show esc_tvs
         ++ "; bad tvs were " ++ show bad_tvs
         ++ highlightFirstLine (rangeOf e)
    sanityCheck (null bad_tvs)
                ("Type not polymorphic enough")
-- }}}


checkSigmaDirect :: Context SigmaTC -> Term -> SigmaTC -> Tc (AnnExpr SigmaTC)
-- {{{
checkSigmaDirect ctx (E_FnAST _rng fn) sigma@(ForAllTC {}) = do
    tcSigmaFn ctx fn (Check sigma)

checkSigmaDirect _ctx _ (ForAllTC {}) =
    tcFails [text $ "checkSigmaDirect: can't check a sigma type against an "
                ++ "arbitrary expression"]

checkSigmaDirect ctx e rho = checkRho ctx e rho
-- }}}

checkRho :: Context SigmaTC -> Term -> RhoTC -> Tc (AnnExpr RhoTC)
-- Invariant: the Rho is always in weak-prenex form
-- {{{
checkRho ctx e ty = do
    debug $ "checkRho " ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show ty
    debug $ "checkRho deferring to tcRho"
    tcRho ctx e (Check ty)
-- }}}

inferRho :: Context SigmaTC -> Term -> String -> Tc (AnnExpr RhoTC)
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
    debug $ "inferRho (" ++ msg ++")" ++ highlightFirstLine (rangeOf e) ++ " :: " ++ show (typeTC a)
    sanityCheck (isRho $ typeTC a) ("inferRho wound up with a sigma type!" ++ highlightFirstLine (rangeOf a))
    return a

-- }}}
mkFnTypeTC args ret = FnTypeTC args ret (UniConst FastCC) (UniConst FT_Func)

tcRho :: Context SigmaTC -> Term -> Expected RhoTC -> Tc (AnnExpr RhoTC)
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
tcRho ctx expr expTy = do
 debugDoc2 $ green (text "typecheck: ") <> textOf expr 0 <> text (" <=? " ++ show expTy)
 logged'' (show $ textOf expr 0 ) $
  tcWithScope expr $ do
    case expr of
      E_VarAST    rng v              -> tcRhoVar      ctx rng (evarName v)      expTy
      E_PrimAST   rng nm [] []       -> tcRhoPrim     ctx rng (T.pack  nm)      expTy
      E_PrimAST   rng "inline-asm" [LitText s, LitText c, LitBool x] [ty] -> do
        ty' <- tcType ctx ty
        matchExp expTy (AnnPrimitive rng ty' (PrimInlineAsm ty' s c x)) "inline-asm"
      E_IntAST    rng txt ->            typecheckInt rng txt expTy   >>= (\v -> matchExp expTy v "tcInt")
      E_RatAST    rng txt -> (typecheckRat rng txt (expMaybe expTy)) >>= (\v -> matchExp expTy v "tcRat")
      E_BoolAST   rng b              -> tcRhoBool         rng   b          expTy
      E_StringAST rng txtorbytes     -> tcRhoTextOrBytes  rng   txtorbytes expTy
      E_MachArrayLit rng mbt args    -> tcRhoArrayLit ctx rng   mbt args   expTy
      E_CallAST   rng base argtup    -> tcRhoCall     ctx rng   base argtup expTy
      E_TupleAST  rng exprs          -> tcRhoTuple    ctx rng   exprs      expTy
      E_IfAST   rng a b c            -> tcRhoIf       ctx rng   a b c      expTy
      E_FnAST  _rng f                -> tcRhoFn       ctx       f          expTy
      E_LetRec rng bindings e        -> tcRhoLetRec   ctx rng   bindings e expTy
      E_LetAST rng binding  e        -> tcRhoLet      ctx rng   binding  e expTy
      E_TyApp  rng e types           -> tcRhoTyApp    ctx rng   e types    expTy
      E_TyCheck rng e ty             -> tcRhoTyCheck  ctx rng   e ty       expTy
      E_Case   rng a branches        -> tcRhoCase     ctx rng   a branches expTy
      E_AllocAST rng a rgn           -> tcRhoAlloc    ctx rng   a rgn      expTy
      E_StoreAST rng e1 e2           -> tcRhoStore    ctx rng   e1 e2      expTy
      E_DerefAST rng e1              -> tcRhoDeref    ctx rng   e1         expTy
      E_SeqAST rng a b               -> tcRhoSeq      ctx rng   a b        expTy
      E_ArrayRead rng (ArrayIndex a b _ s) -> do -- a[b]
              ta <- inferRho ctx a "array read base"
              tb <- inferRho ctx b "array read index"
              tcRhoArrayRead rng s ta tb expTy
      E_ArrayPoke rng (ArrayIndex b c _ s) a -> do -- a >^ b[c]
              ta <- inferRho ctx a "array poke val"
              tb <- checkRho ctx b (ArrayTypeTC (typeTC ta))
              tc <- inferRho ctx c "array poke idx"
              tcRhoArrayPoke rng s ta tb tc expTy
      E_CompilesAST rng maybe_expr -> do
          result <- case maybe_expr of
                      Nothing -> return $ Errors [text $ "parse error"]
                      Just  e -> tcIntrospect (inferSigma ctx e "compiles")
          -- Note: we infer a sigma, not a rho, because we don't want to
          -- instantiate a sigma with meta vars and then never bind them.
          matchExp expTy (AnnCompiles rng boolTypeTC (CompilesResult result)) "compiles"
      E_KillProcess rng (E_StringAST _ (Left msg)) -> do
          tau <- case expTy of
             (Check t) -> return t
             (Infer _) -> newTcUnificationVarTau $ "kill-process"
          matchExp expTy (AnnKillProcess rng tau msg) "kill-process"
      E_KillProcess _rng _ -> tcFails [text $ "prim kill-process requires a string literal"]

matchExp :: Expected SigmaTC -> AnnExpr SigmaTC -> String -> Tc (AnnExpr SigmaTC)
matchExp expTy ann msg =
     case expTy of
         Check s@(ForAllTC {}) -> do
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
tcSigmaVar :: Context SigmaTC -> ExprAnnot -> T.Text -> Tc (AnnExpr SigmaTC)
tcSigmaVar ctx annot name = do
  debugDoc $ green (text "typecheckVar (sigma): ") <> text (T.unpack name ++ "...")
  -- Resolve the given name as either a variable or a primitive reference.
  case (termVarLookup name (contextBindings ctx)
       ,termVarLookup name (nullCtorBindings ctx)
       ,tcSigmaPrim ctx annot name) of
    -- Regular variable (or non-nullary constructor, which we will
    -- typecheck and codegen as a function (we'll generate the wrapper later).
    (Just avar, _, _)       -> return $ E_AnnVar annot avar
    -- Otherwise, first check to see if it's a nullary constructor,
    -- in which case we synthesize a direct constructor application
    -- rather than a regular variable reference.
    (Nothing, Just (tid, mb_cid), _) -> return $
        case mb_cid of
          Nothing  -> error $ "Nullary ctor without cid?!?"
          Just cid -> AnnAppCtor annot (tidType tid) cid []
    (Nothing, Nothing, Just prim) -> return prim
    (Nothing, Nothing, Nothing)   -> do
         msg <- getStructureContextMessage
         tcFails [text $ "Unknown variable " ++ T.unpack name
                  ++ showSourceRange (rangeOf annot)
                  -- ++ "ctx: "++ unlines (map show (Map.toList $ contextBindings ctx))
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
     debugDoc $ green (text "typecheckVar (rho): ") <> text (T.unpack name ++ " :?: " ++ show expTy)
     v_sigma <- tcSigmaVar ctx rng name
     ann_var <- inst v_sigma ("tcRhoVar[" ++ T.unpack name ++ "]")
     debugDoc $ green (text "typecheckVar v_sigma: ") <> text (T.unpack name ++ " :: " ++ show (typeTC v_sigma))
     debugDoc $ green (text "typecheckVar ann_var: ") <> text (T.unpack name ++ " :: " ++ show (typeTC ann_var))
     matchExp expTy ann_var "var"

tcRhoPrim ctx annot name expTy = do
     case tcSigmaPrim ctx annot name of

       Just v_sigma -> do
         ann_var <- inst v_sigma "tcRhoVar"
         matchExp expTy ann_var "var"

       Nothing -> do
         msg <- getStructureContextMessage
         tcFails [text $ "Unknown variable " ++ T.unpack name
                  ++ showSourceRange (rangeOf annot)
                  ++ "ctx: "++ unlines (map show (Map.toList $ contextBindings ctx))
                  ++ "\nhist: " , msg]

tcSigmaPrim :: Context SigmaTC -> ExprAnnot -> T.Text -> Maybe (AnnExpr SigmaTC)
tcSigmaPrim ctx annot name = do
  case termVarLookup name (primitiveBindings ctx) of
    Just (avar, _) -> Just $  mkAnnPrimitive annot ctx avar
    Nothing        -> Nothing

mkAnnPrimitive :: ExprAnnot -> Context SigmaTC -> TypedId SigmaTC -> AnnExpr SigmaTC
mkAnnPrimitive annot ctx tid =
  AnnPrimitive annot (tidType tid) $
    case Map.lookup (identPrefix $ tidIdent tid)
                    (primitiveOperations ctx) of
        Just (NamedPrim tid)      -> NamedPrim tid
        Just (PrimOp nm ty)       -> PrimOp nm ty
        Just (PrimIntTrunc i1 i2) -> PrimIntTrunc i1 i2
        Just (CoroPrim {}       ) -> error $ "mkAnnPrim saw unexpected CoroPrim"
        Just (PrimInlineAsm {}  ) -> error $ "mkAnnPrim saw unexpected PrimInlineAsm"
        Nothing                   -> NamedPrim tid

-- Now, a bunch of straightforward rules:

--  -----------------------------------------
--  G |- True :: Bool      G |- False :: Bool
tcRhoBool rng b expTy = do
-- {{{
    let ty = PrimIntTC I1
    let ab = AnnLiteral rng ty (LitBool b)
    let check t =
          case t of
            PrimIntTC I1 -> return ab
            m@MetaTyVarTC {} -> do unify m ty "bool literal"
                                   return ab
            RefinedTypeTC v _ _ -> check (tidType v)
            _ -> tcFails [text $ "Unable to check Bool constant in context"
                                ++ " expecting non-Bool type " ++ show t
                                ++ showSourceRange (rangeOf rng)]
    case expTy of
         Infer r -> update r (return ab)
         Check t -> check t
-- }}}

--  ------------------
--  G |- "..." :: Text
tcRhoText rng b expTy = do
-- {{{
-- {{{
    let ty = TyConAppTC "Text" []
    let ab = AnnLiteral rng ty (LitText b)
    let check t =
          case t of
             (TyConAppTC "Text" []) -> return ab
             m@MetaTyVarTC {} -> do unify m ty "text literal"
                                    return ab
             RefinedTypeTC v _ _ -> check (tidType v)
             t -> tcFails [text $ "Unable to check Text constant in context"
                                    ++ " expecting non-Text type " ++ show t
                                    ++ showSourceRange (rangeOf rng)]
    case expTy of
         Infer r -> update r (return ab)
         Check t -> check t
-- }}}

tcRhoTextOrBytes rng (Left txt) expTy = tcRhoText  rng txt expTy
tcRhoTextOrBytes rng (Right bs) expTy = tcRhoBytes rng bs  expTy

--  -------------------------
--  G |- b"..." :: Array Int8
tcRhoBytes rng bs expTy = do
    let ty = ArrayTypeTC (PrimIntTC I8)
    let ab = AnnLiteral rng ty (LitByteArray bs)
    let check t =
          case t of
             ArrayTypeTC m -> do unify m (PrimIntTC I8) "byte array literal"
                                 return ab
             m@MetaTyVarTC {} -> do unify m ty "byte array literal"
                                    return ab
             RefinedTypeTC v _ _ -> check (tidType v)
             t -> tcFails [text $ "Unable to check byte array constant in context"
                                    ++ " expecting non-byte-array type " ++ show t
                                    ++ showSourceRange (rangeOf rng)]
    case expTy of
         Infer r -> update r (return ab)
         Check t -> check t
-- }}}

tcRhoArrayValue ctx tau (AE_Int annot str) = do
  AnnLiteral _ _ literal <- checkRho ctx (E_IntAST annot str) tau
  return (Left literal)

tcRhoArrayValue ctx tau (AE_Expr expr) = do
  ae <- checkRho ctx expr tau
  return $ Right ae

--  e1 :: tau             ...           en :: tau
--  ---------------------------------------------------
--  G |- prim mach-array-literal e1 ... en :: Array tau
tcRhoArrayLit ctx rng mbt args expTy = do
-- {{{
    tau <- case mbt of
             Nothing -> newTcUnificationVarTau $ "prim array type"
             Just t  -> do t0 <- tcType ctx t
                           t' <- resolveType rng (localTypeBindings ctx) t0
                           if isTau t'
                            then return t'
                            else
                              tcFails [text "rho array lit must have tau type; had", pretty t]
    let ty = ArrayTypeTC tau
    args' <- mapM (tcRhoArrayValue ctx tau) args
    let ab = AnnArrayLit rng ty args'
    let check t = case t of
             (ArrayTypeTC rho) -> do unify tau rho "mach-array literal"
                                     return ab
             m@MetaTyVarTC {} -> do unify m ty "mach-array literal"
                                    return ab
             RefinedTypeTC v _ _ -> check (tidType v)
             t -> tcFails [text $ "Unable to check array constant in context"
                                ++ " expecting non-array type " ++ show t
                                ++ showSourceRange (rangeOf rng)]
    case expTy of
         Infer r -> update r (return ab)
         Check t -> check t
  -- There's a problematic interaction going on here.
  -- Integer literals do not impose an immediate constraint
  -- on the types they check against, because the type of an integer
  -- is determined after collecting all type constraints, e.g. to determine
  -- whether 0 :: Int8 or 0 :: Int32.
  -- Second, inferSigma should quantify over escaping un-unified meta tyvars,
  -- but if it did, then (prim mach-array-literal 1 2) would UNSOUNDLY have
  -- the type forall t. Array t instead of the proper non-polymorphic type
  -- Array %%T for some integer type eventually unifying with %%T.

  -- For now, we restrict quantification to values and treat arrays
  -- as non-values, even though an immutable array could be a value...
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
    zt <- zonkType (typeTC ea)
    case zt of
      m@MetaTyVarTC {} -> unify m (TupleTypeTC []) "seq-unit"
      _                -> return ()
    return (AnnLetVar rng id ea eb)
-- }}}


--  G |- e1 ::: tau
--  G |- e2 ::: Ref tau
--  --------------------
--  G |- e1 >^ e2 ::: ()
tcRhoStore ctx rng e1 e2 expTy = do
-- {{{
    a1 <- inferRho ctx e1 "store"
    a2 <- checkRho ctx e2 (RefTypeTC (typeTC a1))
    matchExp expTy (AnnStore rng (TupleTypeTC []) a1 a2) "store"
-- }}}


--  G |- e   ::: Ref tau
--  --------------------
--  G |- e ^ :::     tau
tcRhoDeref ctx rng e1 expTy = do
-- {{{
    tau <- case expTy of
             (Check t) -> return t
             (Infer _) -> newTcUnificationVarTau $ "deref_type"
    a1 <- tcRho ctx e1 (Check $ RefTypeTC tau)
    case typeTC a1 of
      RefTypeTC    {} -> return ()
      MetaTyVarTC  {} -> return ()
      other -> tcFails [text $ "Expected deref-ed expr "
                           ++ "to have ref type, had " ++ show other ++ highlightFirstLine (rangeOf rng)]
    matchExp expTy (AnnDeref rng tau a1) "deref"
-- }}}

--  G |-       e1 :::     tau
--  -------------------------
--  G |- ref_l e1 ::: Ref tau
tcRhoAlloc ctx rng e1 rgn expTy = do
-- {{{
    ea <- case expTy of Check (RefTypeTC t) -> tcRho ctx e1 (Check t)
                        _                   -> inferRho ctx e1 "alloc"
    matchExp expTy (AnnAlloc rng (RefTypeTC (typeTC ea)) ea rgn) "alloc"
-- }}}

--  G |- e1 ::: t1
--  G |-  .......
--  G |- en ::: tn
--  ------------------------------------
--  G |- (e1, ..., en) ::: (t1, ..., tn)
tcRhoTuple :: Context SigmaTC -> ExprAnnot -> [Term] -> Expected TypeTC -> Tc (AnnExpr RhoTC)
-- {{{
tcRhoTuple ctx rng exprs expTy = do
   tup <- case expTy of
     Infer _                -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
     Check (TupleTypeTC ts) -> tcTuple ctx rng exprs [Just t  | t <- ts]
     Check (MetaTyVarTC {}) -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
     Check ty -> tcFailsMore [text $ "typecheck: tuple (" ++ show exprs ++ ") "
                             ++ "cannot check against non-tuple type " ++ show ty]
   matchExp expTy tup (highlightFirstLine (rangeOf rng))
  where
    tcTuple ctx rng exps typs = do
        exprs <- typecheckExprsTogether ctx exps typs
        let tys = map typeTC exprs
        return $ AnnTuple rng (TupleTypeTC tys) exprs

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
tcRhoArrayRead :: ExprAnnot -> SafetyGuarantee -> AnnExpr SigmaTC -> AnnExpr SigmaTC -> Expected RhoTC -> Tc (AnnExpr RhoTC)
-- {{{
tcRhoArrayRead annot sg base aiexpr expTy = do
  let rng = rangeOf annot
  let ck t = do
        -- TODO check aiexpr type is compatible with Word
        unify (PrimIntTC I32) (typeTC aiexpr) "arrayread idx type"
        let expr = AnnArrayRead annot t (ArrayIndex base aiexpr rng sg)
        matchExp expTy expr "arrayread"

  let check t = case t of
        ArrayTypeTC t -> do ck t
        MetaTyVarTC _ -> do
            t <- case expTy of
                  Check t -> return t
                  Infer _ -> newTcUnificationVarTau $ "arrayread_type"
            unify (ArrayTypeTC t) (typeTC base) "arrayread type"
            ck t
        RefinedTypeTC v _ _ -> check (tidType v)
        _ ->
            tcFails [text $ "Unable to arrayread expression of non-array type " ++ show (typeTC base)
                        ++ " (context expected type " ++ show expTy ++ ")"
                        ++ highlightFirstLine rng]
  check (typeTC base)
-- }}}

-----------------------------------------------------------------------

-- G |-  v   ::: t
-- G |- b[i] ::: Array t
-- ---------------------
-- G |- v >^ b[i] ::: ()
tcRhoArrayPoke annot s v base i expTy = do
-- {{{
  let ck t = do
      -- TODO check aiexpr type is compatible with Word
      unify t (typeTC v) "arraypoke type"
      let expr = AnnArrayPoke annot (TupleTypeTC [])
                                    (ArrayIndex base i (rangeOf annot) s) v
      matchExp expTy expr "arraypoke"

  let check t = case t of
        ArrayTypeTC t -> ck t
        MetaTyVarTC _ -> do
            t <- newTcUnificationVarTau $ "arraypoke_type"
            unify (ArrayTypeTC t) (typeTC base) "arraypoke type"
            ck t
        RefinedTypeTC v _ _ -> check (tidType v)
        _ ->
          tcFails [text $ "Unable to arraypoke expression of type " ++ show (typeTC base)
                      ++ " (context expected type " ++ show expTy ++ ")"
                      ++ highlightFirstLine (rangeOf annot)]
  check (typeTC base)
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
    ea <- tcRho ctx a (Check boolTypeTC)
    eb <- tcRho ctx b expTy
    ec <- tcRho ctx c expTy
    unify (typeTC eb) (typeTC ec) "IfAST: types of branches didn't match"
    -- TODO use subsumption instead of unification?
    return (AnnIf rng (typeTC eb) ea eb ec)
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
                 Just ta -> do t <- tcType ctx ta
                               checkSigma ctx e1 t
    let ctx' = prependContextBindings ctx [bindingForVar $ TypedId (typeTC a1) id]
    a2 <- tcRho ctx' e2 mt
    return (AnnLetVar rng id a1 a2)
  where
    boundName    = evarName v
    maybeVarType = evarMaybeType v
    isRecursiveFunction boundName expr =
                       (boundName `elem` freeVars expr && isFnAST expr)
                  where   isFnAST (E_FnAST {}) = True
                          isFnAST _            = False
    -- We'll only warn about recursive function bindings;
    -- shadowing is permissible, and erroneous definitions like
    --     let x = x; in x end
    -- will be caught by the usual variable scoping rules.
    errMsg = "Recursive bindings should use 'rec', not 'let':"
           ++ highlightFirstLine (rangeOf rng)
-- }}}

{-
  rec a = body_a;
      b = body_b;
      ...;
   in e end
-}
-- {{{
tcRhoLetRec :: Context SigmaTC -> ExprAnnot -> [TermBinding TypeAST]
                -> Term -> Expected TypeTC  -> Tc (AnnExpr RhoTC)
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
    verifyNonOverlappingBindings (rangeOf rng) "rec" ctxBindings

    -- Typecheck each binding
    tcbodies <- forM (zip unificationVars recBindings) $
       (\(u, TermBinding v b) -> do
           vExpTy <- case evarMaybeType v of
             Nothing -> do r <- tcLift $ newIORef (error "case branch")
                           return (Infer r)
             Just ta -> do t <- tcType ctx ta
                           return (Check t)
           b' <- tcRho ctx b vExpTy
           unify u (typeTC b') ("recursive binding " ++ T.unpack (evarName v))
           return b'
       )

    -- Typecheck the body as well
    e' <- tcRho ctx e mt

    case tcbodies of
      [AnnAppCtor _ _ _ [E_AnnFn _]] -> do
        return $ AnnLetRec rng ids tcbodies e'
      _ -> do
        -- tcLift $ putDocLn $ showStructure (head tcbodies)
        let fns = [f | (E_AnnFn f) <- tcbodies]
        let nonfns = filter notAnnFn tcbodies
                      where notAnnFn (E_AnnFn _) = False
                            notAnnFn _           = True
        sanityCheck (null nonfns) "Recursive bindings should only contain functions!"
        return $ mkFunctionSCCs ids fns e' (AnnLetFuns rng)
-- }}}

-- G |- e ::: forall a1::k1..an::kn, rho
-- G |- t_n <::: k_n                          (checked later)
-- ------------------------------------------
-- G |- e :[ t1..tn ]  ::: rho{t1..tn/a1..an}
tcRhoTyApp :: Context SigmaTC -> ExprAnnot -> Term -> [TypeAST] -> Expected RhoTC -> Tc (AnnExpr RhoTC)
tcRhoTyApp ctx annot e tsAST expTy = do
-- {{{
    debug $ "ty app: inferring sigma type for base..."
    aeSigma <- inferSigma ctx e "tyapp"
    debug $ "ty app: base has type " ++ show (typeTC aeSigma)
    case (tsAST, typeTC aeSigma) of
      ([]   , _           ) -> matchExp expTy aeSigma "empty-tyapp"
      (tsAST, ForAllTC  {}) -> do
         t1tn <- mapM (tcType ctx) tsAST
         let resolve = resolveType annot (localTypeBindings ctx)
         debug $ "local type bindings: " ++ show (localTypeBindings ctx)
         debug $ "********raw type arguments: " ++ show t1tn
         types <- mapM resolve t1tn
         expr <- instWith annot aeSigma types
         matchExp expTy expr "tyapp"
      (_        , MetaTyVarTC _ ) -> do
        tcFails [text $ "Cannot instantiate unknown type of term:"
                ,text $ highlightFirstLine $ rangeOf aeSigma
                ,text $ "Try adding an explicit type annotation."
                ]
      (_        , othertype   ) -> do
        tcFails [text $ "Cannot apply type args to expression of"
                   ++ " non-ForAll type: " ++ show othertype
                ,text $ highlightFirstLine $ rangeOf e]
-- }}}


-- G |- e ~~~> a1 ::: t1
-- G |- t1 is an instance of t
-- ------------------------------------------
-- G |- e as t  ~~~>  a1 ::: t
tcRhoTyCheck ctx _annot e tya expTy = do
-- {{{
    ty  <- tcType ctx tya
    ann <- checkSigma ctx e ty
    matchExp expTy ann "tycheck"
-- }}}

-- G |- b  ~~> f ::: ((s1 ... sn) -> sr)
-- G |- e1 ~~> a1 ::: t1     t1 <= s1
-- G |-  .......
-- G |- en ~~> an ::: tn     tn <= sn
-- ------------------------------------------
-- G |- b e1 ... en ~~> f a1 ... an ::: sr
-- {{{
tcRhoCall :: Context SigmaTC -> ExprAnnot
              -> ExprAST TypeAST -> [ExprAST TypeAST]
              -> Expected SigmaTC -> Tc (AnnExpr RhoTC)
tcRhoCall ctx rng base argstup exp_ty = do
   -- TODO think harder about when it's safe to push exp_ty down
   debug $ "tcRhoCall " ++ show exp_ty
   r <- newTcRef (error $ "tcRho>SigmaCall: empty result: ")
   app <- tcSigmaCall ctx rng base argstup (Infer r)
   instSigma app exp_ty

tryGetVarName (E_VarAST _ v) = T.unpack $ evarName v
tryGetVarName _ = ""

tcSigmaCall :: Context SigmaTC -> ExprAnnot -> ExprAST TypeAST
            -> [ExprAST TypeAST] -> Expected SigmaTC -> Tc (AnnExpr SigmaTC)

tcSigmaCall ctx rng (E_PrimAST _ name@"assert-invariants" _ _) argtup exp_ty = do
    args <- mapM (\arg -> checkSigma ctx arg boolTypeTC) argtup
    let unitType = TupleTypeTC []
    let fnty = mkFnTypeTC [boolTypeTC | _ <- argtup] unitType
    let prim = NamedPrim (TypedId fnty (Ident (T.pack name) 1))
    let primcall = AnnCall rng unitType (AnnPrimitive rng fnty prim) args
    id <- tcFresh "assert-invariants-thunk"
    let thunk = Fn (TypedId (mkFnTypeTC [] unitType) id) [] primcall () rng
    matchExp exp_ty (AnnLetFuns rng [id] [thunk] (AnnTuple rng (TupleTypeTC []) [])) name

tcSigmaCall ctx rng base argexprs exp_ty = do
        annbase <- inferRho ctx base "called base"
        let fun_ty = typeTC annbase
        (args_ty, res_ty, _cc, _) <- unifyFun fun_ty (length argexprs) ("tSC("++tryGetVarName base++")" ++ highlightFirstLine (rangeOf rng))
        debugDoc $ text "tcSigmaCall: fn type of" <+> pretty annbase <+> text "is " <> pretty fun_ty <+> text ";; cc=" <+> text (show _cc)
        debugDoc $ string (highlightFirstLine (rangeOf rng))

        debugDoc $ text "call: fn args ty is " <> pretty args_ty
        debug $ "call: arg exprs are " ++ show argexprs
        sanityCheck (eqLen argexprs args_ty) $
                "tcSigmaCall expected equal # of arguments! Had "
                ++ (show $ List.length argexprs) ++ "; expected "
                ++ (show $ List.length args_ty)
                ++ highlightFirstLine (rangeOf rng)
        --tcLift $ putStrLn $ "tcSigmaCall of " ++ show base
        --tcLift $ putStrLn $ show (zip argexprs args_ty)

        -- Strip refinements; just because a formal parameter has a given refinement,
        -- doesn't mean that the actual will necessarily follow the same refinement!
        args <- sequence [checkSigma ctx arg (shallowStripRefinedTypeTC ty) | (arg, ty) <- zip argexprs args_ty]
        debug $ "call: annargs: "
        debugDoc $ showStructure (AnnTuple rng (TupleTypeTC (map typeTC args)) args)
        debugDoc $ text "call: res_ty  is " <> pretty res_ty
        debugDoc $ text "call: exp_ty is " <> pretty exp_ty
        debugDoc $ text "tcRhoCall deferring to instSigma"
        let app = mkAnnCall rng res_ty annbase args
        debugDoc $ text "call: overall ty is " <> pretty (typeTC app)
        matchExp exp_ty app "tcSigmaCall"

mkAnnCall rng res_ty annbase args =
  case annbase of
    E_AnnTyApp _ _ annprim@(AnnPrimitive _ _ (NamedPrim (TypedId _ (GlobalSymbol gs)))) [_argty]
         | T.unpack gs == "prim_arrayLength"
      -> AnnCall rng res_ty annprim args
    E_AnnTyApp _ _ (AnnPrimitive _ _ (NamedPrim (TypedId _ (GlobalSymbol gs)))) [argty]
         | T.unpack gs == "allocDArray"
      -> AnnAllocArray rng res_ty arraySize argty where [arraySize] = args
    E_AnnVar _rng (_tid, Just cid)
      -> AnnAppCtor rng res_ty cid  args
    _ -> AnnCall rng res_ty annbase args

unifyFun :: RhoTC -> Int -> String -> Tc ([SigmaTC], RhoTC, Unifiable CallConv, Unifiable ProcOrFunc)
unifyFun (FnTypeTC args res cc ft) _ _msg = return (args, res, cc, ft)
unifyFun (ForAllTC {}) _ str = tcFails [text $ "invariant violated: sigma passed to unifyFun!"
                                        ,text $ "For now, lambdas given forall types must be annotated with forall markers."
                                        ,text str]
unifyFun tau nargs msg = do
        arg_tys <- mapM (\_ -> newTcUnificationVarTau "fn args ty") (replicate nargs ())
        res_ty <- newTcUnificationVarTau ("fn res ty:" ++ msg)
        cc <- genUnifiableVar
        ft <- genUnifiableVar
        unify tau (FnTypeTC arg_tys res_ty cc ft) ("unifyFun(" ++ msg ++ ")")
        return (arg_tys, res_ty, cc, ft)
-- }}}

-- G{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { x1 : t1 => ... => xn : tn => e } ::: { t1 => ... => tn => tb }
--
-- {{{
tcRhoFn ctx f expTy = do
  sigma <- tcSigmaFn ctx f expTy
  debug $ "**********************tcRhoFn instantiating " ++ show (typeTC sigma)
  inst sigma "tcRhoFn"
-- }}}

-- G{a1:k1}...{an:kn}{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { forall a1:k1, ..., an:kn, x1 : t1 => ... => xn : tn => e } :::
--        forall a1:k1, ..., an:kn,    { t1 => ... =>      tn => tb }
-- {{{
tcSigmaFn :: Context SigmaTC -> FnAST TypeAST -> Expected SigmaTC -> Tc (AnnExpr SigmaTC)
tcSigmaFn ctx fnAST expTyRaw = do
  debug2 $ "****************tcSigmaFn: nexpTyRaw is " ++ show expTyRaw ++ " for " ++ show (fnAstName fnAST)
  case (fnTyFormals fnAST, expTyRaw) of
    ([], Check (ForAllTC exp_ktvs _)) ->
        -- Our function didn't have a forall, but its type annotation did.
        -- We'll just copy the type parameters to the function and try again.
        tcSigmaFn ctx (fnAST { fnTyFormals = map mkTypeFormal exp_ktvs }) expTyRaw

    ([], _) ->
        -- Our function has no type parameters, and either it had no annotation
        -- or we are inferring its type (and we'll infer a monotype).
        tcRhoFnHelper ctx fnAST expTyRaw

    (tyformals, _) -> do
        let annot = fnAstAnnot fnAST
        let ktvs = map convertTyFormal tyformals
        taus <- genTauUnificationVarsLike ktvs (\n -> "fn type parameter " ++ show n ++ " for " ++ T.unpack (fnAstName fnAST))

        let extTyCtx = ctx { localTypeBindings = extendTypeBindingsWith ctx ktvs taus }

        debugDoc $ text "tcSigmaFn: f is " <> pretty (show fnAST)
        debugDoc $ text "tcSigmaFn: expTyRaw is " <> pretty expTyRaw
        debugDoc $ text "tcSigmaFn: tyformals is " <> pretty tyformals
        debugDoc $ text "tcSigmaFn: ktvs is " <> pretty ktvs
        debugDoc $ text "tcSigmaFn: taus is " <> pretty taus

        mb_rho <-
          case expTyRaw of
            Check (ForAllTC exp_ktvs exp_rho_raw) -> do
              -- Suppose we have something like
              -- f ::  forall a:Boxed, { List a }         [exp_ktvs = a]
              -- f =  { forall b:Boxed,   Nil ! }         [    ktvs = b]
              -- Here, we need the expected type to get the right type for
              -- the instantiation of Nil, but we can't use the type variable 'a
              -- in the expression, because only 'b is in scope.
              -- So, we must rewrite rho in terms of the function's type variables
              -- (rather than rewriting the body in terms of the expected type).
              sanityCheck (eqLen ktvs exp_ktvs)
                         ("tcSigmaFn: expected same number of formals for "
                          ++ show ktvs ++ " and " ++ show exp_ktvs)
              exp_rho' <- resolveType annot (extendTypeBindingsWith ctx exp_ktvs taus) exp_rho_raw
              return $ Just exp_rho'
            _ -> return $ Nothing

        -- While we're munging, we'll also make sure the names are all distinct.
        uniquelyNamedFormals <- getUniquelyNamedAndRetypedFormals' ctx annot
                                       (fnFormals fnAST) (fnAstName fnAST)
                                       (localTypeBindings extTyCtx)

        -- Extend the variable environment with the function arg's types.
        let extCtx = extendContext extTyCtx uniquelyNamedFormals

        -- Check or infer the type of the body.
        (annbody, body_ty, uniquelyNamedBinders) <- case mb_rho of
          -- for Infer or for Check of a non-ForAll type
          Nothing       -> do annbody <- inferSigma extCtx (fnAstBody fnAST) "poly-fn body"
                              return (annbody, typeTC annbody, uniquelyNamedFormals)
          Just exp_rho' -> do
                let var_tys = map tidType uniquelyNamedFormals
                (arg_tys, body_ty, _cc, _ft) <- unifyFun exp_rho' (length var_tys) ("poly-fn-lit" ++ highlightFirstLine (rangeOf annot))

                case (any tcContainsRefinements arg_tys,
                      any tcContainsRefinements var_tys ) of
                   (True, True) ->
                     tcFails [text $ "Cannot yet check a function which has refinements"
                             ++ " on both its explicit argument bindings and its type signature."]
                   (ar, vr) -> do
                     debugDoc3 $ string "!!!!!!!!!!!!!!!!!!!!!!!! (sigma)"
                     debugDoc3 $ text (show $ fnAstName fnAST)
                     debugDoc3 $ text "args/vars refined: " <> pretty (ar,vr)
                     debugDoc3 $ string "var_tys: " <+> pretty var_tys
                     debugDoc3 $ string "arg_tys: " <+> pretty arg_tys

                     mapM_ (tcSelectTy annot) (zip arg_tys var_tys)

                debugDoc $ string "arg_tys: " <+> pretty arg_tys
                debugDoc $ string "zipped : " <+> pretty (zip arg_tys var_tys)
                let unMeta (MetaTyVarTC m) = m
                    unMeta other = error $ "unMeta called with " ++ show other
                _ <- mapM (checkAgainst (map unMeta taus)) (zip arg_tys var_tys)
                var_tys'' <- mapM shZonkType var_tys
                debugDoc $ string "var_tys'': " <+> pretty var_tys''
                debugDoc $ string "metaOf var_tys  : " <+> pretty (show $ collectAllUnificationVars var_tys)
                debugDoc $ string "metaOf var_tys'': " <+> pretty (show $ collectAllUnificationVars $ map unMBS var_tys'')
                -- mvar_tys'' <- mapM shZonkMetaType (collectAllUnificationVars var_tys)

                pickedTys <- mapM pickBetween (zipTogether arg_tys var_tys)
                let uniquelyNamedBinders =
                             map (\(TypedId _ id, ty) -> TypedId ty id)
                                 (zip uniquelyNamedFormals pickedTys)

                annbody <- checkRho extCtx (fnAstBody fnAST) body_ty
                return (annbody, body_ty, uniquelyNamedBinders)

        debugDoc $ text "inferred raw type of body of polymorphic function: "
                        <> pretty (typeTC annbody)

        let fnty0 = ForAllTC ktvs $
                fnTypeTemplate fnAST argtys body_ty
                  where argtys = map tidType uniquelyNamedBinders

        -- The function type is expressed in terms of meta type variables,
        -- which have now served their purpose and must be replaced by
        -- bound type variables. We'll do the replacement by first making sure
        -- that nothing has been unified with them so far, and then writing
        -- the appropriate bound type variable to the ref.
        _ <- mapM (\(t, (tv, _)) -> do
                     t' <- shallowZonk t
                     case t' of
                       (MetaTyVarTC m) -> do
                            debugDoc $ text "zonked " <> pretty t <> text " to " <> pretty t <> text "; writing " <> pretty tv
                            writeTcMetaTC m (TyVarTC tv)
                       _ -> tcFails [text "expected ty param metavar to be un-unified, instead had " <> pretty tv]
                  ) (zip taus ktvs)
        -- Zonk the type to ensure that the meta vars are completely gone.
        debugDoc $ text "inferred raw overall type of polymorphic function: " <> pretty fnty0
        debugDoc $ text "zonking; (meta)/tyvars were " <> list (map pretty (zip taus ktvs))
        fnty <- zonkType fnty0
        debugDoc $ text "inferred overall type of body of polymorphic function: " <> pretty fnty

        -- We also need to zonk the expected type, which might have wound up
        -- getting some of its meta type variables unified with taus that now
        -- refer to bound type variables.
        expTy' <- case expTyRaw of
                    Check t -> liftM Check (zonkType t)
                    Infer _ -> return expTyRaw

        -- Note we collect free vars in the old context, since we can't possibly
        -- capture the function's arguments from the environment!
        let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol $ fnAstName fnAST))
                              uniquelyNamedBinders annbody () annot
        debugDoc $ text "tcSigmaFn calling matchExp  uniquelyNamedFormals = " <> pretty (map tidType uniquelyNamedFormals)
        debugDoc $ text "tcSigmaFn calling matchExp  expTyRaw = " <> pretty expTyRaw
        debugDoc $ text "tcSigmaFn calling matchExp, expTy'   = " <> pretty expTy'
        matchExp expTy' fn "tcSigmaFn"

mkTypeFormal (BoundTyVar nm, kind) = TypeFormal nm kind
mkTypeFormal (othervar, _kind) =
    error $ "Whoops, expected only bound type variables!\n" ++ show othervar

-- Extend the type environment with the forall-bound variables
-- declared in the function literal.
extendTypeBindingsWith ctx ktvs taus =
      foldl' ins (localTypeBindings ctx) (zip taus ktvs)
       where ins m (mtv, (BoundTyVar nm, _k)) = Map.insert nm mtv m
             ins _ (_ ,  (SkolemTyVar {}, _))= error "ForAll bound a skolem!"

-- TODO this can result in losing annotations...
-- If we have something like
--       foo :: { % ra : T : e(ra) }
--       foo = { a : % rb : T : p(rb) }
-- we will completely drop p(rb)!
pickBetween (mb_argty, mb_varty) = do
       case (mb_argty, mb_varty) of
         -- If the argty is a meta variable, we might get more specific error messages
         -- by using the definitely-not-less-specific varty.
         (Just (MetaTyVarTC {}), Just varty) -> return varty
         -- Otherwise, the argty should have at least as much information as the varty,
         -- since the fnTypeTemplate definition in Main.hs will copy the varty's types.
         (Just argty, Just _) -> return argty
         (_, Just varty) -> return varty -- Mismatch, will be caught later by matchExp
         _ -> error $ "zipTogether lied"
-- }}}

mbFreshRefinementVar :: Context SigmaTC -> TypeAST -> Tc [TypedId TypeTC]
mbFreshRefinementVar ctx tv = do
  case tv of
    RefinedTypeAST nm t _e -> do
         id <- tcFresh nm
         t' <- tcType ctx t
         return [TypedId t' id]
    _ -> return []

-- G{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { x1 : t1 => ... => xn : tn => e } ::: { t1 => ... => tn => tb }
-- {{{
tcRhoFnHelper :: Context SigmaTC -> FnAST TypeAST -> Expected RhoTC -> Tc (AnnExpr SigmaTC)
tcRhoFnHelper ctx f expTy = do
    let annot = fnAstAnnot f
    let rng = rangeOf annot
    -- While we're munging, we'll also make sure the names are all distinct.

    -- Add the refinement vars to the context, so that they are in-scope
    -- when checking type refinements.
    -- TODO use levels or something so that function bodies can't refer to
    --      refinement variables from exprs (unless embedded in refn. types).
    refinementVars <- concatMapM (mbFreshRefinementVar ctx) (map tidType $ fnFormals f)
    let ctx' = extendContext ctx refinementVars

    --tcLift $ putStrLn $ "mode is " ++ (case expTy of Infer _ -> "infer"
    --                                                 Check fnty -> "check against " ++ show fnty)

    uniquelyNamedFormals <- getUniquelyNamedAndRetypedFormals' ctx' annot
                                                  (fnFormals f) (fnAstName f)
                                                  (localTypeBindings ctx)

    (mbExpBodyTy, uniquelyNamedBinders) <- case expTy of
       Infer _    -> do
                           return (Nothing, uniquelyNamedFormals)
       Check fnty -> do
                           -- |arg_tys| are the corresponding arguments expected
                           -- by the context (or a type annotation on the binder'
                           -- for this function).
                           (arg_tys, body_ty, _cc, _ft) <- unifyFun fnty (length uniquelyNamedFormals) ("@" ++ highlightFirstLine rng)

                           -- |var_tys| are the types written down by the programmer
                           -- on the function's argument variables.
                           let var_tys = map tidType uniquelyNamedFormals

                           -- It's perhaps a little bit counter-intuitive, but
                           -- the var_tys are the "expected" types, and the
                           -- external annotations are the "actual" types. One
                           -- way of looking at this is that we can alter the
                           -- types associated with the function's arg vars,
                           -- but we can't alter the context's expectations.

                           debugDoc3 $ text "checking subsumption betweeen " <$> indent 4 (pretty (zip arg_tys var_tys))
                           _ <- sequence [subsCheckTy argty varty "mono-fn-arg" |
                                           (argty, varty) <- zip arg_tys var_tys]

                           case (filter tcContainsRefinements arg_tys,
                                 filter tcContainsRefinements var_tys ) of
                               (ars@(_:_), vrs@(_:_)) ->
                                 tcFails [text $ "Cannot yet check a function (" ++ T.unpack (fnAstName f) ++ ") which has refinements"
                                                   ++ " on both its explicit argument bindings and its type signature."
                                         , indent 2 (text "Refined signature types:" <+> indent 2 (pretty ars))
                                         , indent 2 (text "Refined variable types:" <+> indent 2 (pretty vrs))
                                         , string $ highlightFirstLine rng]
                                         -- When we remove this check, we should un-comment one of the tests in
                                         -- bootstrap/testscase/test-fn-precond-2
                               (ar, vr) -> do
                                 debugDoc3 $ string "!!!!!!!!!!!!!!!!!!!!!!!! (rho)"
                                 debugDoc3 $ text (show $ fnAstName f)
                                 debugDoc3 $ text "args/vars refined: " <> pretty (ar,vr)
                                 debugDoc3 $ string "var_tys: " <+> pretty var_tys
                                 debugDoc3 $ string "arg_tys: " <+> pretty arg_tys

                           pickedTys <- mapM pickBetween (zipTogether arg_tys var_tys)
                           let uniquelyNamedBinders =
                                        map (\(TypedId _ id, ty) -> TypedId ty id)
                                            (zip uniquelyNamedFormals pickedTys)

                           return (Just body_ty, uniquelyNamedBinders)

    -- Extend the variable environment with the function arg's types.
    let extCtx = extendContext ctx uniquelyNamedBinders

    -- Check or infer the type of the body.
    annbody <- case mbExpBodyTy of
      Nothing      -> do inferSigma extCtx (fnAstBody f) "mono-fn body"
      Just body_ty -> do checkRho extCtx (fnAstBody f) body_ty

    let fnty = fnTypeTemplate f argtys retty
                where argtys = map tidType uniquelyNamedBinders
                      retty  = case mbExpBodyTy of
                                 Nothing -> typeTC annbody
                                 Just rt -> rt

    fnty' <- zonkType fnty

    debug2 $ "fnty for " ++ (show (fnAstName f)) ++ " is " ++ show fnty
    debug2 $ "zonked fnty for " ++ (show (fnAstName f)) ++ " is " ++ show fnty'

    -- Note we collect free vars in the old context, since we can't possibly
    -- capture the function's arguments from the environment!
    let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol $ fnAstName f))
                          uniquelyNamedBinders annbody () annot
    matchExp expTy fn "tcRhoFn"
-- }}}

tcSelectTy annot (argty, varty) = do
    case (argty, varty) of
       (_, MetaTyVarTC {}) -> do return ()
       (MetaTyVarTC {}, _) -> do
         tcFails [text "didn't expect argty to be meta ty var without varty also being the same..."
                 , prettyWithLineNumbers (rangeOf annot)
                 , text "arg ty:" <+> pretty argty
                 , text "var ty:" <+> pretty varty
                 ]
       _ -> return ()

-- {{{ Helpers for type-checking function literals.
extendContext :: Context SigmaTC -> [TypedId TypeTC] -> Context SigmaTC
extendContext ctx protoFormals =
                 prependContextBindings ctx (map bindingForVar protoFormals)

fnTypeTemplate :: FnAST TypeAST -> [TypeTC] -> TypeTC -> TypeTC
fnTypeTemplate f argtypes retty =
  -- Compute "base" function type, ignoring any type parameters.
  let procOrFunc = if fnWasToplevel f then FT_Proc else FT_Func in
  FnTypeTC argtypes retty (UniConst FastCC) (UniConst procOrFunc)

-- Verify that the given formals have distinct names.
getUniquelyNamedFormals :: SourceRange -> [TypedId ty] -> T.Text -> Tc [TypedId ty]
getUniquelyNamedFormals rng rawFormals fnProtoName = do
    verifyNamesAreDistinct rng (T.unpack fnProtoName)
                               (map (identPrefix . tidIdent) rawFormals)
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
                tcFails [text $ "Cannot rename global symbol " ++ show name]

-- | Verify that the given formals have distinct names,
-- | and return unique'd versions of each.
getUniquelyNamedAndRetypedFormals' ctx annot rawFormals fnProtoName  tybinds = do
    ufs'0 <- getUniquelyNamedFormals (rangeOf annot) rawFormals fnProtoName
    mapM retypeAndResolve ufs'0
   where retypeAndResolve v = do
            fmapM_TID (tcType ctx) v >>= retypeTID (resolveType annot tybinds)

tcType :: Context TypeTC -> TypeAST -> Tc TypeTC
tcType ctx typ = tcType' ctx [] RIS_False typ

data IsRefinementInScope = RIS_True | RIS_False deriving Show

tcType' :: Context TypeTC -> [Ident] -> IsRefinementInScope -> TypeAST -> Tc TypeTC
tcType' ctx refinementArgs ris typ = do
  let q = tcType' ctx refinementArgs RIS_False
  case typ of
        MetaPlaceholderAST MTVTau   nm -> newTcUnificationVarTau nm
        MetaPlaceholderAST MTVSigma nm -> newTcUnificationVarSigma nm
        PrimIntAST         sz -> return (PrimIntTC sz )
        PrimFloat64AST        -> return (PrimFloat64TC)
        TyVarAST      tv      -> return $ TyVarTC tv
        RefTypeAST    ty      -> liftM   RefTypeTC   (q ty)
        ArrayTypeAST  ty      -> liftM   ArrayTypeTC (q ty)
        TupleTypeAST  types   -> liftM   TupleTypeTC (mapM q types)
        CoroTypeAST   s r     -> liftM2  CoroTypeTC  (q s) (q r)
        TyConAppAST nm types  -> liftM (TyConAppTC nm) (mapM q types)
        ForAllAST ktvs rho    -> do taus <- genTauUnificationVarsLike ktvs (\n -> "tcType'forall param " ++ show n)
                                    let xtvs = map (\(tv,_) -> TyVarTC tv) ktvs
                                    let ctx' = ctx { localTypeBindings = extendTypeBindingsWith ctx ktvs taus }
                                    rv <- liftM (ForAllTC ktvs) (tcType' ctx' refinementArgs RIS_False rho)
                                    let tryOverwrite (tv, MetaTyVarTC m) = do
                                            mty <- readTcMeta m
                                            case mty of
                                                Nothing -> do ty' <- zonkType tv
                                                              writeTcMetaTC m ty'
                                                Just  _ -> do tcFails [text "tcType' didn't expect unification variable associated"
                                                                      ,text "with a bound type variable to get unified!"]
                                        tryOverwrite (tv, tau) = do
                                          tcFails [text "tcType'.tryOverwrite could not handle non-meta tau for type variable " <> pretty tv
                                                  ,pretty tau]
                                    mapM_ tryOverwrite (zip xtvs taus)
                                    return rv
        FnTypeAST ss r cc ft -> do
          let rng    = MissingSourceRange $ "refinement for fn type..."
          let refinedFormals = concatMap (\t ->
                           case t of
                             RefinedTypeAST nm t' _ ->
                               [TypedId t' (Ident (T.pack nm) 0)]
                             _ -> []) ss

          uniqRefinedFormals <- getUniquelyNamedAndRetypedFormals' ctx (annotForRange rng)
                                   refinedFormals (T.pack $ "refinement for fn type...")
                                   (localTypeBindings ctx)

          let extCtx = extendContext ctx uniqRefinedFormals

          let refinementArgs' = mkRefinementArgs ss `replacingUniquesWith`
                                 (map tidIdent uniqRefinedFormals)

          --tcLift $ putDocLn $ text "tcType' checking " <> pretty typ <+>
          --                     text "w/ context extended with" <+> pretty uniquelyNamedFormals
          --                     <+> text "and refinement args" <+> pretty refinementArgs'

          ss' <- mapM (tcType' extCtx refinementArgs' RIS_True) ss
          -- The binding for the function's return type, if any, should
          -- be in-scope for its refinement.
          extCtx' <- case r of
                       RefinedTypeAST nm r' _ -> do
                            unf <- getUniquelyNamedAndRetypedFormals' ctx (annotForRange rng)
                                       [TypedId r' (Ident (T.pack nm) 0)] (T.pack "refinement for fn return type...")
                                       (localTypeBindings ctx)
                            return $ extendContext extCtx unf
                       _ -> return extCtx
          r'  <- tcType' extCtx' refinementArgs' RIS_False r
          return $ FnTypeTC ss' r' (UniConst cc) (UniConst ft)
        RefinedTypeAST nm ty e -> do
          (ctx' , id) <-
                 case ris of
                    RIS_True ->
                      case termVarLookup (T.pack nm) (contextBindings ctx) of
                          Just (v, _) -> return (ctx, tidIdent v)
                          _           -> tcFails [text "unable to find refinement type var in context"]
                    RIS_False -> do
                      -- The caller did not extend the context with this refinement,
                      -- so we should do it ourselves.
                      let rng    = MissingSourceRange $ "refinement " ++ nm
                      let formal = TypedId ty (Ident (T.pack nm) 0)
                      [unf] <- getUniquelyNamedAndRetypedFormals' ctx (annotForRange rng)
                                   [formal] (T.pack "refinement for fn return type...")
                                   (localTypeBindings ctx)
                      return (extendContext ctx [unf], tidIdent unf)

          e' <- checkRho ctx' e (PrimIntTC I1)
          ty' <- tcType' ctx' refinementArgs RIS_False ty
          return $ RefinedTypeTC (TypedId ty' id) e' refinementArgs

mkRefinementArgs types =
    map (\(t, idx) ->
            case t of
                 RefinedTypeAST nm _ _ -> Ident (T.pack nm) 0
                 _                     -> Ident (T.pack $ "_" ++ show idx) (-1))
        (zip types [0..])

replacingUniquesWith fakes reals =
  let m = Map.fromList [(txt, uniq) | Ident txt uniq <- reals] in
  map (\x@(Ident t _) -> case Map.lookup t m of Nothing -> x
                                                Just u  -> Ident t u) fakes
-- }}}


-- {{{ CASE scrutinee OF branches END
tcRhoCase :: Context SigmaTC -> ExprAnnot -> ExprAST TypeAST
          -> [CaseArm EPattern Term TypeAST] -> Expected RhoTC -> Tc (AnnExpr RhoTC)
tcRhoCase ctx rng scrutinee branches expTy = do
  -- (A) The expected type applies to the branches,
  --     not to the scrutinee.
  -- (B) Each pattern must check against the scrutinee type.
  -- (C) Each branch must check against the expected type,
  --     as well as successfully unify against the overall type.
  -- (D) Each pattern must have the correct arity.
  ascrutinee <- inferRho ctx scrutinee "scrutinee"
  u <- newTcUnificationVarTau "case"
  debugDoc $ text "case scrutinee has type " <> pretty (typeTC ascrutinee)
  debugDoc $ text "metavar for overall type of case is " <> pretty u
  debugDoc $ text " exp ty is " <> pretty expTy
  let checkBranch (CaseArm pat body guard _ brng) = do
      debugDoc $ text "checking pattern with context ty " <+> pretty (typeTC ascrutinee) <+> string (highlightFirstLine $ rangeOf rng)
      p <- checkPattern ctx pat (typeTC ascrutinee)
      debug $ "case branch pat: " ++ show p
      let bindings = extractPatternBindings p
      debugDoc $ text "case branch generated bindings: " <> list (map pretty bindings)
      let ctxbindings = [varbind id ty | (TypedId ty id) <- bindings]
      verifyNonOverlappingBindings (rangeOf rng) "case" ctxbindings
      let ctx' = prependContextBindings ctx ctxbindings
      aguard <- liftMaybe (\g -> tcRho ctx' g (Check boolTypeTC)) guard
      abody <- tcRho ctx' body expTy
      unify u (typeTC abody) ("Failed to unify all branches of case " ++ highlightFirstLine (rangeOf rng))
      return (CaseArm p abody aguard bindings brng)
  abranches <- forM branches checkBranch
  matchExp expTy (AnnCase rng u ascrutinee abranches) "case"
 where
    checkPattern :: Context SigmaTC -> EPattern TypeAST -> TypeTC -> Tc (Pattern TypeTC)
    -- Make sure that each pattern has the proper arity,
    -- and record its type given a known type for the context in which
    -- the pattern appears.
    checkPattern ctx pattern ctxTy = case pattern of
      EP_Wildcard r       -> do return $ P_Atom $ P_Wildcard r ctxTy
      EP_Variable r v     -> do checkSuspiciousPatternVariable r v
                                id <- tcFreshT (evarName v)
                                return $ P_Atom $ P_Variable r (TypedId ctxTy id)
      EP_Bool     r b     -> do let boolexpr = E_BoolAST (annotForRange r) b
                                annbool <- tcRho ctx boolexpr (Check ctxTy)
                                return $ P_Atom $ P_Bool r (typeTC annbool) b
      EP_Int      r str   -> do (AnnLiteral _ ty (LitInt int))
                                         <- typecheckInt (annotForRange r) str
                                                         (Check ctxTy)
                                --tcLift $ putDocLn $ text ("P_Int " ++ str) <+> pretty ctxTy
                                return $ P_Atom $ P_Int r ty int

      EP_Ctor     r eps s -> do
        info@(CtorInfo cid (DataCtor _ tyformals types _crng)) <- getCtorInfoForCtor ctx s
        sanityCheck (ctorArity cid == List.length eps) $
              "Incorrect pattern arity: expected " ++
              (show $ ctorArity cid) ++ " pattern(s), but got "
              ++ (show $ List.length eps) ++ showSourceRange r
        sanityCheck (ctorArity cid == List.length types) $
              "Invariant violated: constructor arity did not match # types!"
              ++ showSourceRange r

        ty@(TyConAppTC _ metas) <-
                            generateTypeSchemaForDataType ctx (ctorTypeName cid)
        let ktvs = map convertTyFormal tyformals
        ts <- mapM (\ty -> instSigmaWith ktvs ty metas) types
        ps <- sequence [checkPattern ctx p t | (p, t) <- zip eps ts]

        debug $ "checkPattern for "   ++ show (pretty pattern)
        debug $ "*** P_Ctor -  ty   " ++ show (pretty ty     )
        debug $ "*** P_Ctor -  ty   " ++ show (pretty ctxTy  )
        debug $ "*** P_Ctor - metas " ++ show (pretty metas  )
        debug $ "*** P_Ctor - sgmas " ++ show (pretty ts     )

        unify ty ctxTy ("checkPattern:P_Ctor " ++ show cid)
        return $ P_Ctor r ty ps info

      EP_Tuple     r eps  -> do
        ts <-
          case ctxTy of
            TupleTypeTC ts -> return ts
            _ -> do ts <- sequence [newTcUnificationVarTau "tup" | _ <- eps]
                    unify ctxTy (TupleTypeTC ts) "tuple-pattern"
                    return ts
        sanityCheck (eqLen eps ts) $
                "Cannot match pattern against tuple type of "
             ++ "different length." ++ showSourceRange r
        ps <- sequence [checkPattern ctx p t | (p, t) <- zip eps ts]
        return $ P_Tuple r (TupleTypeTC ts) ps
    -----------------------------------------------------------------------
    getCtorInfoForCtor :: Context SigmaTC -> T.Text -> Tc (CtorInfo SigmaTC)
    getCtorInfoForCtor ctx ctorName = do
      let ctorInfos = contextCtorInfo ctx
      case Map.lookup ctorName ctorInfos of
        Just [info] -> return info
        elsewise -> tcFails [text $ "Typecheck.getCtorInfoForCtor: Too many or"
                                    ++ " too few definitions for $" ++ T.unpack ctorName
                                    ++ "\n\t" ++ show (pretty elsewise)]

    generateTypeSchemaForDataType :: Context SigmaTC -> DataTypeName -> Tc RhoTC
    generateTypeSchemaForDataType ctx typeName = do
      case Map.lookup typeName (contextDataTypes ctx) of
        Just [dt] -> do
          formals <- mapM (\_ -> newTcUnificationVarTau "dt-tyformal") (dataTypeTyFormals dt)
          return $ TyConAppTC typeName formals
        other -> tcFails [text $ "Typecheck.generateTypeSchemaForDataType: Too many or"
                            ++ " too few definitions for $" ++ typeName
                            ++ "\n\t" ++ show (pretty other)]

    extractPatternBindings :: Pattern t -> [TypedId t]
    extractPatternBindings (P_Atom (P_Wildcard    {})) = []
    extractPatternBindings (P_Atom (P_Bool        {})) = []
    extractPatternBindings (P_Atom (P_Int         {})) = []
    extractPatternBindings (P_Atom (P_Variable _ tid)) = [tid]
    extractPatternBindings (P_Ctor _ _ ps _)  = concatMap extractPatternBindings ps
    extractPatternBindings (P_Tuple _ _ ps)   = concatMap extractPatternBindings ps

    checkSuspiciousPatternVariable rng var =
      if T.unpack (evarName var) `elem` ["true", "false"]
       then tcFails [text $ "Error: this matches a variable, not a boolean constant!"
                      ++ highlightFirstLine rng]
       else return ()
-- }}}

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

subsCheckTy :: SigmaTC -> SigmaTC -> String -> Tc ()
-- {{{
subsCheckTy sigma1 sigma2@(ForAllTC {}) msg = do
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

instance Show (AnnExpr TypeTC) where show e = show (pretty e)

subsCheckRhoTy :: SigmaTC -> RhoTC -> Tc ()
subsCheckRhoTy (ForAllTC ktvs rho) rho2 = do -- Rule SPEC
             taus <- genTauUnificationVarsLike ktvs (\n -> "instSigma type parameter " ++ show n)
             rho1 <- instSigmaWith ktvs rho taus
             subsCheckRhoTy rho1 rho2
subsCheckRhoTy rho1 (FnTypeTC as2 r2 cc2 ft2) = unifyFun rho1 (length as2) "subsCheckRhoTy" >>= \(as1, r1, cc1, ft1) -> subsCheckFunTy as1 r1 cc1 ft1 as2 r2 cc2 ft2
subsCheckRhoTy (FnTypeTC as1 r1 cc1 ft1) rho2 = unifyFun rho2 (length as1) "subsCheckRhoTy" >>= \(as2, r2, cc2, ft2) -> subsCheckFunTy as1 r1 cc1 ft1 as2 r2 cc2 ft2
subsCheckRhoTy tau1 tau2 -- Rule MONO
     = do
          logged' ("subsCheckRhoTy " ++ show (pretty (tau1, tau2))) $ unify tau1 tau2 "subsCheckRho" -- Revert to ordinary unification
-- }}}

subsCheck :: (AnnExpr SigmaTC) -> SigmaTC -> String -> Tc (AnnExpr SigmaTC)
-- {{{
subsCheck esigma sigma2@(ForAllTC {}) msg = do
  (skols, rho) <- skolemize sigma2
  debug $ "subsCheck skolemized sigma to " ++ show rho ++ " via " ++ show skols
                                            ++ ", now deferring to subsCheckRho"
  _ <- subsCheckRho esigma rho
  esc_tvs <- getFreeTyVars [typeTC esigma, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skols
  sanityCheck (null bad_tvs) ("subsCheck(" ++ msg ++ "): Type\n" ++ show (typeTC esigma) ++
                       " not as polymorphic as\n" ++ show sigma2 ++
                       "\nbad type variables: " ++ show bad_tvs)
  return esigma

subsCheck _esigma _rho2 _msg = tcFails [text $ "rho passed to subsCheck!"]

subsCheckRho :: AnnExpr SigmaTC -> RhoTC -> Tc (AnnExpr RhoTC)
subsCheckRho esigma rho2 = do
  case (typeTC esigma, rho2) of
    (_, ForAllTC {}) -> do tcFails [text $ "violated invariant: sigma passed to subsCheckRho"]
    (ForAllTC {}, _) -> do -- Rule SPEC
        debug $ "subsCheckRho instantiating " ++ show (typeTC esigma)
        erho <- inst esigma "subsCheckRho"
        debug $ "subsCheckRho instantiated to " ++ show (typeTC erho)
        debug $ "subsCheckRho inst. type against " ++ show rho2
        subsCheckRho erho rho2

    (rho1, FnTypeTC as2 r2 cc2 ft2) -> do debug $ "subsCheckRho fn 1"
                                          (as1, r1, cc1, ft1) <- unifyFun rho1 (length as2) "sCR1"
                                          subsCheckFunTy as1 r1 cc1 ft1 as2 r2 cc2 ft2
                                          return esigma
    (FnTypeTC as1 r1 cc1 ft1, _)    -> do debug "subsCheckRho fn 2"
                                          (as2, r2, cc2, ft2) <- unifyFun rho2 (length as1) "sCR2"
                                          debug $ "&&&&&& r1: " ++ show r1
                                          debug $ "&&&&&& r2: " ++ show r2
                                          subsCheckFunTy as1 r1 cc1 ft1 as2 r2 cc2 ft2
                                          return esigma
    -- Elide the two FUN rules and subsCheckFun because we're using
    -- shallow, not deep, skolemization due to being a strict language.

    (rho1, _) -> do -- Rule MONO
        logged esigma ("subsCheckRho " ++ show (pretty (rho1, rho2))) $ unify rho1 rho2 ("subsCheckRho[" ++ show rho2 ++ "]" ++ show (showStructure esigma)) -- Revert to ordinary unification
        return esigma
-- }}}

-- {{{ Helper functions for subsCheckRho to peek inside type constructors
subsCheckFunTy as1 r1 cc1 ft1 as2 r2 cc2 ft2 = do
        if eqLen as1 as2
          then return ()
          else do msg <- getStructureContextMessage
                  tcFailsMore [text "Function types must have equal-length argument lists"
                              ,msg]
        debug $ "subsCheckFunTy arg: " ++ show as2 ++ " ?<=? " ++ show as1
        mapM_ (\(a2, a1) -> subsCheckTy a2 a1 "sCFTa") (zip as2 as1)
        debug $ "subsCheckFunTy res: " ++ show r1 ++ " ?<=? " ++ show r2
        subsCheckTy r1 r2 "sCFTr"
        tcUnifyCC cc1 cc2
        tcUnifyFT ft1 ft2
        return ()
-- }}}

instSigma :: AnnExpr SigmaTC -> Expected RhoTC -> Tc (AnnExpr RhoTC)
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
instSigma e1 (Check t2) = do {
                             ; debug $ "instSigma " ++ show (typeTC e1) ++ " :?: " ++ show t2
                             ; debug $ "instSigma deferring to subsCheckRho"
                             ; subsCheckRho e1 t2
                             }
instSigma e1 (Infer r)  = do { e <- inst e1 "instSigma"
                             ; debug $ "instSigma " ++ show (typeTC e1) ++ " -inst-> " ++ show (typeTC e)
                             ; tcLift $ writeIORef r (typeTC e)
                             ; return e }

inst :: AnnExpr SigmaTC -> String -> Tc (AnnExpr RhoTC)
-- Transform a Sigma type into a Rho type by instantiating the ForAll's
-- type parameters with unification variables.
-- {{{
inst base msg = do
  --zonked <- shallowZonk (typeTC base)
  zonked <- return (typeTC base)
  case zonked of
     ForAllTC ktvs _rho -> do
       taus <- genTauUnificationVarsLike ktvs (\n -> "inst("++msg++") type parameter " ++ vname base n)
       instWith (annExprAnnot base) base taus
     _rho -> return base

instWith :: ExprAnnot -> AnnExpr SigmaTC -> [TauTC] -> Tc (AnnExpr RhoTC)
instWith _          aexpSigma [] = do
        sanityCheck (isRho $ typeTC aexpSigma)
                     "Tried to instantiate a sigma with no types!"
        return aexpSigma

instWith rng aexpSigma taus = do
    instRho <- tryInstSigmaWith (typeTC aexpSigma) taus
    return $ E_AnnTyApp rng instRho aexpSigma taus

tryInstSigmaWith sigma taus = do
  --zonked <- shallowZonk sigma
  zonked <- return sigma
  case zonked of
     ForAllTC ktvs rho -> instSigmaWith ktvs rho taus
     rho               -> return rho

instSigmaWith ktvs rho taus = do
    sanityCheck (eqLen taus ktvs)
                ("Arity mismatch in instSigma: can't instantiate"
                ++ show (List.length ktvs) ++ " type variables with "
                ++ show (List.length taus) ++ " types!")
    let tyvarsAndTys = List.zip (tyvarsOf ktvs) taus
    zonked <- zonkType rho -- Do a deep zonk to ensure we don't miss any vars.
    return $ parSubstTcTy tyvarsAndTys zonked
-- }}}

-- {{{
resolveType :: ExprAnnot -> Map String TypeTC -> TypeTC -> Tc TypeTC
resolveType annot origSubst origType = go origSubst origType where
 go subst x =
  let q x = go subst x in
  case x of
    PrimIntTC   _                  -> return x
    PrimFloat64TC                  -> return x
    MetaTyVarTC   _                -> return x
    TyVarTC  (SkolemTyVar _ _ _)   -> return x
    TyVarTC  (BoundTyVar name)     -> case Map.lookup name subst of
                                         Nothing -> tcFails [text $ "Typecheck.hs: ill-formed type with free bound variable " ++ name
                                                            ,text "    " <> text "embedded within type " <> pretty origType
                                                            ,text "    " <> text "with orig subst " <> pretty (Map.toList origSubst)
                                                            ,text $ highlightFirstLine (rangeOf annot)]
                                         Just ty -> return ty
    RefTypeTC     ty               -> liftM  RefTypeTC    (q ty)
    ArrayTypeTC   ty               -> liftM  ArrayTypeTC  (q ty)
    FnTypeTC    ss t cc cs         -> do (t':ss') <- mapM q (t:ss)
                                         return $ FnTypeTC  ss' t' cc cs
    CoroTypeTC   s t               -> liftM2 CoroTypeTC  (q s) (q t)
    TyConAppTC    tc  types        -> liftM  (TyConAppTC  tc) (mapM q types)
    TupleTypeTC       types        -> liftM   TupleTypeTC     (mapM q types)
    RefinedTypeTC v e args -> do v' <- fmapM_TID q v
                                 return $ RefinedTypeTC v' e args
    ForAllTC      ktvs rho         -> liftM (ForAllTC  ktvs) (go subst' rho)
                                       where
                                        subst' = foldl' ins subst ktvs
                                        ins m (tv@(BoundTyVar nm), _k) = Map.insert nm (TyVarTC  tv) m
                                        ins _     (SkolemTyVar {}, _k) = error "ForAll bound a skolem!"

fmapM_TID f (TypedId t id) = do t' <- f t
                                return $ TypedId t' id
-- }}}

-- Turns a type like (forall t, T1 t -> T2 t) into (T1 ~s) -> (T2 ~s)
-- where ~s denotes a skolem type variable. Also returns the generated tyvars.
skolemize :: TypeTC -> Tc ([TyVar], RhoTC)
-- {{{
skolemize (ForAllTC ktvs rho) = do
     skolems <- mapM newTcSkolem ktvs
     let tyvarsAndTys = List.zip (tyvarsOf ktvs)
                                 (map TyVarTC skolems)
     return (skolems, parSubstTcTy tyvarsAndTys rho)
skolemize ty = return ([], ty)
-- }}}

getFreeTyVars :: [TypeTC] -> Tc [TyVar]
-- {{{
getFreeTyVars xs = do zs <- mapM zonkType xs
                      return $ Set.toList (Set.fromList $ concatMap (go []) zs)
                 where
  go :: [TyVar] -> SigmaTC -> [TyVar]
  go bound x =
    case x of
        PrimIntTC         {} -> []
        PrimFloat64TC     {} -> []
        TyConAppTC _nm types     -> concatMap (go bound) types
        TupleTypeTC types        -> concatMap (go bound) types
        FnTypeTC ss r   _ _      -> concatMap (go bound) (r:ss)
        CoroTypeTC s r           -> concatMap (go bound) [s,r]
        ForAllTC  tvs rho        -> go (tyvarsOf tvs ++ bound) rho
        TyVarTC   tv             -> if tv `elem` bound then [] else [tv]
        MetaTyVarTC  {}          -> []
        RefTypeTC    ty          -> (go bound) ty
        ArrayTypeTC  ty          -> (go bound) ty
        RefinedTypeTC v _e _args -> (go bound) (tidType v) -- TODO handle tyvars in expr/args?
-- }}}

unMBS :: MetaBindStatus -> TypeTC
unMBS (NonMeta t) = t
unMBS (MetaUnbound m  ) = MetaTyVarTC m
unMBS (MetaBoundTo _ t) = t

instance Pretty MetaBindStatus where pretty mbs = string (show mbs)

data MetaBindStatus = NonMeta TypeTC
                    | MetaUnbound (MetaTyVar TypeTC)
                    | MetaBoundTo (MetaTyVar TypeTC) TypeTC
                    deriving Show

shZonkType :: TypeTC -> Tc MetaBindStatus
shZonkType x = do
    case x of
        MetaTyVarTC m -> do shZonkMetaType m
        _ -> return (NonMeta x)

shZonkMetaType m = do
  mty <- readTcMeta m
  case mty of
    Nothing -> do return $ MetaUnbound m
    Just ty -> do return $ MetaBoundTo m ty

-- As in the paper, zonking recursively eliminates indirections
-- from instantiated meta type variables.
zonkType :: TypeTC -> Tc TypeTC
-- {{{
zonkType x = do
    case x of
        MetaTyVarTC m -> do mty <- readTcMeta m
                            case mty of
                              Nothing -> do debugDoc $ string "unable to zonk meta " <> pretty x
                                            return x
                              Just ty -> do ty' <- zonkType ty >>= return
                                            writeTcMetaTC m ty'
                                            return ty'
        PrimIntTC     {}        -> return x
        PrimFloat64TC {}        -> return x
        TyVarTC       {}        -> return x
        TyConAppTC  nm types    -> liftM  (TyConAppTC nm) (mapM zonkType types)
        TupleTypeTC    types    -> liftM  (TupleTypeTC  ) (mapM zonkType types)
        ForAllTC    tvs  rho    -> liftM  (ForAllTC tvs ) (zonkType rho)
        RefTypeTC       ty      -> liftM  (RefTypeTC    ) (zonkType ty)
        ArrayTypeTC     ty      -> do debug $ "zonking array ty: " ++ show ty
                                      liftM (ArrayTypeTC  ) (zonkType ty)
        CoroTypeTC s r          -> liftM2 (CoroTypeTC  ) (zonkType s) (zonkType r)
        RefinedTypeTC (TypedId ty id) e __args   -> liftM (\t -> RefinedTypeTC (TypedId t id) e __args) (zonkType ty)
        FnTypeTC ss r   cc cs   -> do ss' <- mapM zonkType ss ; r' <- zonkType r
                                      return $ FnTypeTC ss' r' cc cs
-- }}}

-- Sad hack:
-- Given code like
--    poly2b :: forall b:Boxed, { { b => Int32 } => Int32 };
--    poly2b = { forall b:Boxed, tmp : ?? T => 0 };
-- we want to "unify" ??T with { b => Int32 },
-- but we can't literally unify because then we'd fail on code like
--    poly2b :: forall b:Boxed, { { b => Int32 } => Int32 };
--    poly2b = { forall b:Boxed, tmp : { b => Int32 } => 0 };
-- when we would try to unify the bound type variable b with itself.
-- Also, for code like
--    poly2b :: forall b:Boxed, { b => Int32 };
--    poly2b = { forall b:Boxed, tmp :?? T => 0 };
-- ... SADFACE
checkAgainst taus (ety, MetaTyVarTC m) = do
  debugDoc $ string "checkAgainst ety: " <+> pretty ety
  debugDoc $ string "checkAgainst cty: " <+> pretty (MetaTyVarTC m)
  let tryOverwrite = do
        mty <- readTcMeta m
        case mty of
            Nothing -> do ty' <- zonkType ety
                          writeTcMetaTC m ty'
            Just  _ -> do return ()

  case ety of
    MetaTyVarTC em | em `elem` taus -> do
        ty' <- zonkType ety
        debugDoc $ string "checkAgainst: ety ~> " <+> pretty ty'
        --tryOverwrite
        return ()
    _ -> tryOverwrite
checkAgainst _ (_, _) = return ()

-- {{{ Unification driver
-- If unification fails, the provided error message (if any)
-- is printed along with the unification failure error message.
-- If unification succeeds, each unification variable in the two
-- types is updated according to the unification solution.
unify :: TypeTC -> TypeTC -> String -> Tc ()
unify t1 t2 msg = do
  --z1 <- zonkType t1
  --z2 <- zonkType t2
  --tcLift $ putDocLn $ green $ text $ "unify " ++ show t1 ++ " ~> " ++ show z1
  --                               ++ "\n?==? " ++ show t2 ++ " ~> " ++ show z2 ++ " (" ++ msg ++ ")"
  unify' 0 t1 t2 msg

unify' !depth t1 t2 msg | depth == 512 =
   error $ "unify hit depth 512 equating "
        ++ show t1 ++ " and " ++ show t2 ++ "\n" ++ msg

unify' !depth t1 t2 msg = do
  debugDoc $ green $ text $ "unify " ++ show t1 ++ " ?==? " ++ show t2 ++ " (" ++ msg ++ ")"
  case (t1, t2) of
    (MetaTyVarTC m1, MetaTyVarTC m2) -> do
      mt1 <- readTcMeta m1
      mt2 <- readTcMeta m2
      debugDoc $ text $ show t1 ++ " ~> " ++ show mt1
      debugDoc $ text $ show t2 ++ " ~> " ++ show mt2
      return ()
    _ -> return ()

  tcOnError (liftM text (Just msg)) (tcUnifyTypes t1 t2) $ \(Just soln) -> do
     debugDoc $ text $ "soln is: " ++ show soln
     let univars = collectAllUnificationVars [t1, t2]
     forM_ univars $ \m -> do
       mt1 <- readTcMeta m
       case (mt1, Map.lookup (mtvUniq m) soln) of
         (_,       Nothing)          -> return () -- no type to update to.
         (Just x1, Just x2)          -> do unify' (depth + 1) x1 x2 msg
         -- The unification var m1 has no bound type, but it's being
         -- associated with var m2, so we'll peek through m2.
         (Nothing, Just (MetaTyVarTC m2)) -> do
                         mt2 <- readTcMeta m2
                         case mt2 of
                             Just x2 -> do debugDoc $ pretty (MetaTyVarTC m2) <+> text "~>" <+> pretty x2
                                           unify' (depth + 1) (MetaTyVarTC m) x2 msg
                             Nothing -> writeTcMetaTC m (MetaTyVarTC m2)
         (Nothing, Just x2) -> do unbounds <- collectUnboundUnificationVars [x2]
                                  case m `elem` unbounds of
                                     False   -> writeTcMetaTC m x2
                                     True    -> occurdCheck   m x2
  where
     occurdCheck m t = tcFails [text $ "Occurs check for " ++ show (MetaTyVarTC m)
                                   ++ " failed in " ++ show t
                               ,string msg]
-- }}}

-- {{{ Well-formedness checks
-- The judgement   G |- T
tcTypeWellFormed :: String -> Context SigmaTC -> TypeTC -> Tc ()
tcTypeWellFormed msg ctx typ = do
  let q = tcTypeWellFormed msg ctx
  case typ of
        PrimIntTC      {}     -> return ()
        PrimFloat64TC  {}     -> return ()
        MetaTyVarTC    {}     -> return ()
        TyConAppTC  nm types  ->
                            case Map.lookup nm (contextDataTypes ctx) of
                                   Just  _ -> mapM_ q types
                                   Nothing -> tcFails [text $ "Unknown type "
                                                        ++ nm ++ " " ++ msg]
        TupleTypeTC types     -> mapM_ q types
        FnTypeTC  ss r   _ _  -> mapM_ q (r:ss)
        CoroTypeTC  s r       -> mapM_ q [s,r]
        RefTypeTC     ty      -> q ty
        ArrayTypeTC   ty      -> q ty
        RefinedTypeTC v _e  _ -> q (tidType v)
        ForAllTC   tvs rho    -> tcTypeWellFormed msg (extendTyCtx ctx tvs) rho
        TyVarTC  (SkolemTyVar {}) -> return ()
        TyVarTC  tv@(BoundTyVar _) ->
                 case Prelude.lookup tv (contextTypeBindings ctx) of
                   Nothing -> tcFails [text $ "Unbound type variable "
                                           ++ show tv ++ " " ++ msg]
                   Just  _ -> return ()

tcContainsRefinements :: TypeTC -> Bool
tcContainsRefinements typ =
  case typ of
        RefinedTypeTC {} -> True
        PrimIntTC      {}      -> False
        PrimFloat64TC  {}      -> False
        MetaTyVarTC    {}      -> False
        TyConAppTC _nm tys     -> any tcContainsRefinements tys
        TupleTypeTC    tys     -> any tcContainsRefinements tys
        FnTypeTC   ss r   _ _  -> any tcContainsRefinements (r:ss)
        CoroTypeTC  s r        -> any tcContainsRefinements [s,r]
        RefTypeTC     ty       -> tcContainsRefinements ty
        ArrayTypeTC   ty       -> tcContainsRefinements ty
        ForAllTC  _tvs rho     -> tcContainsRefinements rho
        TyVarTC  (SkolemTyVar {})   -> False
        TyVarTC  _tv@(BoundTyVar _) -> False -- or do we need to look at the context?

tcContext :: Context TypeTC -> Context TypeAST -> Tc (Context SigmaTC)
tcContext emptyCtx ctxAST = do
  sanityCheck (Map.null $ localTypeBindings ctxAST)
        "Expected to start typechecking with an empty lexical type environment"
  sanityCheck (null $ contextTypeBindings ctxAST)
        "Expected to start typechecking with an empty lexical type environment"

  debug2 "converting Context TypeAST to Context TypeTC"
  debug2 (show ctxAST)
  ctx <- liftContextM (tcType emptyCtx) ctxAST
  debug2 "done converting Context TypeAST to Context TypeTC"

  -- For now, we disallow mutually recursive data types
  let checkDataType :: (String, [DataType TypeTC]) -> Tc ()
      checkDataType (nm,dts) = do {
    case dts of
      [dt] -> do
         sanityCheck (nm == typeFormalName (dataTypeName dt)) ("Data type name mismatch for " ++ nm)
         let tyformals = dataTypeTyFormals dt
         let extctx = extendTyCtx ctx (map convertTyFormal tyformals)
         case detectDuplicates (map dataCtorName (dataTypeCtors dt)) of
           []   -> mapM_ (tcDataCtor nm extctx) (dataTypeCtors dt)
           dups -> tcFails [text $ "Duplicate constructor names " ++ show dups
                                ++ " in definition of data type " ++ nm]
      _ -> tcFails [text $ "Data type name " ++ nm
                       ++ " didn't map to a single data type!"]
  }

  mapM_ checkDataType (Map.toList $ contextDataTypes ctx)

  return ctx


tcDataCtor :: String -> Context SigmaTC -> DataCtor TypeTC -> Tc ()
tcDataCtor dtname ctx (DataCtor nm _tyfs tys _rng) = do
  let msg = "in field of data constructor " ++ T.unpack nm ++ " of type " ++ dtname
  mapM_ (tcTypeWellFormed msg ctx) tys
-- }}}

-- {{{ Miscellaneous helpers.


collectUnboundUnificationVars :: [TypeTC] -> Tc [MetaTyVar TypeTC]
collectUnboundUnificationVars xs = do
  xs' <- mapM zonkType xs
  return $ [m | m <- collectAllUnificationVars xs' , not $ isForIntLit m]
    where isForIntLit m = mtvDesc m == "int-lit"

collectAllUnificationVars :: [TypeTC] -> [MetaTyVar TypeTC]
collectAllUnificationVars xs = Set.toList (Set.fromList (concatMap go xs))
  where go x =
          case x of
            PrimIntTC  _            -> []
            PrimFloat64TC           -> []
            TyConAppTC  _nm types   -> concatMap go types
            TupleTypeTC  types      -> concatMap go types
            FnTypeTC  ss r   _ _    -> concatMap go (r:ss)
            CoroTypeTC  s r         -> concatMap go [s,r]
            ForAllTC  _tvs rho      -> go rho
            TyVarTC   _tv           -> []
            MetaTyVarTC   m         -> [m]
            RefTypeTC     ty        -> go ty
            ArrayTypeTC   ty        -> go ty
            RefinedTypeTC v _ _     -> go (tidType v)

vname (E_AnnVar _rng (av, _)) n = show n ++ " for " ++ T.unpack (identPrefix $ tidIdent av)
vname _                       n = show n

varbind id ty = TermVarBinding (identPrefix id) (TypedId ty id, Nothing)
bindingForVar (TypedId ty id) = varbind id ty

genTauUnificationVarsLike :: [a] -> (Int -> String) -> Tc [TypeTC]
genTauUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVarTau (namegen n) | (_, n) <- zip spine [1..]]

  {-
genSigmaUnificationVarsLike :: [a] -> (Int -> String) -> Tc [TypeAST]
genSigmaUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVarSigma (namegen n) | (_, n) <- zip spine [1..]]
-}

genUnifiableVar = do
  u <- newTcUniq
  r <- tcLift $ fresh Nothing
  return $ UniVar (u, r)

bindingName :: ContextBinding ty -> T.Text
bindingName (TermVarBinding nm _) = nm

verifyNamesAreDistinct :: SourceRange -> String -> [T.Text] -> Tc ()
verifyNamesAreDistinct rng name names = do
    case detectDuplicates names of
        []   -> return ()
        dups -> tcFails [text $ "Error when checking " ++ name ++ ": "
                              ++ "had duplicated bindings: " ++ show dups
                              ++ highlightFirstLine rng]

verifyNonOverlappingBindings :: SourceRange -> String -> [ContextBinding ty] -> Tc ()
verifyNonOverlappingBindings rng name binders = do
    verifyNamesAreDistinct rng name (map bindingName binders)

tyvarsOf ktyvars = map (\(tv,_k) -> tv) ktyvars

isRho (ForAllTC _ _) = False
isRho _              = True

instance Show a => Show (Expected a) where
  show (Infer _) = "<infer>"
  show (Check a) = show a

instance Pretty a => Pretty (Expected a) where
  pretty (Infer _) = text "<infer>"
  pretty (Check a) = pretty a

instance Pretty ty => Pretty (CtorInfo ty) where
  pretty (CtorInfo cid dc) = parens (text "CtorInfo" <+> text (show cid) <+> pretty dc)

instance Pretty ty => Pretty (DataCtor ty) where
  pretty (DataCtor name _tyformals _ctortyargs _range) =
        parens (text "DataCtor" <+> text (T.unpack name))

instance Pretty ty => Pretty (DataType ty) where
  pretty (DataType name tyformals dctors _range) =
        text "type case " <> pretty name <+> hsep (map pretty tyformals)
                <$> vsep (map pretty dctors)

instance Pretty TypeFormal where
  pretty (TypeFormal name kind) = text name <> text " :: " <> pretty kind

retypeTID :: (t1 -> Tc t2) -> TypedId t1 -> Tc (TypedId t2)
retypeTID f (TypedId t1 id) = f t1 >>= \t2 -> return (TypedId t2 id)

eqLen a b = List.length a == List.length b

getEnvTypes ctx = return (map ctxBinderType $ Map.elems (contextBindings ctx))
  where ctxBinderType (tid, _) = tidType tid

expMaybe (Infer _) = Nothing
expMaybe (Check t) = Just t

update r e_action = do e <- e_action
                       tcLift $ writeIORef r (typeTC e)
                       return e

type Term = ExprAST TypeAST

tcVERBOSE = False

debug    s = do when tcVERBOSE (tcLift $ putStrLn s)
debug2   s = do when tcVERBOSE (tcLift $ putStrLn s)
debugDoc d = do when tcVERBOSE (tcLift $ putDocLn d)
debugDoc2 d = do when tcVERBOSE (tcLift $ putDocLn d)
debugDoc3 d = do when tcVERBOSE (tcLift $ putDocLn d)

-- The free-variable determination logic here is tested in
--      test/bootstrap/testcases/rec-fn-detection
instance Expr (ExprAST TypeAST) where
  freeVars e = case e of
    E_LetAST _rng (TermBinding v b) e ->
                                freeVars b ++ (freeVars e `butnot` [evarName v])
    E_LetRec _rng nest _ -> concatMap freeVars (childrenOf e) `butnot`
                                          [evarName v | TermBinding v _ <- nest]
    E_Case _rng e arms   -> freeVars e ++ (concatMap caseArmFreeVars arms)
    E_FnAST _rng f       -> let bodyvars  = freeVars (fnAstBody f) in
                            let boundvars = map (identPrefix.tidIdent) (fnFormals f) in
                            bodyvars `butnot` boundvars
    E_VarAST _rng v      -> [evarName v]
    _                    -> concatMap freeVars (childrenOf e)

freeVarsMb Nothing  = []
freeVarsMb (Just e) = freeVars e

caseArmFreeVars (CaseArm epat body guard _ _) =
  (freeVars body ++ freeVarsMb guard) `butnot` epatBoundNames epat
  where epatBoundNames :: EPattern ty -> [T.Text]
        epatBoundNames epat =
          case epat of
            EP_Wildcard {}        -> []
            EP_Variable _rng evar -> [evarName evar]
            EP_Ctor     {}        -> []
            EP_Bool     {}        -> []
            EP_Int      {}        -> []
            EP_Tuple    _rng pats -> concatMap epatBoundNames pats

typeTC :: AnnExpr TypeTC -> TypeTC
typeTC = typeOf

logged'' msg action = do
  --tcLift $ putStrLn $ "{ " ++ msg
  rv <- action
  --tcLift $ putStrLn $ "} :: " ++ show (pretty $ typeTC rv)
  return rv

logged' msg action = do
  --tcLift $ putStrLn $ "{ " ++ msg
  rv <- action
  --tcLift $ putStrLn $ "}"
  return rv

logged expr msg action = do
  --tcLift $ putStrLn $ "{ " ++ msg
  rv <- action
  --tcLift $ putStrLn $ "} :: " ++ show (pretty $ typeTC expr)
  return rv
-- }}}
