{-# LANGUAGE Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.Typecheck(tcSigmaToplevel, tcSigmaToplevelNonFn, tcTypeWellFormed,
                        tcContext, tcType, fnTypeShallow, mkLevels,
                        tcReplaceQuantifiedVars) where

import Prelude hiding ((<$>))

import qualified Data.List as List(length, zip, elem, lookup, foldl1')
import Data.List(foldl', (\\))
import Control.Monad(liftM, forM, liftM, liftM2, when)

import qualified Data.Text as T(Text, pack, unpack, length, head, append)
import Data.Map(Map)
import qualified Data.Map as Map(lookup, insert, keys, elems, fromList, toList, null)
import qualified Data.Set as Set(toList, fromList, intersection, difference)
import Data.Sequence(Seq)
import qualified Data.Sequence as Seq
import Data.Maybe (fromMaybe)
import Data.IORef(readIORef,writeIORef)
import Data.UnionFind.IO(fresh)
import Data.Foldable(toList)

import Foster.Base
import Foster.BaseUtils
import Foster.Kind
import Foster.TypeAST
import Foster.TypeTC
import Foster.ExprAST
import Foster.AnnExpr
import Foster.Infer
import Foster.Context
import Foster.TypecheckInt(typecheckInt, typecheckRat)
import Foster.Output(OutputOr(Errors, OK), putDocLn)
import Foster.PrettyAnnExpr()
import Foster.SourceRange(SourceRange(..), rangeOf,
          highlightFirstLineStr, highlightFirstLineDoc, prettySourceRangeInfo, showSourceRangeStr, prettyWithLineNumbers)

import Data.Text.Prettyprint.Doc

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
--   * To force an expression to be typechecked in pure (rho) inference mode,
--     try the following construct: case INFER of _ -> ... end.
--
--   * For inferSigma, use (prim __COMPILES__ INFER) or { x = INFER; ... }
--
--   * To force an expression to be checked against a meta type variable,
--     the easiest approach is to use a reference store operation: METATY >^ r.
--
--   * To force an expression to be checked against a particular type,
--     write { f : { T => () }   =>   f EXPR }
--     or just do    (EXPR as T)
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
--   * inferSigma called by
--        tcRhoLet (let/rec-bindings without type annotations)
--        tcRhoTyApp
--        tcCompiles
--        tc*FnHelper (Infer, or Check of a rho type)
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

tcSigmaToplevelNonFn :: Context TypeTC -> Term -> Tc (AnnExpr SigmaTC)
tcSigmaToplevelNonFn ctx ast = do
  inferSigma ctx ast "tcSigmaToplevel"

tcSigmaToplevel :: ContextBinding TypeTC -> Context TypeTC -> Term -> Tc (AnnExpr SigmaTC)
tcSigmaToplevel (TermVarBinding _txt (tid, _)) ctx ast = do
-- {{{
    -- Make sure the (potentially user-supplied) type annotation is well-formed.
    {- TODO
    tcTypeWellFormed ("in the type declaration for " ++ T.unpack txt)
                     ctx (tidType tid)
                     -}

    debugDoc $ text "tcSigmaToplevel deferring to checkSigmaDirect with expected type"
            <$> (prettyT (tidType tid)) <> line
    e <- checkSigmaDirect ctx ast (tidType tid)
    debugDoc $ text "tcSigmaToplevel returned expression with type " <> prettyT (typeTC e)

    return e
-- }}}

inferSigma :: Context SigmaTC -> Term -> String -> Tc (AnnExpr SigmaTC)
-- {{{
inferSigma ctx e msg = do
  e' <- inferSigmaHelper ctx e msg
  shouldDoQuant <- tcShouldQuantify
  if shouldDoQuant
    then doQuantification e' ctx
    else return e'

inferSigmaHelper :: Context SigmaTC -> Term -> String -> Tc (AnnExpr SigmaTC)
inferSigmaHelper ctx (E_TyCheck annot e ta) _msg = do
    ty <- tcTypeAndResolve ctx ta annot
    checkSigma ctx e ty
-- Special-case variables and function literals
-- to avoid a redundant instantation + generalization
inferSigmaHelper ctx (E_VarAST rng v) _msg = tcSigmaVar ctx rng (evarName v)
inferSigmaHelper ctx (E_FnAST _rng f)  msg = do r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                                                tcSigmaFn  ctx f (Infer r)
inferSigmaHelper ctx (E_CallAST   rng base argtup ca) msg = do
                r <- newTcRef (error $ "inferSigmaFn: empty result: " ++ msg)
                tcSigmaCall     ctx rng   base argtup ca (Infer r)
inferSigmaHelper ctx e msg = do
    debugIf dbgSigma $ string "inferSigmaHelper " <> highlightFirstLineDoc (rangeOf e)
    debugIf dbgSigma $ showStructure e
    debugIf dbgSigma $ string $  "inferSigmaHelper deferring to inferRho"
    inferRho ctx e msg
-- }}}

checkSigma :: Context SigmaTC -> Term -> SigmaTC -> Tc (AnnExpr SigmaTC)
-- {{{
checkSigma ctx (E_FnAST _ f) sigma = tcSigmaFn ctx f (Check sigma)
checkSigma ctx e sigma = do
    (skol_tvs, rho) <- skolemize sigma
    if not (null skol_tvs)
      then do
        debugIf dbgSigma $ string "checkSigma " <> highlightFirstLineDoc (rangeOf e) <> string (" :: " ++ show sigma)
        debugIf dbgSigma $ string $ "checkSigma used " ++ show skol_tvs ++ " to skolemize " ++ show sigma ++ " to " ++ show rho
        debugIf dbgSigma $ string "checkSigma deferring to checkRho for: " <> highlightFirstLineDoc (rangeOf e)
      else return ()

    ann <- checkRho ctx e rho
    checkForEscapingTypeVariables e ann ctx sigma skol_tvs
    return ann
-- }}}

instance (Show ty) => Show (TVar ty) where
  show (Unbound lvl) = "Unbound:" ++ show lvl
  show (BoundTo ty ) = "BoundTo:" ++ show ty

-- {{{
doQuantification :: AnnExpr SigmaTC -> Context SigmaTC -> Tc (AnnExpr SigmaTC)
doQuantification e' ctx = do
    let t = typeTC e'

    -- OCaml generalizes types without needing to scan the environment:
    --    http://okmij.org/ftp/ML/generalization.html
    -- We should eventually do the same.
    -- Without such tricks, quantification is O(n^2).
    env_tys <- getEnvTypes ctx
    env_tvs <- collectUnboundUnificationVars env_tys
    res_tvs <- collectUnboundUnificationVars [t]
    let forall_tvs = res_tvs \\ env_tvs
    debugIf dbgQuant $ text "{{{{"
    debugIf dbgQuant $ text "doQuantificationCheck: e' = " <$$> indent 4 (showStructure e')
    debugIf dbgQuant $ prettyT t
    t' <- zonkType t
    debugIf dbgQuant $ text "zonked: " <$> prettyT t'
    debugIf dbgQuant $ text "inferSigma inferred :: " <> prettyT t
    debugIf dbgQuant $ text "non-effect tvs: " <> (prettyT $ map show [tv | tv <- forall_tvs, not (mtvIsEffect tv)])
    debugIf dbgQuant $ text "effect tvs: " <> (prettyT $ map show [tv | tv <- forall_tvs, (mtvIsEffect tv)])

    forall_tys <- mapM readTcMeta forall_tvs
    debugIf dbgQuant $ text "env_typs"   <$> indent 2 (vcat $ map prettyT env_tys)
    debugIf dbgQuant $ text "env_tyvars" <$> indent 2 (vcat $ map prettyT env_tvs)
    debugIf dbgQuant $ text "res_tyvars" <$> indent 2 (vcat $ map prettyT res_tvs)
    debugIf dbgQuant $ text "forall_tys" <$> indent 2 (vcat $ map prettyT forall_tys)
    debugIf dbgQuant $ text "}}}}}"
    let nonfx_forall_tvs = [tv | tv <- forall_tvs, not (mtvIsEffect tv)]
    let    fx_forall_tvs = [tv | tv <- forall_tvs,     (mtvIsEffect tv)]
    case () of
      _ | not (isValue e') -> return e' -- Don't generalize over non-values...
      _ | not (null nonfx_forall_tvs) -> do
         tcWarn [text "the expression"
                , indent 4 (highlightFirstLineDoc (rangeOf e'))
                , indent 2 (text "is being given a type involving meta type variables,"
                          <$> text "not an implicitly-generalized polymorphic type"
                          <+> text "(as might be expected in ML or Haskell).")]
         return e'
      _ | null fx_forall_tvs -> return e'
      _ -> do -- generalize over escaping effect meta type variables
        let newBinderNames = take (length fx_forall_tvs) (allBinderNames \\ tyVarBinders t )
            newBinders = map (\strName -> BoundTyVar strName rng) newBinderNames
            rng  = rangeOf (annExprAnnot e')
        let writeTv (mtv, tv) = writeTcMeta mtv (TyVarTC tv (UniConst KindEffect))
        mapM_ writeTv (zip fx_forall_tvs newBinders)
        let sigma = quantifyOver [(tv, KindEffect) | tv <- newBinders] t
        return $ case e' of
          E_AnnVar annot (tid, mcid) -> E_AnnVar annot ((TypedId sigma (tidIdent tid)), mcid)
          E_AnnFn fn -> E_AnnFn fn { fnVar = TypedId sigma (fnIdent fn) }
          _          -> E_AnnTyApp (annExprAnnot e') sigma e' []

quantifyOver tyvars (ForAllTC existing rho) = ForAllTC (existing ++ tyvars) rho
quantifyOver tyvars rho = ForAllTC tyvars rho

-- a-z, then a1..z1, etc.
allBinderNames = let base = ['a'..'z'] in
                 map T.pack $ [ [x] | x <- base ] ++ [ (x : show i) | i <- [1..], x <- base ]

tyVarBinders :: TypeTC -> [T.Text]
tyVarBinders t = go [] t
  where go acc (ForAllTC ktvs rho) = go (map (binderName . fst) ktvs ++ acc) rho
        go acc t = foldl' go acc (childrenOf t)

        binderName (BoundTyVar s _) = s
        binderName (SkolemTyVar s _ _) = error $ "tyVarBinders.SKOLEM." ++ T.unpack s

isValue e = case e of
  AnnLiteral      {} -> True
  E_AnnFn         {} -> True
  AnnCompiles     {} -> True
  E_AnnTyApp _ _ a _ -> isValue a
  AnnAppCtor _ _ _ exprs -> all isValue exprs
  AnnRecord  _ _ _ exprs -> all isValue exprs
  AnnTuple   _ _ _ exprs -> all isValue exprs
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
         ++ highlightFirstLineStr (rangeOf e)
    if null bad_tvs
      then return ()
      else do tytc <- zonkType (typeTC _ann)
              tcFailsMore [text "Type not polymorphic enough",
                        indent 10 $ prettyT sigma,
                        text "when looking at expression",
                        highlightFirstLineDoc (rangeOf e),
                        text "with inferred type ",
                        indent 10 $ prettyT tytc,
                        text "escaping skolems:",
                        indent 10 $ pretty bad_tvs]
-- }}}


checkSigmaDirect :: Context SigmaTC -> Term -> SigmaTC -> Tc (AnnExpr SigmaTC)
-- {{{
checkSigmaDirect ctx expr@(E_FnAST _rng fn) sigma@(ForAllTC {}) = do
   tcWithScope expr $
      tcSigmaFn ctx fn (Check sigma)

checkSigmaDirect _ctx _ (ForAllTC {}) =
    tcFails [text "checkSigmaDirect: can't check a sigma type against an arbitrary expression"]

checkSigmaDirect ctx e rho = checkRho ctx e rho
-- }}}

checkRho :: Context SigmaTC -> Term -> RhoTC -> Tc (AnnExpr RhoTC)
-- Invariant: the Rho is always in weak-prenex form
-- {{{
checkRho ctx e ty = do
    debug $ "checkRho " ++ highlightFirstLineStr (rangeOf e) ++ " :: " ++ show ty
    debug $ "checkRho deferring to tcRho"
    tcRho ctx e (Check ty)
-- }}}

inferRho :: Context SigmaTC -> Term -> String -> Tc (AnnExpr RhoTC)
-- {{{
inferRho ctx e msg = do
    ref <- newTcRef (error $ "inferRho: empty result: " ++ msg)
    debug $ "inferRho " ++ highlightFirstLineStr (rangeOf e)
    debug $ "inferRho deferring to tcRho"
    a <- tcRho ctx e (Infer ref)
    a <- inst a "inferRho"
    debug $ "tcRho (" ++ msg ++") finished, reading inferred type from ref"
    debug $ "tcRho (" ++ msg ++"): " ++ highlightFirstLineStr (rangeOf e)
    ty <- tcLift $ readIORef ref
    debug $ "inferRho (" ++ msg ++")" ++ highlightFirstLineStr (rangeOf e) ++ " :: " ++ show ty
    debug $ "inferRho (" ++ msg ++")" ++ highlightFirstLineStr (rangeOf e) ++ " :: " ++ show (typeTC a)
    sanityCheck (isRho $ typeTC a) (T.pack $ "inferRho wound up with a sigma type!" ++ highlightFirstLineStr (rangeOf a))
    return a

-- }}}
tcRho :: Context SigmaTC -> Term -> Expected RhoTC -> Tc (AnnExpr RhoTC)
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
tcRho ctx expr expTy = do
 debugDoc2 $ green (text "typecheck: ") <> textOf expr 0 <> string (" <=? " ++ show expTy)
 logged'' (show $ textOf expr 0 ) $
  tcWithScope expr $ do
    case expr of
      E_VarAST    rng v              -> tcRhoVar      ctx rng (evarName v)      expTy
      E_CallPrimAST rng "inline-asm" [LitText s, LitText c, LitBool x] [ty] [] -> do
        ty' <- tcType ctx ty
        matchExp expTy (AnnPrimitive rng ty' (PrimInlineAsm ty' s c x)) "inline-asm"

      E_CallPrimAST rng "record-lookup" [LitText fieldName] [] [expr] ->
        tcRhoRecordLookup ctx rng expr fieldName expTy

      E_CallPrimAST rng nm [] [] args -> tcRhoCallPrim ctx rng nm args expTy
      E_CallPrimAST   {} -> tcFails [text "Typecheck saw unexpected primitive", string $ show expr]
      E_IntAST    rng txt ->  typecheckInt rng txt           expTy   >>= (\v -> matchExp expTy v "tcInt")
      E_RatAST    rng txt -> (typecheckRat rng txt (expMaybe expTy)) >>= (\v -> matchExp expTy v "tcRat")
      E_BoolAST   rng b              -> tcRhoBool         rng   b          expTy
      E_StringAST rng txtorbytes     -> tcRhoTextOrBytes  rng   txtorbytes expTy
      E_MachArrayLit rng mbt args    -> tcRhoArrayLit ctx rng   mbt args   expTy
      E_CallAST   rng base argtup ca -> tcRhoCall     ctx rng   base argtup ca expTy
      E_RecordAST rng labels exprs   -> tcRhoRecord   ctx rng   labels exprs expTy
      E_TupleAST  rng boxy exprs     -> tcRhoTuple    ctx rng   boxy exprs  expTy
      E_IfAST   rng a b c            -> tcRhoIf       ctx rng   a b c      expTy
      E_FnAST  _rng f                -> tcRhoFn       ctx       f          expTy
      E_LetRec rng bindings e        -> tcRhoLetRec   ctx rng   bindings e expTy
      E_LetAST rng binding  e        -> tcRhoLet      ctx rng   binding  e expTy
      E_TyApp  rng e types           -> tcRhoTyApp    ctx rng   e types    expTy
      E_TyCheck rng e ty             -> tcRhoTyCheck  ctx rng   e ty       expTy
      E_Handler rng e arms mb_xform  -> tcRhoHandler  ctx rng   e arms mb_xform expTy
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
      E_KillProcess rng (E_StringAST _ (SS_Text _ msg)) -> do
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
                       subsCheckRho ann t msg
         Infer r -> do update r (return ann)

-- First, an interesting pair of rules for variables:
--
--
--  G contains v ::: s             G has v as primitive
--  ------------------     or      -----------------------
--  G |- v ~~> v ::: s             G |- v ~~> prim v ::: s
-- {{{
tcSigmaVar :: Context SigmaTC -> ExprAnnot -> T.Text -> Tc (AnnExpr SigmaTC)
tcSigmaVar ctx annot name = do
  debugDoc $ green (text "typecheckVar (sigma): ") <> text name <> text "..."
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
         tcFails [string $ "Unknown variable " ++ T.unpack name
                 ,prettyWithLineNumbers (rangeOf annot)
                 ]
-- }}}

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
-- {{{
tcRhoVar ctx rng name expTy = do
     debugIf dbgVar $ green (text "typecheckVar (rho): exp_ty ") <> text name <> text " :?: " <> prettyT expTy
     v_sigma <- tcSigmaVar ctx rng name
     ann_var <- inst v_sigma ("tcRhoVar[" ++ T.unpack name ++ "]")
     debugIf dbgVar $ green (text "typecheckVar v_sigma: ") <> text name <> text " :: " <> prettyT (typeTC v_sigma)
     debugIf dbgVar $ green (text "typecheckVar ann_var: ") <> text name <> text " :: " <> prettyT (typeTC ann_var)
     matchExp expTy ann_var "var"


tcRhoCallPrim ctx rng name [arg] expTy | name == T.pack "log-type" = do
    e <- inferSigma ctx arg (T.unpack name)
    tcLift $ putDocLn $ yellow (text "inferred type of ") <> highlightFirstLineDoc (rangeOf arg) <$> text " is " <> blue (prettyT (typeTC e))
    do t' <- zonkType (typeTC e)
       tcLift $ putDocLn $ yellow (text "which zonks to ") <> prettyT t'
    matchExp expTy (AnnTuple rng unitTypeTC KindPointerSized []) (T.unpack name)

tcRhoCallPrim ctx rng name args expTy | name == T.pack "assert-invariants" = do
    levels <- mkLevels
    let mkFnTypeTC args ret = FnTypeTC args ret emptyEffectTC
                                      (UniConst FastCC) (UniConst FT_Func) levels

    args <- mapM (\arg -> checkSigma ctx arg boolTypeTC) args
    let fnty = mkFnTypeTC [boolTypeTC | _ <- args] unitTypeTC
    let prim = NamedPrim (TypedId fnty (Ident name 1))
    let primcall = AnnCall rng unitTypeTC (AnnPrimitive rng fnty prim) args CA_None
    id <- tcFresh "assert-invariants-thunk"
    let thunk = Fn (TypedId (mkFnTypeTC [] unitTypeTC) id) [] primcall () rng
    matchExp expTy (AnnLetFuns rng [id] [thunk] (AnnTuple rng unitTypeTC KindPointerSized [])) (T.unpack name)

tcRhoCallPrim ctx annot name args expTy = do
    -- Most (but not all) primitives can be given function-like signatures.
    -- The special cases should already have been handled.
    --
    -- To reduce boilerplate for the remainder, we look up a function type
    -- associated with each primitive, then type check a synthetic call of
    -- a "normal" variable.
    debugIf dbgVar $ green (text "tcRhoCallPrim: ") <> text name <> text " :?: " <> prettyT expTy
    case tcSigmaPrim ctx annot name of

       Just v_sigma -> do
         debugIf dbgVar $ green (text "tcRhoCallPrim: ") <> text name <> text  " :?: " <> prettyT v_sigma
         ann_var <- inst v_sigma "tcRhoVar"
         debugIf dbgVar $ green (text "tcRhoCallPrim: ") <> text name <> text  " :?: " <> prettyT ann_var
         primcall <- tcSigmaCallWithAnnBase ctx annot ann_var args CA_None expTy
         matchExp expTy primcall "var"

       Nothing -> do
         tcFails [string $ "Unknown primitive " ++ T.unpack name
                 ,prettyWithLineNumbers (rangeOf annot)
                 ]


tcSigmaPrim :: Context SigmaTC -> ExprAnnot -> T.Text -> Maybe (AnnExpr SigmaTC)
tcSigmaPrim ctx annot name = do
  case termVarLookup name (primitiveBindings ctx) of
    Just (avar, _) -> Just $  mkAnnPrimitive annot ctx avar
    Nothing        ->
      if name == T.pack "log-type"
        then let ty = unitTypeTC in
             Just (AnnPrimitive annot ty $ NamedPrim (TypedId ty (Ident name 0)))
        else Nothing

mkAnnPrimitive :: ExprAnnot -> Context SigmaTC -> TypedId SigmaTC -> AnnExpr SigmaTC
mkAnnPrimitive annot ctx tid =
  AnnPrimitive annot (tidType tid) $
    case Map.lookup (identPrefix $ tidIdent tid)
                    (primitiveOperations ctx) of
        Just (NamedPrim tid)      -> NamedPrim tid
        Just (PrimOp nm ty)       -> PrimOp nm ty
        Just (PrimOpInt o i1 i2)  -> PrimOpInt o i1 i2
        Just (FieldLookup name o) -> FieldLookup name o
        Just (CoroPrim {}       ) -> error $ "mkAnnPrim saw unexpected CoroPrim"
        Just (PrimInlineAsm {}  ) -> error $ "mkAnnPrim saw unexpected PrimInlineAsm"
        Just (LookupEffectHandler tag) -> LookupEffectHandler tag
        Nothing                   -> NamedPrim tid
-- }}}

-- Now, a bunch of straightforward rules:

--  -----------------------------------------
--  G |- True :: Bool      G |- False :: Bool
tcRhoBool rng b expTy = do
-- {{{
    let ty = PrimIntTC I1
    let ab = AnnLiteral rng ty (LitBool b)
    let check t0 = do
          t <- repr t0
          case t of
            PrimIntTC I1 -> return ab
            m@MetaTyVarTC {} -> do unify m ty [text "bool literal"]
                                   return ab
            RefinedTypeTC v _ _ -> check (tidType v)
            _ -> tcFails [string $ "Unable to check Bool constant in context"
                                ++ " expecting non-Bool type " ++ show t
                         , prettySourceRangeInfo (rangeOf rng)]
    case expTy of
         Infer r -> update r (return ab)
         Check t -> check t
-- }}}

--  ------------------
--  G |- [r]"..." :: Text (or Int8 or Int32)
tcRhoText rng b expTy = do
-- {{{
-- {{{
    let ty = TyAppTC (TyConTC "Text") []
    let ab = AnnLiteral rng ty (LitText b)
    let check t0 = do
          t <- repr t0
          case t of
             TyAppTC (TyConTC "Text") [] -> return ab
             m@MetaTyVarTC {} -> do unify m ty [text "text literal"]
                                    return ab
             RefinedTypeTC v _ _ -> check (tidType v)
             PrimIntTC I8 | T.length b == 1 ->
               if fromEnum (T.head b) >= 256
                 then tcFails [text "Rune cannot be represented as an Int8:"
                              , prettySourceRangeInfo (rangeOf rng)]
                 else return $ AnnLiteral rng t (LitInt $ LiteralInt (fromIntegral $ fromEnum $ T.head b) 8  b)
             PrimIntTC I32 | T.length b == 1 ->
                      return $ AnnLiteral rng t (LitInt $ LiteralInt (fromIntegral $ fromEnum $ T.head b) 32 b)
             t -> tcFails [string $ "Unable to check Text constant in context"
                                    ++ " expecting non-Text type " ++ show t
                          , prettySourceRangeInfo (rangeOf rng)]
    case expTy of
         Infer r -> update r (return ab)
         Check t -> check t
-- }}}

tcRhoTextOrBytes rng (SS_Text  _raw txt) expTy = tcRhoText  rng txt expTy
tcRhoTextOrBytes rng (SS_Bytes _raw bs)  expTy = tcRhoBytes rng bs  expTy

--  -------------------------
--  G |- b"..." :: Array Int8
tcRhoBytes rng bs expTy = do
    let ty = ArrayTypeTC (PrimIntTC I8)
    let ab = AnnLiteral rng ty (LitByteArray bs)
    let check t0 = do
          t <- repr t0
          case t of
             ArrayTypeTC m -> do unify m (PrimIntTC I8) [text "byte array literal"]
                                 return ab
             m@MetaTyVarTC {} -> do unify m ty [text "byte array literal"]
                                    return ab
             RefinedTypeTC v _ _ -> check (tidType v)
             t -> tcFails [string $ "Unable to check byte array constant in context"
                                    ++ " expecting non-byte-array type " ++ show t
                          , prettySourceRangeInfo (rangeOf rng)]
    case expTy of
         Infer r -> update r (return ab)
         Check t -> check t
-- }}}

-- {{{ We separate literal vals from non-literal expressions in array literals.
tcRhoArrayValue ctx tau (AE_Int annot str) = do
  AnnLiteral _ _ literal <- checkRho ctx (E_IntAST annot str) tau
  return (Left literal)

tcRhoArrayValue ctx tau (AE_Expr expr) = do
  ae <- checkRho ctx expr tau
  return $ Right ae
-- }}}

--  e1 :: tau             ...           en :: tau
--  ---------------------------------------------------
--  G |- prim mach-array-literal e1 ... en :: Array tau
tcRhoArrayLit ctx annot mbt args expTy = do
-- {{{
    tau <- case mbt of
             Nothing -> newTcUnificationVarTau $ T.pack $ "prim array type:" ++ showSourceRangeStr (rangeOf annot)
             Just t  -> do t' <- tcTypeAndResolve ctx t annot
                           if isTau t'
                            then return t'
                            else
                              tcFails [text "rho array lit must have tau type; had", prettyT t]
    let ty = ArrayTypeTC tau
    args' <- mapM (tcRhoArrayValue ctx tau) args
    let ab = AnnArrayLit annot ty args'
    let check t0 = do
          t <- repr t0
          case t of
             (ArrayTypeTC rho) -> do unify tau rho [text "mach-array literal"]
                                     return ab
             m@MetaTyVarTC {} -> do unify m ty [text "mach-array literal"]
                                    return ab
             RefinedTypeTC v _ _ -> check (tidType v)
             t -> tcFails [string $ "Unable to check array constant in context"
                                ++ " expecting non-array type " ++ show t
                          , prettySourceRangeInfo (rangeOf annot)]
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



--  G |- e1 ::: tau     (unit or integer)
--  G |- e2 ::: t2
--  -------------------
--  G |- e1 ; e2 ::: t2
-- {{{
tcRhoSeq ctx annot a b expTy = do
    ea <- inferRho ctx a "seq"
    id <- tcFresh ".seq"
    eb <- tcRho ctx b expTy
    --tcLift $ putDocLn $ text "type " <> pretty (typeTC ea) <> text " given to expr " <> pretty ea
    tcRhoSeqCheck (rangeOf a) (typeTC ea)
    return (AnnLetVar annot id ea eb)

tcRhoSeqCheck range t0 = do
    ty <- repr t0
    case ty of
      MetaTyVarTC mtv  -> tcAddConstraint (TcC_SeqUnit mtv) range
      TupleTypeTC _ [] -> return ()
      PrimIntTC n | n /= I1 -> return ()
      RefinedTypeTC v _ _ -> tcRhoSeqCheck range (tidType v)
      _ | isFnTyLike ty ->
           tcFails [text "Sequenced expression returned a function type:"
                   , indent 2 $ vcat [prettyWithLineNumbers range
                                     ,text "Maybe you forgot a function call?"
                                     ,string $ "If not, please add a value binding to make it clear "
                                          ++ "that you want to ignore the function-valued result."]]
      _ -> tcFails [text "Sequenced expression had a non-unit type:" <+> prettyT ty
                   , indent 2 $ vcat [prettyWithLineNumbers range]]

isFnTyLike (FnTypeTC {}) = True
isFnTyLike (RefinedTypeTC v _ _) = isFnTyLike (tidType v)
isFnTyLike (ForAllTC _ t) = isFnTyLike t
isFnTyLike _ = False
-- }}}


--  G |- e1 ::: tau
--  G |- e2 ::: Ref tau
--  --------------------
--  G |- e1 >^ e2 ::: ()
tcRhoStore ctx rng e1 e2 expTy = do
-- {{{
    a1 <- inferRho ctx e1 "store"
    a2 <- checkRho ctx e2 (RefTypeTC (typeTC a1))
    matchExp expTy (AnnStore rng unitTypeTC a1 a2) "store"
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
    t0 <- repr $ typeTC a1
    ty <- case t0 of
      RefTypeTC ty    -> return ty
      MetaTyVarTC  {} -> return tau
      other -> tcFails [string $ "Expected deref-ed expr "
                           ++ "to have ref type, had " ++ show other,
                        highlightFirstLineDoc (rangeOf rng)]
    matchExp expTy (AnnDeref rng ty a1) "deref"
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

analyzeLabels :: [T.Text] -> [T.Text] -> ([T.Text], [T.Text])
analyzeLabels lX lY =
  let sX = Set.fromList lX
      sY = Set.fromList lY
      sI = Set.intersection sX sY
  in (Set.toList (Set.difference sX sI), Set.toList (Set.difference sY sI))

--  G |- e1 ::: t1
--  G |-  .......
--  G |- en ::: tn
--  ------------------------------------
--  G |- (l1: e1, ..., ln: en) ::: (ln: t1, ..., ln: tn)
tcRhoRecord :: Context SigmaTC -> ExprAnnot -> [T.Text] -> [Term] -> Expected TypeTC -> Tc (AnnExpr RhoTC)
-- {{{
tcRhoRecord ctx rng labels exprs expTy = do
   rct <- case expTy of
     Infer _                    -> tcRecord ctx rng exprs [Nothing | _ <- exprs]
     Check t0 -> do
       t <- repr t0
       case t of MetaTyVarTC {} -> tcRecord ctx rng exprs [Nothing | _ <- exprs]
                 RecordTypeTC ctxLabels ts -> do
                      case analyzeLabels labels ctxLabels of
                        ([], []) -> do tcRecord ctx rng exprs [Just t  | t <- ts]
                        (extras, missings) -> do
                          tcFailsMore [text "Mismatched labels" <+> parens (pretty extras <> pretty missings) <+> text " for record"
                                      , highlightFirstLineDoc (rangeOf rng)]
                      
                 _ -> tcFailsMore [string $ "Record cannot check against non-record type " ++ show t
                                  , showStructure t]
   matchExp expTy rct (highlightFirstLineStr (rangeOf rng))
  where
    tcRecord ctx rng exps typs = do
      exprs <- typecheckExprsTogether ctx exps typs
      let tys = map typeTC exprs
      return $ AnnRecord rng (RecordTypeTC labels tys) labels exprs

    -- Typechecks each expression in the same context
    typecheckExprsTogether ctx exprs expectedTypes = do
        sanityCheck (eqLen exprs expectedTypes)
            (T.pack $ "typecheckExprsTogether: had different number of values ("
               ++ (show $ length exprs)
               ++ ") and expected types (" ++ (show $ length expectedTypes)
               ++ ")\nThis might be caused by a missing semicolon!\n"
               ++ show exprs ++ " versus \n" ++ show expectedTypes)
        mapM (\(e,mt) -> case mt of
                          Nothing -> inferRho ctx e "tuple subexpr"
                          Just t  -> checkRho ctx e t)
             (List.zip exprs expectedTypes)
-- }}}

--  G |- e ::: (l1: t1, ..., ln: tn)
--  ------------------------------------
--  G |- e.lX ::: tX
tcRhoRecordLookup :: Context SigmaTC -> ExprAnnot -> Term -> T.Text -> Expected TypeTC -> Tc (AnnExpr RhoTC)
-- -- {{{
tcRhoRecordLookup ctx rng expr fieldName expTy = do
   base <- inferRho ctx expr "indexed-record"
   tV <- repr (typeTC base)
   let mkRecordLookup tX = (AnnCall rng tX (AnnPrimitive rng tX (FieldLookup fieldName Nothing)) [base] CA_None)

   case (tV, expTy) of
      (MetaTyVarTC {}, Check tX) -> do
            -- Apply constraint that e has a record type mapping fieldName to tX.
            tcFailsMore [string $ "Record indexing cannot yet apply constraint to meta type variable " ++ show tV
                        , showStructure tV]
            -- No need to matchExp because we're just passing through the context-provided type.
            return (mkRecordLookup tX)

      (MetaTyVarTC {}, Infer _) -> do
            tX <- newTcUnificationVarTau $ "record_index"
            -- Apply constraint that e has a record type mapping fieldName to tX.
            tcFailsMore [string $ "Record indexing cannot yet apply constraint to meta type variable " ++ show tV
                        , showStructure tV]
            matchExp expTy (mkRecordLookup tX) (highlightFirstLineStr (rangeOf rng))

      (RecordTypeTC labels tys, _) -> do
        -- Check that v is a record type mapping fieldName to tX.
        case Map.lookup fieldName (Map.fromList (zip labels tys)) of
          Just tX -> do
                        matchExp expTy (mkRecordLookup tX) (highlightFirstLineStr (rangeOf rng))
          Nothing -> tcFailsMore [string $ "Record indexing applied to record type without field " ++ show fieldName
                        , indent 8 (text "The following fields were available: " <> pretty (map show labels))
                        ]

      _ -> do                   
            tcFailsMore [string $ "Record indexing applied to non-record type " ++ show tV
                        , showStructure tV]

-- }}}

--  G |- e1 ::: t1
--  G |-  .......
--  G |- en ::: tn
--  ------------------------------------
--  G |- (e1, ..., en) ::: (t1, ..., tn)
tcRhoTuple :: Context SigmaTC -> ExprAnnot -> Kind -> [Term] -> Expected TypeTC -> Tc (AnnExpr RhoTC)
-- {{{
tcRhoTuple ctx rng kind exprs expTy = do
   tup <- case expTy of
     Infer _                    -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
     Check t0 -> do
       t <- repr t0
       case t of MetaTyVarTC {} -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
                 TupleTypeTC kind' ts -> do
                                   tcUnifyKinds (UniConst kind) kind'
                                   tcTuple ctx rng exprs [Just t  | t <- ts]
                 _ -> tcFailsMore [string $ "Tuple cannot check against non-tuple type " ++ show t
                                  , showStructure t]
   matchExp expTy tup (highlightFirstLineStr (rangeOf rng))
  where
    tcTuple ctx rng exps typs = do
        exprs <- typecheckExprsTogether ctx exps typs
        let tys = map typeTC exprs
        return $ AnnTuple rng (TupleTypeTC (UniConst kind) tys) kind exprs

    -- Typechecks each expression in the same context
    typecheckExprsTogether ctx exprs expectedTypes = do
        sanityCheck (eqLen exprs expectedTypes)
            (T.pack $ "typecheckExprsTogether: had different number of values ("
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
-- ----------------------  e2 ::: t2 where t2 is a word-like type
-- G |- e1 .[ e2 ]  ::: t
tcRhoArrayRead :: ExprAnnot -> SafetyGuarantee -> AnnExpr SigmaTC -> AnnExpr SigmaTC -> Expected RhoTC -> Tc (AnnExpr RhoTC)
-- {{{
tcRhoArrayRead annot sg base aiexpr expTy = do
  let rng = rangeOf annot
  let ck t = do
        let expr = AnnArrayRead annot t (ArrayIndex base aiexpr rng sg)
        matchExp expTy expr "arrayread"

  let check t0 = do
       t <- repr t0
       case t of
        ArrayTypeTC t -> do ck t
        MetaTyVarTC _ -> do
            t <- case expTy of
                  Check t -> return t
                  Infer _ -> newTcUnificationVarTau $ "arrayread_type"
            unify (ArrayTypeTC t) (typeTC base) [text "arrayread type"]
            ck t
        RefinedTypeTC v _ _ -> check (tidType v)
        _ ->
            tcFails [string $ "Unable to arrayread expression of non-array type " ++ show (typeTC base)
                        ++ " (context expected type " ++ show expTy ++ ")"
                    , highlightFirstLineDoc rng]
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
        unify t (typeTC v) [text "arraypoke type"]
        let expr = AnnArrayPoke annot unitTypeTC
                                    (ArrayIndex base i (rangeOf annot) s) v
        matchExp expTy expr "arraypoke"

  let check t = case t of
        ArrayTypeTC t -> ck t
        MetaTyVarTC _ -> do
            t <- newTcUnificationVarTau $ "arraypoke_type"
            unify (ArrayTypeTC t) (typeTC base) [text "arraypoke type"]
            ck t
        RefinedTypeTC v _ _ -> check (tidType v)
        _ ->
          tcFails [string $ "Unable to arraypoke expression of type " ++ show (typeTC base)
                      ++ " (context expected type " ++ show expTy ++ ")"
                  , highlightFirstLineDoc (rangeOf annot)]
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
    unify (typeTC eb) (typeTC ec) [
         text "The two branches of an `if` expression must match."
        ,text "    The `then` branch had type" <+> prettyT (typeTC eb) <> text ";"
        ,text "    the `else` branch had type" <+> prettyT (typeTC ec) <> text "."]
    -- TODO use subsumption instead of unification?
    return (AnnIf rng (typeTC eb) ea eb ec)
-- }}}

--  G         |- e1 ::: t1
--  G{x:::t1} |- e2 ::: t2
--  ----------------------------
--  G |- let x = e1 in e2 ::: t2
tcRhoLet ctx rng (TermBinding v e1) e2 mt = do
-- {{{
    sanityCheck (not $ isRecursiveFunction boundName e1) (errMsg boundName)
    id <- tcFreshT boundName
    let ctxPend = ctx `addPendingBinding` v
    a1 <- case maybeVarType of
                 Nothing -> inferSigma ctxPend e1 "let"
                 Just ta -> do t <- tcType ctxPend ta
                               checkSigma ctxPend e1 t
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
    errMsg boundName = T.pack $ "Recursive binding of " ++ show boundName ++ " should use 'REC':"
           ++ highlightFirstLineStr (rangeOf rng)
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
    -- each binding (unless it has an explicit type annotation).
    unificationVarsOrTys <- sequence
                                [case e of
                                  E_TyCheck _ _ ty -> do ty' <- tcType ctx0 ty
                                                         return $ Right ty'
                                  E_FnAST _ f -> liftM Right (fnTypeShallow ctx0 f)
                                  _ -> liftM Left $ newTcUnificationVarSigma $
                                         "letrec_" `prependedTo` (evarName v)
                                | (TermBinding v e) <- recBindings]
    ids <- sequence [tcFreshT (evarName v) | (TermBinding v _) <- recBindings]
    -- Create an extended context for typechecking the bindings
    let varbind' (id, Left  u)  = varbind id u
        varbind' (id, Right ty) = varbind id ty
        ctxBindings = map varbind' (zip ids unificationVarsOrTys)
        ctx = prependContextBindings ctx0 ctxBindings
    verifyNonOverlappingBindings (rangeOf rng) "rec" ctxBindings

    -- Typecheck each binding
    tcbodies <- forM (zip unificationVarsOrTys recBindings) $
       (\(u_or_ty, TermBinding v b) -> do
           let ctxPend = ctx `addPendingBinding` v
           b' <- case (u_or_ty, evarMaybeType v) of
             (_, Just _) -> do tcFails [text "shouldn't have any annotation on letrec!"]
             (Left _u, _) -> do inferSigma ctxPend b "letrecX"
             (Right t, _) -> do checkSigma ctxPend b t
           case u_or_ty of
             Left u -> unify u (typeTC b') [string $ "recursive binding " ++ T.unpack (evarName v)]
             _      -> return ()
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
        when (not $ null nonfns) $ do
          tcFails $ [text "Recursive bindings should only contain functions! Had:"
                    ] ++ map showStructure nonfns
        let fnMarker fn _isCyclic = fn
        return $ mkFunctionSCCs ids fns e' fnMarker (AnnLetFuns rng)
-- }}}

--      M <= n
--      tX for X in [M,n] is a fresh metavar
-- G |- e ::: forall a1::k1..an::kn, rho
-- G |- t_n <::: k_n                          (checked later)
-- ------------------------------------------
-- G |- e :[ t1..tM ]  ::: rho{t1..tn/a1..an}
--
-- Note: we allow partial application, because otherwise it gets extremely
-- awkward to call functions that were quantified over effect variables.
tcRhoTyApp :: Context SigmaTC -> ExprAnnot -> Term -> [TypeAST] -> Expected RhoTC -> Tc (AnnExpr RhoTC)
tcRhoTyApp ctx annot e tsAST expTy = do
-- {{{
    debug $ "ty app: inferring sigma type for base..."
    aeSigma <- inferSigma ctx e "tyapp"
    debug $ "ty app: base has type " ++ show (typeTC aeSigma)
    situation <- classifyTypeInstSituation tsAST (typeTC aeSigma)
    case situation of
      TI_Sigma -> do
            types <- mapM (\t -> tcTypeAndResolve ctx t annot) tsAST
            expr <- instWith ("tcRhoTyApp: " ++ highlightFirstLineStr (rangeOf annot)) annot aeSigma types
            matchExp expTy expr "tyapp"
      TI_Empty -> matchExp expTy aeSigma "empty-tyapp"
      TI_Rho rho ->
            tcFails [string $ "Cannot apply type args to expression of"
                       ++ " non-polymorphic type: " ++ show rho
                    , highlightFirstLineDoc $ rangeOf e]
      TI_Unresolved ->
            tcFails [text $ "Could not instantiate due to unresolved type for the following term:"
                    , highlightFirstLineDoc $ rangeOf aeSigma
                    ,text $ "Try adding an explicit type annotation."
                    ]

data TypeInstSituation = TI_Empty | TI_Sigma | TI_Unresolved | TI_Rho TypeTC

classifyTypeInstSituation [] _ = return $ TI_Empty
classifyTypeInstSituation _ (ForAllTC {}) = return $ TI_Sigma
classifyTypeInstSituation tys tv@(MetaTyVarTC _) = do
  t <- repr tv
  case t of
    MetaTyVarTC _ -> return $ TI_Unresolved
    _ -> classifyTypeInstSituation tys t
classifyTypeInstSituation _ rho = return $ TI_Rho rho
-- }}}


-- G |- e ~~~> a1 ::: t1
-- G |- t1 is an instance of t
-- ------------------------------------------
-- G |- e as t  ~~~>  a1 ::: t
tcRhoTyCheck ctx annot e tya expTy = do
-- {{{
    ty <- tcTypeAndResolve ctx tya annot
    ann <- checkSigma ctx e ty
    do tcLift $ putDocLn $ text "tycheck ann result was " <> showStructure ann
    rv <- matchExp expTy ann "tycheck"
    do tcLift $ putDocLn $ text "tycheck rv result was " <> showStructure rv
    return $ rv
-- }}}

-- G |- b  ~~> f ::: ((s1 ... sn) -> sr)
-- G |- e1 ~~> a1 ::: t1     t1 <= s1
-- G |-  .......
-- G |- en ~~> an ::: tn     tn <= sn
-- ------------------------------------------
-- G |- b e1 ... en ~~> f a1 ... an ::: sr
-- {{{
tcRhoCall :: Context SigmaTC -> ExprAnnot
              -> ExprAST TypeAST -> [ExprAST TypeAST] -> CallAnnot
              -> Expected SigmaTC -> Tc (AnnExpr RhoTC)
tcRhoCall ctx rng base argstup ca exp_ty = do
   -- TODO think harder about when it's safe to push exp_ty down
   debug $ "tcRhoCall " ++ show exp_ty
   r <- newTcRef (error $ "tcRho>SigmaCall: empty result: ")
   app <- tcSigmaCall ctx rng base argstup ca (Infer r)
   instSigma app exp_ty

tryGetVarName (E_AnnVar _ (tid, _)) = T.unpack $ identPrefix (tidIdent tid)
tryGetVarName (AnnPrimitive _ _ fprim) = show fprim
tryGetVarName _ = ""

tcSigmaCall :: Context SigmaTC -> ExprAnnot -> ExprAST TypeAST
            -> [ExprAST TypeAST] -> CallAnnot -> Expected SigmaTC -> Tc (AnnExpr SigmaTC)

tcSigmaCall ctx rng base argexprs ca exp_ty = do
    annbase <- inferRho ctx base "called base"
    tcSigmaCallWithAnnBase ctx rng annbase argexprs ca exp_ty

tcSigmaCallWithAnnBase :: Context SigmaTC -> ExprAnnot -> AnnExpr TypeTC
            -> [ExprAST TypeAST] -> CallAnnot -> Expected SigmaTC -> Tc (AnnExpr SigmaTC)

tcSigmaCallWithAnnBase ctx rng annbase argexprs ca exp_ty = do
        let dbg d = debugIf dbgCalls d

        dbg $ text "{{{"

        let fun_ty = typeTC annbase
        (args_tys, res_ty_raw, fx, _cc, _, _levels) <- unifyFun fun_ty (length argexprs) ("tSC("++tryGetVarName annbase++")" ++ highlightFirstLineStr (rangeOf rng))
        dbg $ text "tcSigmaCall: fn type of" <+> prettyT annbase <+> text "is " <$$>
                    indent 2 (prettyT fun_ty <$$>
                              text ";; cc=" <+> prettyT _cc
                              <$$> text ";; fx=" <+> prettyT fx)
        dbg $ highlightFirstLineDoc (rangeOf rng)

        dbg $ text "call: fn args tys are " <> prettyT args_tys
        dbg $ string $ "call: arg exprs are " ++ show argexprs
        sanityCheck (eqLen argexprs args_tys) $
                T.pack $ "tcSigmaCall expected equal # of arguments! Had "
                ++ (show $ List.length argexprs) ++ "; expected "
                ++ (show $ List.length args_tys)
                ++ highlightFirstLineStr (rangeOf rng)
        --tcLift $ putStrLn $ "tcSigmaCall of " ++ show base
        --tcLift $ putStrLn $ show (zip argexprs args_ty)

        -- Strip refinements; just because a formal parameter has a given refinement,
        -- doesn't mean that the actual will necessarily follow the same refinement!
        args <- tcOnError [text "Failure when typechecking call"
                          ,highlightFirstLineDoc (rangeOf rng)]
                   (sequence [checkSigma ctx arg (shallowStripRefinedTypeTC ty)
                             | (arg, ty) <- zip argexprs args_tys]) return

        let res_ty = substExprsForRefinedArgs res_ty_raw args_tys args
        debugIf False $ text "res_ty_raw was " <> dullwhite (prettyT res_ty_raw)
        debugIf False $ text "res_ty     was " <> prettyT res_ty
        debugIf False $ text "after substituting for arg tys"
        debugIf False $ indent 6 (vcat $ map prettyT args_tys)
        debugIf False $ text "^^^^^^^"
        dbg $ text "call: annargs: "
        dbg $ showStructure (AnnTuple rng (TupleTypeTC (UniConst KindPointerSized)
                                                            (map typeTC args))
                                               KindPointerSized args)
        dbg $ text "call: res_ty  is " <> prettyT res_ty
        dbg $ text "call: exp_ty is " <> prettyT exp_ty
        dbg $ text "tcRhoCall deferring to instSigma"

        dbg $ green (text "call: annbase is: ") <> showStructure annbase

        ctxFx <- tcGetCurrentFnFx
        fx' <- repr fx
        if not $ isEmptyEffect fx'
          then do
            ctxFx' <- zonkType ctxFx
            debugIf False $ highlightFirstLineDoc (rangeOf rng)
            debugIf False $ text "ctxFx: " <> prettyT ctxFx'
            debugIf False $ text "fx: " <> prettyT fx'
            debugIf False $ showStructure fun_ty
            debugIf False $ text "len argexprs:" <> pretty (length argexprs) <+> string ("tSC("++tryGetVarName annbase++")")
            unify fx ctxFx' [text $ "Inconsistent effects at call site: "
                            ,highlightFirstLineDoc (rangeOf rng)
                            ,text $ "Effect of called function:"
                            ,indent 4 (prettyT fx')
                            ,text $ "Effect of calling context:"
                            ,indent 4 (prettyT ctxFx')]
          else return ()

        let app = mkAnnCall rng res_ty annbase args ca
        dbg $ text "call: overall ty is " <> prettyT (typeTC app)
        rv <- matchExp exp_ty app "tcSigmaCall"
        dbg $ text "}}}"
        return rv

mkAnnCall rng res_ty annbase args ca =
  case annbase of
    -- Strip type application to make it clear to KN that we're using
    -- primitives in a first-order way.
    E_AnnTyApp _ _ annprim@(AnnPrimitive _ _ (NamedPrim (TypedId _ (GlobalSymbol gs _)))) [_argty]
         | T.unpack gs `elem` ["prim_arrayLength"]
      -> AnnCall rng res_ty annprim args ca
    E_AnnTyApp _ _ annprim@(AnnPrimitive _ _ (PrimOp nm _)) [_argty]
      | nm `elem` ["=="]
      -> AnnCall rng res_ty annprim args ca

    E_AnnTyApp _ _ (AnnPrimitive _ _ (NamedPrim (TypedId _ (GlobalSymbol gs _)))) [argty]
         | T.unpack gs == "allocDArray"
      -> case args of
           [arraySize] -> AnnAllocArray rng res_ty arraySize argty Nothing DoZeroInit
           _ -> error $ "saw anncall of " ++ show annbase ++ " with args: " ++ show args
    E_AnnVar _rng (_tid, Just cid)
      -> AnnAppCtor rng res_ty cid  args
    _ -> AnnCall rng res_ty annbase args ca

unifyFun :: RhoTC -> Int -> String -> Tc ([SigmaTC], RhoTC, RhoTC, Unifiable CallConv, Unifiable ProcOrFunc, Levels)
unifyFun (FnTypeTC args res fx cc ft levels) _ _msg = return (args, res, fx, cc, ft, levels)
unifyFun (ForAllTC {}) _ str = tcFails [text "invariant violated: sigma passed to unifyFun!"
                                        ,text "For now, lambdas given forall types must be annotated with forall markers."
                                        ,string str]
unifyFun tau nargs msg = do
        arg_tys <- mapM (\_ -> newTcUnificationVarTau $ T.pack $ "fn args ty:" ++ msg) (replicate nargs ())
        res_ty <- newTcUnificationVarTau (T.pack $ "fn res ty:" ++ msg)
        fx_ty  <- newTcUnificationVarEffect (T.pack $ "effectvar:" ++ msg)
        cc <- genUnifiableVar
        ft <- genUnifiableVar
        levels <- mkLevels
        unify tau (FnTypeTC arg_tys res_ty fx_ty cc ft levels) [string $ "unifyFun(" ++ msg ++ ")"]
        return (arg_tys, res_ty, fx_ty, cc, ft, levels)
-- }}}

hasNonTrivialRefinementDifferences (arg_ty, var_ty) =
  case (arg_ty, var_ty) of
    (RefinedTypeTC _ e_arg _ , RefinedTypeTC _ e_var _) ->
      not (equivStructureAndVarNames e_arg e_var)
    _ -> False

allP f xs ys = all (uncurry f) (zip xs ys)

liftEqUnifiable f u1 u2 =
  case (u1, u2) of
    (UniConst v1, UniConst v2) -> f v1 v2
    (UniVar (x1, _), UniVar (x2, _)) -> x1 == x2
    _ -> False

sameLabels :: [T.Text] -> [T.Text] -> Bool
sameLabels l1 l2 = l1 == l2

-- TODO maybe this should be monadic, to compute reprs first?
tcTypeEquiv t1 t2 =
  let q = tcTypeEquiv in
  case (t1, t2) of
     (PrimIntTC            s1 , PrimIntTC          s2   ) -> s1 == s2
     (TyConTC      tcnm1      , TyConTC   tcnm2         ) -> tcnm1 == tcnm2
     (TyAppTC      con1 tys1  , TyAppTC   con2 tys2     ) -> allP tcTypeEquiv (con1:tys1) (con2:tys2)
     (RecordTypeTC labs1 tys1 , RecordTypeTC labs2 tys2 ) -> sameLabels labs1 labs2 && allP tcTypeEquiv tys1 tys2
     (TupleTypeTC _k1    tys1 , TupleTypeTC _k2    tys2 ) -> {- TODO kinds -} allP tcTypeEquiv tys1 tys2
     (FnTypeTC     s1 t1 fx1 c1 x1 _levels1,
      FnTypeTC     s2 t2 fx2 c2 x2 _levels2) -> allP q s1 s2 && q t1 t2 && q fx1 fx2 && liftEqUnifiable (==) c1 c2 && liftEqUnifiable (==) x1 x2 -- ignore levels?
     (ForAllTC   tvs1 rho1    , ForAllTC   tvs2 rho2    ) -> allP (==) tvs1 tvs2 && q rho1 rho2
     (TyVarTC    tv1 _mbk1    , TyVarTC    tv2 _mbk2    ) -> tv1 == tv2
     (MetaTyVarTC m1          , MetaTyVarTC m2          ) -> m1 == m2
     (RefTypeTC     ty1       , RefTypeTC     ty2       ) -> q ty1 ty2
     (ArrayTypeTC   ty1       , ArrayTypeTC   ty2       ) -> q ty1 ty2
     (RefinedTypeTC v1 e1 _ids1, RefinedTypeTC v2 e2 _ids2) -> v1 `equivTypedId` v2 && equivStructureAndVarNames e1 e2 -- note: no check on ids...
     _ -> False

equivTypedId tid1 tid2 =
  tidType tid1 `tcTypeEquiv` tidType tid2 && identPrefix (tidIdent tid1) == identPrefix (tidIdent tid2)

equivStructureAndVarNames :: AnnExpr TypeTC -> AnnExpr TypeTC -> Bool
equivStructureAndVarNames e1 e2 =
  let q = equivStructureAndVarNames in
  let qf _f1 _f2 = error "equivStructureAndVarNames can't yet handle functions" in
  let qc _c1 _c2 = error "equivStructureAndVarNames can't yet handle case arms" in
  let qtid = equivTypedId in
  let qp prim1 prim2 =
        case (prim1, prim2) of
            (NamedPrim tid1               , NamedPrim tid2              ) -> qtid tid1 tid2
            (PrimOp name1 ty1             , PrimOp name2 ty2            ) -> name1 == name2 && tcTypeEquiv ty1 ty2
            (PrimOpInt o1 isba isbx       , PrimOpInt o2 isba2 isbx2    ) -> isba == isba2 && isbx == isbx2 && o1 == o2
            (CoroPrim     p1 tya1 tyb1    , CoroPrim     p2 tya2 tyb2   ) -> p1 == p2 && tcTypeEquiv tya1 tya2 && tcTypeEquiv tyb1 tyb2
            (PrimInlineAsm ty1 txa txb b1 , PrimInlineAsm ty2 tza tzb b2) -> tcTypeEquiv ty1 ty2 && txa == tza && txb == tzb && b1 == b2
            _ -> False
          in
  let qcr cr1 cr2 =
        case (cr1, cr2) of
           (CompilesResult (OK e1)       , CompilesResult (OK e2)         ) -> q e1 e2
           (CompilesResult (Errors errs1), CompilesResult (Errors errs2)  ) -> map show errs1 == map show errs2
           _ -> False
         in
  let qai ai1 ai2 =
        case (ai1, ai2) of
            (ArrayIndex ea1 eb1 _ sg1 , ArrayIndex ea2 eb2 _ sg2) -> q ea1 ea2 && q eb1 eb2 && sg1 == sg2
          in
  let qa le1 le2 =
        case (le1, le2) of
            (Left l1, Left l2) -> l1 == l2
            (Right e1, Right e2) -> q e1 e2
            _ -> False in
  case (e1, e2) of
      (AnnLiteral     _ _ lit1        , AnnLiteral     _ _ lit2        )  -> lit1 == lit2
      (AnnCall        _ _ e1c e1s _   , AnnCall        _ _ e2c e2s _   )  -> allP q (e1c:e1s) (e2c:e2s)
      (AnnAppCtor     _ _ c1  e1s     , AnnAppCtor     _ _ c2  e2s     )  -> c1 == c2 && allP q e1s e2s
      (AnnCompiles    _ _ cr1         , AnnCompiles    _ _ cr2         )  -> cr1 `qcr` cr2
      (AnnKillProcess _ ty1 t1        , AnnKillProcess _ ty2 t2        )  -> t1 == t2 && tcTypeEquiv ty1 ty2
      (AnnIf          _ _ c1 a1 b1    , AnnIf          _ _ c2 a2 b2    )  -> allP q [c1,a1,b1] [c2,a2,b2]
      (E_AnnFn        f1              , E_AnnFn        f2              )  -> qf f1 f2
      (AnnLetVar      _ i1 e1 b1      , AnnLetVar      _ i2 e2 b2      )  -> i1 == i2 && q e1 e2 && q b1 b2
      (AnnLetRec      _ is1 es1 b1    , AnnLetRec      _ is2 es2 b2    )  -> allP (==) is1 is2 && allP q es1 es2 && q b1 b2
      (AnnLetFuns     _ is1 fs1 b1    , AnnLetFuns     _ is2 fs2 b2    )  -> allP (==) is1 is2 && allP qf fs1 fs2 && q b1 b2
      (AnnAlloc       _ _ e1 mr1      , AnnAlloc       _ _ e2 mr2      )  -> q e1 e2 && mr1 == mr2
      (AnnDeref       _ _ e1          , AnnDeref       _ _ e2          )  -> q e1 e2
      (AnnStore       _ _ e1 x1       , AnnStore       _ _ e2 x2       )  -> q e1 e2 && q x1 x2
      (AnnArrayLit    _ _ le1         , AnnArrayLit    _ _ le2         )  -> allP qa le1 le2
      (AnnAllocArray  _ _ e1 t1 mr1 z1, AnnAllocArray  _ _ e2 t2 mr2 z2)  -> q e1 e2 && tcTypeEquiv t1 t2 && mr1 == mr2 && z1 == z2
      (AnnArrayRead   _ _ ai1         , AnnArrayRead   _ _ ai2         )  -> ai1 `qai` ai2
      (AnnArrayPoke   _ _ ai1 e1      , AnnArrayPoke   _ _ ai2 e2      )  -> ai1 `qai` ai2 && q e1 e2
      (AnnRecord      _ _ l1s e1s     , AnnRecord      _ _ l2s e2s     )  -> -- sorted labels?
                                                                             l1s == l2s && allP q e1s e2s
      (AnnTuple       _ _ k1 e1s      , AnnTuple       _ _ k2 e2s      )  -> k1 == k2 && allP q e1s e2s
      (AnnCase        _ _ e1 c1s      , AnnCase        _ _ e2 c2s      )  -> q e1 e2 && allP qc c1s c2s
      (E_AnnVar       _ (tid1, mcid1) , E_AnnVar       _ (tid2, mcid2) )  -> qtid tid1 tid2  && mcid1 == mcid2
      (AnnPrimitive   _ _ p1          , AnnPrimitive   _ _ p2          )  -> p1 `qp` p2
      (E_AnnTyApp     _ _ e1 t1s      , E_AnnTyApp     _ _ e2 t2s      )  -> q e1 e2 && allP tcTypeEquiv t1s t2s
      _ -> False


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

mkFnName pendings = do
 u <- newTcUniq
 return $
     T.pack $ (joinWith "__" (toList $ Seq.reverse $ fmap T.unpack pendings)) ++ ".anon" ++ "." ++ show u ++ "_"

-- G{a1:k1}...{an:kn}{x1 : t1}...{xn : tn} |- e ::: tb
-- ---------------------------------------------------------------------
-- G |- { forall a1:k1, ..., an:kn, x1 : t1 => ... => xn : tn => e } :::
--        forall a1:k1, ..., an:kn,    { t1 => ... =>      tn => tb }
-- {{{
tcSigmaFn :: Context SigmaTC -> FnAST TypeAST -> Expected SigmaTC -> Tc (AnnExpr SigmaTC)
tcSigmaFn ctx0 fnAST0 expTyRaw = do
  fnAST <- if T.pack "" == (fnAstName fnAST0)
             then do nm <- mkFnName (pendingBindings ctx0)
                     return fnAST0 { fnAstName = nm }
             else do return fnAST0
  let ctx = ctx0 { pendingBindings = Seq.singleton (fnAstName fnAST) }
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
        tcSigmaFnHelper ctx fnAST expTyRaw tyformals

tcSigmaFnHelper ctx fnAST expTyRaw tyformals = do
    let annot = fnAstAnnot fnAST
    let ktvs = map convertTyFormal tyformals
    taus <- genNonSigmaUnificationVarsLike ktvs (\n -> T.pack $ "fn type parameter " ++ show n ++ " for " ++ T.unpack (fnAstName fnAST))

    let extTyCtx = ctx { localTypeBindings = extendTypeBindingsWith ctx ktvs taus }

    debugDoc $ text "tcSigmaFn: f is " <> pretty (show fnAST)
    debugDoc $ text "tcSigmaFn: expTyRaw is " <> prettyT expTyRaw
    debugDoc $ text "tcSigmaFn: tyformals is " <> pretty tyformals
    debugDoc $ text "tcSigmaFn: ktvs is " <> pretty ktvs
    debugDoc $ text "tcSigmaFn: taus is " <> prettyT taus

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
                     (T.pack $ "tcSigmaFn: expected same number of formals for "
                      ++ show ktvs ++ " and " ++ show exp_ktvs)
          exp_rho' <- resolveType annot (extendTypeBindingsWith ctx exp_ktvs taus) exp_rho_raw
          return $ Just exp_rho'
        _ -> return $ Nothing

    -- While we're munging, we'll also make sure the names are all distinct.
    uniquelyNamedFormals <- getUniquelyNamedAndRetypedFormals' ctx annot
                                   (fnFormals fnAST) (fnAstName fnAST)
                                   (localTypeBindings extTyCtx) []

    -- Extend the variable environment with the function arg's types.
    let extCtx = extendContext extTyCtx uniquelyNamedFormals

    -- Check or infer the type of the body.
    (annbody, body_ty, fx, uniquelyNamedBinders) <- case mb_rho of
      -- for Infer or for Check of a non-ForAll type
      Nothing       -> do fx <- newTcUnificationVarEffect "sigma.fx.infer"
                          annbody <- tcWithCurrentFx fx $
                                       inferSigma extCtx (fnAstBody fnAST) "poly-fn body"
                          return (annbody, typeTC annbody, fx, uniquelyNamedFormals)
      Just exp_rho' -> do
            let var_tys = map tidType uniquelyNamedFormals
            (arg_tys, body_ty, fx, _cc, _ft, _levels) <- unifyFun exp_rho' (length var_tys) ("poly-fn-lit" ++ highlightFirstLineStr (rangeOf annot))

            if any hasNonTrivialRefinementDifferences (zip arg_tys var_tys)
              then
                 tcFails [string $ "Cannot yet check a function which has refinements"
                         ++ " on both its explicit argument bindings and its type signature."]
              else do
                 debugDoc3 $ string "!!!!!!!!!!!!!!!!!!!!!!!! (sigma)"
                 debugDoc3 $ string (show $ fnAstName fnAST)
                 debugDoc3 $ string "var_tys: " <+> prettyT var_tys
                 debugDoc3 $ string "arg_tys: " <+> prettyT arg_tys

                 mapM_ (tcSelectTy annot) (zip arg_tys var_tys)

            debugDoc $ string "arg_tys: " <+> prettyT arg_tys
            debugDoc $ string "zipped : " <+> prettyT (zip arg_tys var_tys)
            mapM_ (\(t1, t2) -> subsCheckTy t1 t2 "sCETM") (zip var_tys arg_tys)
            
            --var_tys'' <- mapM shZonkType var_tys
            --debugDoc $ string "var_tys'': " <+> pretty var_tys''
            --debugDoc $ string "metaOf var_tys  : " <+> pretty (show $ collectAllUnificationVars var_tys)
            --debugDoc $ string "metaOf var_tys'': " <+> pretty (show $ collectAllUnificationVars $ map unMBS var_tys'')
            -- mvar_tys'' <- mapM shZonkMetaType (collectAllUnificationVars var_tys)

            pickedTys <- pickBetween (rangeOf (fnAstAnnot fnAST))
                                     arg_tys var_tys
            let uniquelyNamedBinders =
                         map (\(TypedId _ id, ty) -> TypedId ty id)
                             (zip uniquelyNamedFormals pickedTys)

            --tcLift $ putDocLn $ text ("tcSigmaFnHelper: fx for " ++ show (fnAstName fnAST) ++ " is ") <> pretty fx
            annbody <- tcWithCurrentFx fx $
                         checkRho extCtx (fnAstBody fnAST) body_ty
            return (annbody, body_ty, fx, uniquelyNamedBinders)

    debugDoc $ text "inferred raw type of body of polymorphic function: "
                    <> prettyT (typeTC annbody)

    levels <- mkLevels
    let fnty0 = ForAllTC ktvs $
            fnTypeTemplate fnAST argtys body_ty fx levels
              where argtys = map tidType uniquelyNamedBinders

    -- The function type is expressed in terms of meta type variables,
    -- which have now served their purpose and must be replaced by
    -- bound type variables. We'll do the replacement by first making sure
    -- that nothing has been unified with them so far, and then writing
    -- the appropriate bound type variable to the ref.
    _ <- mapM (\(t, (tv, k)) -> do
                 t' <- repr t
                 case t' of
                   (MetaTyVarTC m) -> do
                        debugDoc $ text "zonked " <> prettyT t <> text " to " <> prettyT t <> text "; writing " <> pretty tv
                        writeTcMetaTC m (TyVarTC tv (UniConst k))
                   _ -> tcFails [text "The following polymorphic function will only work if the type parameter"
                                   <+> pretty tv <+> text "is always instantiated to" <+> prettyT t'
                                ,highlightFirstLineDoc (rangeOf annot)]
              ) (zip taus ktvs)
    -- Zonk the type to ensure that the meta vars are completely gone.
    debugDoc $ text "inferred raw overall type of polymorphic function: " <> prettyT fnty0
    debugDoc $ text "zonking; (meta)/tyvars were " <> prettyT taus <$> pretty ktvs
    fnty <- zonkType fnty0
    debugDoc $ text "inferred overall type of body of polymorphic function: " <> prettyT fnty

    -- We also need to zonk the expected type, which might have wound up
    -- getting some of its meta type variables unified with taus that now
    -- refer to bound type variables.
    expTy' <- case expTyRaw of
                Check t -> liftM Check (zonkType t)
                Infer _ -> return expTyRaw

    -- Note we collect free vars in the old context, since we can't possibly
    -- capture the function's arguments from the environment!
    let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol (fnAstName fnAST) NoRename))
                          uniquelyNamedBinders annbody () annot
    debugDoc $ text "tcSigmaFn calling matchExp  uniquelyNamedFormals = " <> prettyT (map tidType uniquelyNamedFormals)
    debugDoc $ text "tcSigmaFn calling matchExp  expTyRaw = " <> prettyT expTyRaw
    debugDoc $ text "tcSigmaFn calling matchExp, expTy'   = " <> prettyT expTy'
    matchExp expTy' fn "tcSigmaFn"

mkTypeFormal (BoundTyVar nm sr, kind) = TypeFormal nm sr kind
mkTypeFormal (othervar, _kind) =
    error $ "Whoops, expected only bound type variables!\n" ++ show othervar

-- Extend the type environment with the forall-bound variables
-- declared in the function literal.
extendTypeBindingsWith ctx ktvs taus =
      foldl' ins (localTypeBindings ctx) (zip taus ktvs)
       where ins m (mtv, (BoundTyVar nm _sr, _k)) = Map.insert nm mtv m
             ins _ (_ ,  (SkolemTyVar {}, _))= error "ForAll bound a skolem!"

-- TODO this can result in losing annotations...
-- If we have something like
--       foo :: { % ra : T : e(ra) }
--       foo = { a : % rb : T : p(rb) }
-- we will completely drop p(rb)!
pickBetween rng argtys vartys =
  if Prelude.length argtys /= Prelude.length vartys
    then tcFails [text "Expected this function to have" <+> pretty (Prelude.length argtys) <+>
                           text "arguments, but it had" <+> pretty (Prelude.length vartys) <> text ":"
                 , highlightFirstLineDoc rng]
    else mapM picked (zipTogether argtys vartys)
  where
   picked (mb_argty_0, mb_varty) = do
     mb_argty <- liftMaybe repr mb_argty_0
     case (mb_argty, mb_varty) of
       -- If the argty is a meta variable, we might get more specific error messages
       -- by using the definitely-not-less-specific varty.
       (Just (MetaTyVarTC {}), Just varty) -> return varty
       -- Otherwise, the argty should have at least as much information as the varty,
       -- since the fnTypeTemplate definition in Main.hs will copy the varty's types.
       (Just argty, Just _) -> return argty
       (_, Just varty) -> return varty -- Mismatch, will be caught later by matchExp
       _ -> tcFails [text "Invariant violated in Typecheck.hs:pickBetween while checking:"
                    , highlightFirstLineDoc rng]
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
                                                  (localTypeBindings ctx) (map tidIdent refinementVars)

    (mbExpBodyTy, fx, uniquelyNamedBinders) <- case expTy of
       Infer _    -> do    fx <- newTcUnificationVarEffect "rho.fx.infer"
                           return (Nothing, fx, uniquelyNamedFormals)
       Check fnty -> do
                           -- |arg_tys| are the corresponding arguments expected
                           -- by the context (or a type annotation on the binder'
                           -- for this function).
                           (arg_tys, body_ty, fx, _cc, _ft, _levels) <- unifyFun fnty (length uniquelyNamedFormals) ("@" ++ highlightFirstLineStr rng)

                           -- |var_tys| are the types written down by the programmer
                           -- on the function's argument variables.
                           let var_tys = map tidType uniquelyNamedFormals

                           -- It's perhaps a little bit counter-intuitive, but
                           -- the var_tys are the "expected" types, and the
                           -- external annotations are the "actual" types. One
                           -- way of looking at this is that we can alter the
                           -- types associated with the function's arg vars,
                           -- but we can't alter the context's expectations.

                           debugDoc3 $ text "checking subsumption betweeen " <$> indent 4 (prettyT (zip arg_tys var_tys))
                           _ <- sequence [subsCheckTy argty varty "mono-fn-arg" |
                                           (argty, varty) <- zip arg_tys var_tys]

                           if any hasNonTrivialRefinementDifferences (zip arg_tys var_tys)
                             then do
                                 tcFails [string $ "Cannot yet check a function (" ++ T.unpack (fnAstName f) ++ ") which has refinements"
                                                   ++ " on both its explicit argument bindings and its type signature."
                                         --, indent 2 (text "Refined signature types:" <+> indent 2 (pretty ars))
                                        -- , indent 2 (text "Refined variable types:" <+> indent 2 (pretty vrs))
                                         , highlightFirstLineDoc rng]
                                         -- When we remove this check, we should un-comment one of the tests in
                                         -- bootstrap/testscase/test-fn-precond-2
                             else do
                                 debugDoc3 $ string "!!!!!!!!!!!!!!!!!!!!!!!! (rho)"
                                 debugDoc3 $ string (show $ fnAstName f)
                                 debugDoc3 $ string "var_tys: " <+> prettyT var_tys
                                 debugDoc3 $ string "arg_tys: " <+> prettyT arg_tys

                           pickedTys <- pickBetween rng arg_tys var_tys
                           let uniquelyNamedBinders =
                                        map (\(TypedId _ id, ty) -> TypedId ty id)
                                            (zip uniquelyNamedFormals pickedTys)

                           return (Just body_ty, fx, uniquelyNamedBinders)

    -- Extend the variable environment with the function arg's types.
    let extCtx = extendContext ctx uniquelyNamedBinders

    -- Check or infer the type of the body.
    annbody <- tcWithCurrentFx fx $
      case mbExpBodyTy of
        Nothing      -> do inferSigma extCtx (fnAstBody f) "mono-fn body"
        Just body_ty -> do checkRho extCtx (fnAstBody f) body_ty

    levels <- mkLevels
    let fnty = fnTypeTemplate f argtys retty fx levels
                where argtys = map tidType uniquelyNamedBinders
                      retty  = case mbExpBodyTy of
                                 Nothing -> typeTC annbody
                                 Just rt -> rt

    do fnty' <- zonkType fnty
       debug2 $ "fnty for " ++ (show (fnAstName f)) ++ " is " ++ show fnty
       debug2 $ "zonked fnty for " ++ (show (fnAstName f)) ++ " is " ++ show fnty'

    -- Note we collect free vars in the old context, since we can't possibly
    -- capture the function's arguments from the environment!
    let fn = E_AnnFn $ Fn (TypedId fnty (GlobalSymbol (fnAstName f) NoRename))
                          uniquelyNamedBinders annbody () annot
    matchExp expTy fn "tcRhoFn"
-- }}}

tcSelectTy annot (argty0, varty0) = do
    argty <- repr argty0
    varty <- repr varty0
    case (argty, varty) of
       (_, MetaTyVarTC {}) -> do return ()
       (MetaTyVarTC {}, _) -> do
         tcFails [text "didn't expect argty to be meta ty var without varty also being the same..."
                 , prettyWithLineNumbers (rangeOf annot)
                 , text "arg ty:" <+> prettyT argty
                 , text "var ty:" <+> prettyT varty
                 ]
       _ -> return ()

-- {{{ Helpers for type-checking function literals.
extendContext :: Context SigmaTC -> [TypedId TypeTC] -> Context SigmaTC
extendContext ctx protoFormals =
                 prependContextBindings ctx (map bindingForVar protoFormals)

fnTypeTemplate :: FnAST TypeAST -> [TypeTC] -> TypeTC -> TypeTC -> Levels -> TypeTC
fnTypeTemplate _f argtypes retty fx levels =
  -- Compute "base" function type, ignoring any type parameters.
  FnTypeTC argtypes retty fx (UniConst FastCC) (UniConst FT_Func) levels

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
        rename (GlobalSymbol name _alt) _u =
                tcFails [text "Cannot rename global symbol " <> text name]

-- | Verify that the given formals have distinct names,
-- | and return unique'd versions of each.
getUniquelyNamedAndRetypedFormals' ctx annot rawFormals fnProtoName  tybinds refinementArgs = do
    ufs'0 <- getUniquelyNamedFormals (rangeOf annot) rawFormals fnProtoName
    mapM retypeAndResolve ufs'0
   where retypeAndResolve v = do
            fmapM_TID (tcType' ctx refinementArgs ris) v >>= retypeTID (resolveType annot tybinds)
         ris = if null refinementArgs then RIS_False else RIS_True

tcTypeAndResolve ctx typ annot = do
  t <- tcType ctx typ
  resolveType annot (localTypeBindings ctx) t

tcType :: Context TypeTC -> TypeAST -> Tc TypeTC
tcType ctx typ = tcType' ctx [] RIS_False typ

data IsRefinementInScope = RIS_True | RIS_False deriving Show

tcType' :: Context TypeTC -> [Ident] -> IsRefinementInScope -> TypeAST -> Tc TypeTC
tcType' ctx refinementArgs ris typ = do
  let q = tcType' ctx refinementArgs RIS_False
  case typ of
        MetaPlaceholderAST MTVTau    nm -> newTcUnificationVarTau    (T.pack nm)
        MetaPlaceholderAST MTVSigma  nm -> newTcUnificationVarSigma  (T.pack nm)
        MetaPlaceholderAST MTVEffect nm -> newTcUnificationVarEffect (T.pack nm)
        PrimIntAST         sz -> return (PrimIntTC sz )
        TyVarAST      tv      -> liftM (TyVarTC tv) genUnifiableVar
        RefTypeAST    ty      -> liftM   RefTypeTC   (q ty)
        ArrayTypeAST  ty      -> liftM   ArrayTypeTC (q ty)
        RecordTypeAST labels types -> liftM  (RecordTypeTC labels) (mapM q types)
        TupleTypeAST  k types -> liftM  (TupleTypeTC (UniConst k)) (mapM q types)
        TyConAST nam          -> return $ TyConTC nam
        TyAppAST con types    -> do kindCheckDT con types ctx
                                    liftM2 TyAppTC (q con) (mapM q types)
        ForAllAST ktvs rho    -> do taus <- genNonSigmaUnificationVarsLike ktvs (\n -> T.pack $ "tcType'forall param " ++ show n)
                                    let xtvs = map (\(tv,k) -> TyVarTC tv (UniConst k)) ktvs
                                    let ctx' = ctx { localTypeBindings = extendTypeBindingsWith ctx ktvs taus }
                                    rv <- liftM (ForAllTC ktvs) (tcType' ctx' refinementArgs RIS_False rho)
                                    let tryOverwrite (tv, MetaTyVarTC m) = do
                                            mty <- readTcMeta m
                                            case mty of
                                                Unbound _ -> do writeTcMetaTC m tv
                                                BoundTo (MetaTyVarTC m') -> tryOverwrite (tv, MetaTyVarTC m' )
                                                BoundTo ut -> do tcFailsMore [
                                                                   text "tcType' didn't expect unification variable" <+> prettyT m <+> text "associated"
                                                                  ,text "with a bound type variable" <+> prettyT tv <+> text "to get unified!"
                                                                  ,indent 8 (prettyT ut)
                                                                  ,line
                                                                  ,prettyT typ]
                                        tryOverwrite (tv, tau) = do
                                          tcFails [text "tcType'.tryOverwrite could not handle non-meta tau for type variable " <> prettyT tv
                                                  ,prettyT tau]
                                    mapM_ tryOverwrite (zip xtvs taus)
                                    return rv
        FnTypeAST ss r fx cc ft -> do
          let rng    = MissingSourceRange $ "refinement for fn type..."
          let annot = annotForRange rng

          refinedFormalsFull <- mapM (\ (t, idx) -> do
                case t of
                  RefinedTypeAST nm t' _ -> return $ Right (TypedId t' (Ident (T.pack nm) 0))
                  other                  -> do i <- tcFreshT (T.pack $ "_" ++ show idx)
                                               return $ Left (TypedId other i))
               (zip ss [0..])

          let bareRefinedFormals = [v | Right v <- refinedFormalsFull]

          uniqRefinedFormals <- getUniquelyNamedAndRetypedFormals' ctx annot
                                   bareRefinedFormals (T.pack $ "refinement for fn type...")
                                   (localTypeBindings ctx) []

          let extCtx = extendContext ctx uniqRefinedFormals
          let refinementArgs' = map tidIdent uniqRefinedFormals ++
                                  [tidIdent v | Left v <- refinedFormalsFull]

          --tcLift $ putDocLn $ text "tcType' checking " <> pretty typ
          --                 <$> text "w/ context extended with" <+> pretty uniqRefinedFormals
          --                 <$> text "and refinement args" <+> pretty refinementArgs'

          ss' <- mapM (tcType' extCtx refinementArgs' RIS_True) ss
          -- The binding for the function's return type, if any, should
          -- be in-scope for its refinement.
          extCtx' <- case r of
                       RefinedTypeAST nm r' _ -> do
                            unf <- getUniquelyNamedAndRetypedFormals' ctx annot
                                       [TypedId r' (Ident (T.pack nm) 0)] (T.pack "refinement for fn return type...")
                                       (localTypeBindings ctx) []
                            return $ extendContext extCtx unf
                       _ -> return extCtx
          r'  <- tcType' extCtx' refinementArgs' RIS_False r
          fx' <- tcType' ctx [] RIS_False fx
          levels <- mkLevels
          return $ FnTypeTC ss' r' fx' (UniConst cc) (UniConst ft) levels
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
                                   (localTypeBindings ctx) []
                      return (extendContext ctx [unf], tidIdent unf)

          e' <- checkRho ctx' e (PrimIntTC I1)
          ty' <- tcType' ctx' refinementArgs RIS_False ty
          return $ RefinedTypeTC (TypedId ty' id) e' refinementArgs

kindCheckDT con tys ctx = do
  case con of
    TyConAST dtname -> do
      case mapSeqLookup dtname (contextDataTypes ctx) of
        MSL_Lone dt -> do
          let numActuals = length (dataTypeTyFormals dt)
          if length tys /= numActuals
            then tcFails [text "Inconsistent use of type constructor" <+> pretty dtname <> text ":"
                         ,text "    Expected" <+> describeNumber numActuals "no"
                          <+> text "type parameter" <> text (sIfNotOne numActuals) <+>
                              text "but was given" <+> describeNumber (length tys) "zero"]
            else return ()
        _ -> return ()
    _ -> return ()

sIfNotOne n = if n == 1 then "" else "s"

describeNumber n zero = text $
  case n of
    0 -> zero
    1 -> "one"
    2 -> "two"
    3 -> "three"
    4 -> "four"
    5 -> "five"
    6 -> "six"
    7 -> "seven"
    8 -> "eight"
    9 -> "nine"
    10 -> "ten"
    _ -> T.pack (show n)
-- }}}


-- {{{ Effect handlers:
{-
    { e } : { r @ (eff|effs) }
    arm : Eff => r'?    (r' if xform, else r)
    xform : { r => r' }
    
    Within each arm declared as Eff => o,
        resume      : { o => r'? @ effs }
    and resume_bare : { o => r'? @ (eff|effs) }
    -----------------------------------------
    HANDLE e arms (AS xform) END : r'? @ effs
-}
tcRhoHandler :: Context SigmaTC -> ExprAnnot
             -> ExprAST TypeAST -> [CaseArm EPattern Term TypeAST] -> Maybe (ExprAST TypeAST)
             -> Expected RhoTC -> Tc (AnnExpr RhoTC)
tcRhoHandler  ctx rng e arms mb_xform expTy = do
  -- We add a thunk wrapper to capture the effect of the handled action, so as to avoid
  -- infecting the effect of the calling function. Presumably most backends (including the
  -- native coroutine backend) will need some form of lambda, so this lets the programmer
  -- not bother writing the wrapper explicitly.
  u <- newTcUniq
  actionThunk <- inferRho ctx (E_FnAST rng (FnAST rng (T.pack $ ".fx.thunk_" ++ show u) [] [] e False)) "handled"

  hp <- newTcUnificationVarTau "handler-patterns"

  r   <- newTcUnificationVarTau "action"
  r'  <- newTcUnificationVarTau "xformed"
  resumeid <- tcFreshT $ T.pack "resume"
  resumebareid <- tcFreshT $ T.pack "resumebare"

  -- The return type of the handler (aka r'?)
  let r'p = case mb_xform of Nothing -> r
                             _       -> r'

  effs <- newTcUnificationVarTau "handler-effs"

  let preCheckBranch (CaseArm pat _ _ _ _) = checkEffectPattern ctx pat hp

  ps_outtys <- forM arms preCheckBranch
  eff <- zonkType hp
  let fneff = effectExtendTC eff effs

  levels <- mkLevels
  
  -- TODO (typeTC action)
  let checkBranch (CaseArm pat body guard _ brng, (p, outty)) = do
        let names = epatBoundNames pat
        verifyNamesAreDistinct (rangeOf rng) "case" names

        let resumety = FnTypeTC [outty] r effs (UniConst FastCC) (UniConst FT_Func) levels
        let resumebarety = FnTypeTC [outty] r fneff (UniConst FastCC) (UniConst FT_Func) levels

        tcLift $ putDocLn $ text "resumebarety: " <$> align (indent 10 (prettyT resumebarety))
        tcLift $ putDocLn $ text "resumebarety: " <$> align (indent 10 (showStructure resumebarety))

        let bindings = extractPatternBindings p
        let ctxbindings = [varbind id ty | (TypedId ty id) <-
                                            TypedId resumebarety resumebareid :
                                            TypedId resumety resumeid : toList bindings]
        let ctx' = prependContextBindings ctx ctxbindings

        tcLift $ putStrLn $ show (contextBindings ctx')

        aguard <- liftMaybe (\g -> tcRho ctx' g (Check boolTypeTC)) guard
        -- TODO use outty for type of resume func
        abody <- tcRho ctx' body expTy
        unify r'p (typeTC abody) [string $ "Failed to unify all branches of case " ++ highlightFirstLineStr (rangeOf rng)]
        return (CaseArm p abody aguard bindings brng)

  abranches <- forM (zip arms ps_outtys) checkBranch

  _ <- subsCheckRho actionThunk (FnTypeTC [] r fneff (UniConst FastCC) (UniConst FT_Func) levels)
                "handler-action"

  mb_xform' <- case mb_xform of
                Nothing -> return Nothing
                Just xform -> do
                  xform' <- inferRho ctx xform "xform"
                  x <- subsCheckRho xform' (FnTypeTC [r] r' effs
                                           (UniConst FastCC) (UniConst FT_Func) levels) "xform"
                  return $ Just x

  matchExp expTy (AnnHandler rng r'p eff actionThunk abranches mb_xform' (resumeid, resumebareid)) "case"

extractPatternBindings :: Pattern t -> Seq (TypedId t)
extractPatternBindings (P_Atom (P_Wildcard    {})) = Seq.empty
extractPatternBindings (P_Atom (P_Bool        {})) = Seq.empty
extractPatternBindings (P_Atom (P_Int         {})) = Seq.empty
extractPatternBindings (P_Atom (P_Variable _ tid)) = Seq.singleton tid
extractPatternBindings (P_Ctor _ _ ps _)  = seqConcatMap extractPatternBindings (Seq.fromList ps)
extractPatternBindings (P_Tuple _ _ ps)   = seqConcatMap extractPatternBindings (Seq.fromList ps)
extractPatternBindings (P_Or    _ _ ps)   = seqConcatMap extractPatternBindings (Seq.fromList ps)
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
  debugDoc $ text "case scrutinee has type " <> prettyT (typeTC ascrutinee)
  debugDoc $ text "metavar for overall type of case is " <> prettyT u
  debugDoc $ text " exp ty is " <> prettyT expTy
  let checkBranch (CaseArm pat body guard _ brng) = do
        let names = epatBoundNames pat
        verifyNamesAreDistinct (rangeOf rng) "case" names

        p <- checkPattern ctx pat (typeTC ascrutinee)
        let bindings = extractPatternBindings p
        let ctxbindings = [varbind id ty | (TypedId ty id) <- toList $ bindings]
        let ctx' = prependContextBindings ctx ctxbindings
        aguard <- liftMaybe (\g -> tcRho ctx' g (Check boolTypeTC)) guard
        abody <- tcRho ctx' body expTy
        unify u (typeTC abody) [string $ "Failed to unify all branches of case "
                               , highlightFirstLineDoc (rangeOf rng)]
        return (CaseArm p abody aguard bindings brng)
  abranches <- forM branches checkBranch
  matchExp expTy (AnnCase rng u ascrutinee abranches) "case"

checkEffectPattern :: Context SigmaTC -> EPattern TypeAST -> TypeTC
                   -> Tc (Pattern TypeTC, TypeTC)
checkEffectPattern ctx pattern ctxTy = case pattern of
  EP_Ctor     r eps ctorName -> do
    case mapSeqLookup ctorName (contextEffectCtorInfo ctx) of
      MSL_Lone (cid, effctor) -> do
        let tyformals = dataCtorDTTyF $ effectCtorAsData effctor
            types     = dataCtorTypes $ effectCtorAsData effctor
            info      = CtorInfo cid (effectCtorAsData effctor)

        sanityCheck (ctorArity cid == List.length eps) $
              T.pack $ "Incorrect pattern arity: expected " ++
              (show $ ctorArity cid) ++ " pattern(s), but got "
              ++ (show $ List.length eps) ++ show (prettySourceRangeInfo r)
        sanityCheck (ctorArity cid == List.length types) $
              T.pack $ "Invariant violated: constructor arity did not match # types!"
              ++ show (prettySourceRangeInfo r)

        --ty@(TyAppTC _ metas) <- generateTypeSchemaForDataType ctx r (ctorTypeName cid)
        ty@(TyAppTC _ metas) <- do
          formals <- mapM (\_ -> newTcUnificationVarTau (T.pack $ "eff-tyformal:" ++ showSourceRangeStr r)) tyformals
          return $ TyAppTC (TyConTC $ ctorTypeName cid) formals
        
        let ktvs = map convertTyFormal tyformals
        ts <- mapM (\ty -> instSigmaWith "eff ctor pattern" ktvs ty metas) types
        ps <- sequence [checkPattern ctx p t | (p, t) <- zip eps ts]

        unify ty ctxTy [string $ "checkEffectPattern:P_Ctor " ++ show cid]
        ty' <- zonkType ty
        tcLift $ putDocLn $ text "ty: " <$> align (indent 10 (prettyT ty))
        tcLift $ putDocLn $ text "ty': " <$> align (indent 10 (prettyT ty'))

        outty' <-  instSigmaWith "eff ctor pattern" ktvs (effectCtorOutput effctor) metas
        tcLift $ putDocLn $ text "outty': " <$> align (indent 10 (prettyT outty'))

        return (P_Ctor r ty ps info, outty' )


      MSL_Missing -> tcFails [string $ "Missing definition for effect $" ++ T.unpack ctorName
                          , highlightFirstLineDoc r]
      _elsewise -> tcFails [string $ "Too many or"
                                  ++ " too few definitions for effect $" ++ T.unpack ctorName]

  _ -> tcFails [text "Effect patterns should start with a data constructor"]

checkPattern :: Context SigmaTC -> EPattern TypeAST -> TypeTC
             -> Tc (Pattern TypeTC)
-- Make sure that each pattern has the proper arity,
-- and record its type given a known type for the context in which
-- the pattern appears.
checkPattern ctx pattern ctxTy = case pattern of
  EP_Wildcard r       -> do return $ P_Atom $ P_Wildcard r ctxTy
  EP_Variable r v     -> do checkSuspiciousPatternVariable r v
                            id <- tcFreshT (evarName v)
                            return $ P_Atom $ P_Variable r (TypedId ctxTy id)
                              where
        checkSuspiciousPatternVariable rng var =
          if T.unpack (evarName var) `elem` ["true", "false"]
          then tcFails [string $ "Error: this matches a variable, not a boolean constant!"
                       , highlightFirstLineDoc rng]
          else return ()

  EP_Bool     r b     -> do let boolexpr = E_BoolAST (annotForRange r) b
                            annbool <- tcRho ctx boolexpr (Check ctxTy)
                            return $ P_Atom $ P_Bool r (typeTC annbool) b
  EP_Int      r str   -> do (AnnLiteral _ ty (LitInt int))
                                      <- typecheckInt (annotForRange r) str
                                                      (Check ctxTy)
                            --tcLift $ putDocLn $ text ("P_Int " ++ str) <+> pretty ctxTy
                            return $ P_Atom $ P_Int r ty int

  -- TODO
  --  * use answer type from EffectCtor when typechecking hander arm resume funcs
  --  * only check for effect ctors at toplevel; nested ctors are data
  --  * merge somehow the CtorInfo and (CtorId, EffectCtor) paths in getCtorInfoForCtor
  EP_Ctor     r eps s -> do
    info@(CtorInfo cid (DataCtor _ tyformals types _repr _lone _crng)) <- getCtorInfoForCtor ctx r s
    sanityCheck (ctorArity cid == List.length eps) $
          T.pack $ "Incorrect pattern arity: expected " ++
          (show $ ctorArity cid) ++ " pattern(s), but got "
          ++ (show $ List.length eps) ++ showSourceRangeStr r
    sanityCheck (ctorArity cid == List.length types) $
          T.pack $ "Invariant violated: constructor arity did not match # types!"
          ++ showSourceRangeStr r

    ty@(TyAppTC _ metas) <-
                        generateTypeSchemaForDataType ctx r (ctorTypeName cid)
    let ktvs = map convertTyFormal tyformals
    ts <- mapM (\ty -> instSigmaWith "ctor pattern" ktvs ty metas) types
    ps <- sequence [checkPattern ctx p t | (p, t) <- zip eps ts]

    debug $ "checkPattern for "   ++ show (prettyT pattern)
    debug $ "*** P_Ctor -  ty   " ++ show (prettyT ty     )
    debug $ "*** P_Ctor -  ty   " ++ show (prettyT ctxTy  )
    debug $ "*** P_Ctor - metas " ++ show (prettyT metas  )
    debug $ "*** P_Ctor - sgmas " ++ show (prettyT ts     )

    unify ty ctxTy [string $ "checkPattern:P_Ctor " ++ show cid]
    return $ P_Ctor r ty ps info

  EP_Or     r eps  -> do
    let (epatFirst : rest) = eps
    let firstNames = epatBoundNames epatFirst
    if firstNames /= []
        then tcFailsMore [text "Subpatterns of an 'or' cannot yet bind variables..."
                        ,highlightFirstLineDoc (rangeOf epatFirst)]
        else return ()
    mapM_ (\epat -> do
      let boundNames = epatBoundNames epat
      if firstNames == boundNames
        then return ()
        else let descNames names =
                    case names of
                      []  -> text "no names were"
                      [x] -> text "the name" <+> text x <+> text "was"
                      _   -> text "the names" <+> hsep (punctuate comma (map text names)) <+> text "were"
                in
              tcFailsMore [text "The subpatterns of an 'or' must provide bindings for the same variable names."
                          ,text "Otherwise, things would go haywire if the scrutinized value matched a branch"
                          ,text "that didn't bind a name used by the body."
                          ,descNames firstNames <+> text "bound by"
                          ,highlightFirstLineDoc (rangeOf epatFirst)
                          ,text "whereas" <+> descNames boundNames <+> text "bound by"
                          ,highlightFirstLineDoc (rangeOf epat)
                          ]) rest
    pats <- mapM (\epat -> checkPattern ctx epat ctxTy) eps
    return $ P_Or r ctxTy pats

  EP_Tuple     r eps  -> do
    (ts, kind) <-
      case ctxTy of
        TupleTypeTC kind ts -> return (ts, kind)
        _ -> do ts <- sequence [newTcUnificationVarTau (T.pack $ "tup" ++ showSourceRangeStr (rangeOf ep)) | ep <- eps]
                kind <- genUnifiableVar
                unify ctxTy (TupleTypeTC kind ts) [text "tuple-pattern"]

                return (ts, kind)
    sanityCheck (eqLen eps ts) $
            T.pack $ "Cannot match pattern against tuple type of "
          ++ "different length." ++ showSourceRangeStr r
    ps <- sequence [checkPattern ctx p t | (p, t) <- zip eps ts]
    return $ P_Tuple r (TupleTypeTC kind ts) ps
 where
    -----------------------------------------------------------------------
    getCtorInfoForCtor :: Context SigmaTC -> SourceRange -> T.Text -> Tc (CtorInfo SigmaTC)
    getCtorInfoForCtor ctx r ctorName = do
      case fmap toList $ Map.lookup ctorName (contextCtorInfo ctx) of
        Just [info] -> return info
        Nothing  -> tcFails [string $ "Missing definition for $" ++ T.unpack ctorName
                            , highlightFirstLineDoc r]
        elsewise -> tcFails [string $ "Typecheck.getCtorInfoForCtor: Too many or"
                                    ++ " too few definitions for $" ++ T.unpack ctorName
                                    ++ "\n\t" ++ show (prettyT elsewise)]

generateTypeSchemaForDataType :: Context SigmaTC -> SourceRange -> DataTypeName -> Tc RhoTC
generateTypeSchemaForDataType ctx r typeName = do
  case mapSeqLookup typeName (contextDataTypes ctx) of
    MSL_Lone dt -> do
          formals <- mapM (\_ -> newTcUnificationVarTau (T.pack $ "dt-tyformal:" ++ showSourceRangeStr r)) (dataTypeTyFormals dt)
          return $ TyAppTC (TyConTC typeName) formals
    MSL_Many _ -> tcFails [string $ "Typecheck.generateTypeSchemaForDataType: Too many"
                        ++ " definitions for $" ++ T.unpack typeName]
    _ -> tcFails [string $ "Typecheck.generateTypeSchemaForDataType: No"
                       ++ " definitions for $" ++ T.unpack typeName]
-- }}}

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

subsCheckTy :: SigmaTC -> SigmaTC -> String -> Tc ()
-- {{{
subsCheckTy sigma1 sigma2@(ForAllTC {}) msg = do
  (skols, rho) <- skolemize sigma2
  debug $ "subsCheckTy deferring to subsCheckRhoTy"
  subsCheckRhoTy sigma1 rho ("subsCheckTy(" ++ msg ++ ")")
  esc_tvs <- getFreeTyVars [sigma1, sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skols
  if null bad_tvs
    then return ()
    else do zonked <- zonkType sigma1
            tcFailsMore [text "Type not polymorphic enough",
                      indent 10 $ prettyT zonked,
                      text "escaping skolems:",
                      indent 10 $ pretty bad_tvs]

subsCheckTy sigma1 rho2 msg = subsCheckRhoTy sigma1 rho2 ("subsCheckTy("++msg++")")

instance Show (AnnExpr TypeTC) where show e = show (prettyT e)

subsCheckRhoTy :: SigmaTC -> RhoTC -> String -> Tc ()
subsCheckRhoTy (ForAllTC ktvs rho) rho2 msg = do -- Rule SPEC
             taus <- genNonSigmaUnificationVarsLike ktvs (\n -> T.pack $ "instSigma type parameter " ++ show n)
             rho1 <- instSigmaWith "subsCheckRhoTy" ktvs rho taus
             subsCheckRhoTy rho1 rho2 msg
subsCheckRhoTy rho1 (FnTypeTC as2 r2 fx2 cc2 ft2 lvls2) msg = unifyFun rho1 (length as2) msg >>= \(as1, r1, fx1, cc1, ft1, lvls1) -> subsCheckFunTy as1 r1 fx1 cc1 ft1 lvls1 as2 r2 fx2 cc2 ft2 lvls2 msg
subsCheckRhoTy (FnTypeTC as1 r1 fx1 cc1 ft1 lvls1) rho2 msg = unifyFun rho2 (length as1) msg >>= \(as2, r2, fx2, cc2, ft2, lvls2) -> subsCheckFunTy as1 r1 fx1 cc1 ft1 lvls1 as2 r2 fx2 cc2 ft2 lvls2 msg
subsCheckRhoTy tau1 tau2 msg -- Rule MONO
     = do
          logged' ("subsCheckRhoTy " ++ show (prettyT (tau1, tau2)) ++ " ;; " ++ msg) $
            unify tau1 tau2 [string $ "subsCheckRhoTy-MONO(" ++ msg ++ ")"]
                            {- ++ [text $ "Tried to unify"
                            ,pretty tau1
                            ,text $ "with"
                            ,pretty tau2] -} -- Revert to ordinary unification
-- }}}

subsCheck :: (AnnExpr SigmaTC) -> SigmaTC -> String -> Tc (AnnExpr SigmaTC)
-- {{{
subsCheck esigma sigma2@(ForAllTC {}) msg = do
  (skols, rho) <- skolemize sigma2
  debug $ "subsCheck skolemized sigma to " ++ show rho ++ " via " ++ show skols
                                            ++ ", now deferring to subsCheckRho"
  _ <- subsCheckRho esigma rho ("subsCheck(" ++ msg ++")")
  let tytc1 = typeTC esigma
  esc_tvs <- getFreeTyVars [tytc1, sigma2]
  esc_tvs1 <- getFreeTyVars [tytc1]
  esc_tvs2 <- getFreeTyVars [sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skols
  if null bad_tvs
    then return ()
    else do tcFailsMore [text "Type not polymorphic enough",
                      indent 10 $ prettyT (typeTC esigma),
                      text "when looking at expression",
                      highlightFirstLineDoc (rangeOf esigma),
                      --text "with pre-skolemization inferred type ",
                      --indent 10 $ pretty tytc0,
                      text "and post-skolemization inferred type ",
                      indent 10 $ prettyT tytc1,
                      text "escaping skolems:",
                      indent 10 $ pretty bad_tvs,
                      text "escaping tvs: ",
                      pretty esc_tvs1,
                      pretty esc_tvs2]
  return esigma

subsCheck _esigma _rho2 _msg = tcFails [text $ "rho passed to subsCheck!"]

subsCheckRho :: AnnExpr SigmaTC -> RhoTC -> String -> Tc (AnnExpr RhoTC)
subsCheckRho esigma rho2 msg = do
  case (typeTC esigma, rho2) of
    (_, ForAllTC {}) -> do tcFails [text $ "violated invariant: sigma passed to subsCheckRho"]
    (ForAllTC {}, _) -> do -- Rule SPEC
        debugIf False $ string $ "subsCheckRho instantiating " ++ show (typeTC esigma)
        erho <- inst esigma msg --("subsCheckRho(" ++ msg ++ ")")
        debugIf False $ string $ "subsCheckRho instantiated to " ++ show (typeTC erho)
        debugIf False $ string $ "subsCheckRho inst. type against " ++ show rho2
        subsCheckRho erho rho2 msg

    (rho1, FnTypeTC as2 r2 fx2 cc2 ft2 lvls2) -> do
        debug $ "subsCheckRho fn 1"
        debugIf False $ text "subsCheckRho1 being called for " <> highlightFirstLineDoc (rangeOf esigma)
        (as1, r1, fx1, cc1, ft1, lvls1) <- unifyFun rho1 (length as2) "sCR1"
        subsCheckFunTy as1 r1 fx1 cc1 ft1 lvls1 as2 r2 fx2 cc2 ft2 lvls2 msg
        return esigma
    (FnTypeTC as1 r1 fx1 cc1 ft1 lvls1, _)    -> do
        debug "subsCheckRho fn 2"
        (as2, r2, fx2, cc2, ft2, lvls2) <- unifyFun rho2 (length as1) "sCR2"
        debug $ "&&&&&& r1: " ++ show r1
        debug $ "&&&&&& r2: " ++ show r2
        subsCheckFunTy as1 r1 fx1 cc1 ft1 lvls1 as2 r2 fx2 cc2 ft2 lvls2 msg
        return esigma
    -- Elide the two FUN rules and subsCheckFun because we're using
    -- shallow, not deep, skolemization due to being a strict language.

    (rho1, _) -> do -- Rule MONO
        logged esigma ("subsCheckRho " ++ show (prettyT (rho1, rho2))) $
            unify rho1 rho2 [string $ "subsCheckRho[" ++ show rho2 ++ "](" ++ msg ++ ")", showStructure esigma] -- Revert to ordinary unification
        return esigma
-- }}}

-- {{{ Helper functions for subsCheckRho to peek inside type constructors
subsCheckFunTy as1 r1 fx1 cc1 ft1 _lvls1 as2 r2 fx2 cc2 ft2 _lvls2 msg = do
        if eqLen as1 as2
          then return ()
          else do msg <- getStructureContextMessage
                  tcFailsMore [text "Function types must have equal-length argument lists"
                              ,msg]
        debug $ "subsCheckFunTy arg: " ++ show as2 ++ " ?<=? " ++ show as1
        mapM_ (\(nth, a2, a1) -> subsCheckTy a2 a1 ("sCFTa[arg " ++ show nth ++ "]("++msg++")"))
              (zip3 [0..] as2 as1)
        debug $ "subsCheckFunTy res: " ++ show r1 ++ " ?<=? " ++ show r2
        subsCheckTy r1 r2 "sCFTr"
        subsCheckTy fx1 fx2 "sCFTfx"
        tcUnifyCC cc1 cc2
        tcUnifyFT ft1 ft2
        -- TODO levels?
        return ()
-- }}}

instSigma :: AnnExpr SigmaTC -> Expected RhoTC -> Tc (AnnExpr RhoTC)
-- Invariant: if the second argument is (Check rho),
-- 	      then rho is in weak-prenex form
instSigma e1 (Check t2) = do {
                             ; debug $ "instSigma " ++ show (typeTC e1) ++ " :?: " ++ show t2
                             ; debug $ "instSigma deferring to subsCheckRho"
                             ; subsCheckRho e1 t2 "instSigma"
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
  case typeTC base of
     ForAllTC ktvs _rho -> do
       taus <- genNonSigmaUnificationVarsLike ktvs (\n -> T.pack $ "inst("++msg++") type parameter " ++ vname base n)
       instWith "inst" (annExprAnnot base) base taus
     _rho -> return base

instWith :: String -> ExprAnnot -> AnnExpr SigmaTC -> [TauTC] -> Tc (AnnExpr RhoTC)
instWith _ _          aexpSigma [] = do
        sanityCheck (isRho $ typeTC aexpSigma)
                     "Tried to instantiate a sigma with no types!"
        return aexpSigma

instWith whereFrom rng aexpSigma taus = do
    instRho <- tryInstSigmaWith whereFrom (typeTC aexpSigma) taus
    return $ E_AnnTyApp rng instRho aexpSigma taus

tryInstSigmaWith whereFrom sigma taus = do
  case sigma of
     ForAllTC ktvs rho -> do let tailKtvs = drop (length taus) ktvs
                             partialTaus <- genNonSigmaUnificationVarsLike tailKtvs (\n -> T.pack $ "tISW type parameter " ++ show n)
                             instSigmaWith whereFrom ktvs rho (taus ++ partialTaus)
     rho               -> return rho

instSigmaWith whereFrom ktvs rho taus = do
    sanityCheck (eqLen taus ktvs)
                (T.pack $ "Arity mismatch in instSigma: can't instantiate "
                ++ show (List.length ktvs) ++ " type variables with "
                ++ show (List.length taus) ++ " types!" ++ "\n"
                ++ "rho: " ++ show rho ++ "\n"
                ++ "ktvs: " ++ show ktvs ++ "\n"
                ++ "taus: " ++ show taus ++ "\n"
                ++ "context: " ++ whereFrom)
    let tyvarsAndTys = List.zip (tyvarsOf ktvs) taus
    tcReplaceQuantifiedVars tyvarsAndTys rho

assocFilterOut :: Eq a => [(a,b)] -> [a] -> [(a,b)]
assocFilterOut lst keys = [(a,b) | (a,b) <- lst, not(List.elem a keys)]

-- Substitute each element of prv with its corresponding element from nxt.
tcReplaceQuantifiedVars :: [(TyVar, TypeTC)] -> TypeTC -> Tc TypeTC
tcReplaceQuantifiedVars prvNextPairs ty =
    let q = tcReplaceQuantifiedVars prvNextPairs in
    case ty of
        TyVarTC  tv _mbk     -> return $ fromMaybe ty $ List.lookup tv prvNextPairs
        MetaTyVarTC m        -> do tvar <- readTcMeta m
                                   case tvar of
                                     Unbound _ -> return ty
                                     BoundTo _ -> repr ty >>= q
        PrimIntTC     {}     -> return $ ty
        TyConTC       {}     -> return $ ty
        TyAppTC con tys      -> do con' <- q con
                                   tys' <- mapM q tys
                                   return $ TyAppTC con' tys'
        RecordTypeTC labels types      -> liftM  (RecordTypeTC labels) (mapM q types)
        TupleTypeTC k  types -> liftM (TupleTypeTC k) (mapM q types)
        RefTypeTC    t       -> liftM RefTypeTC    (q t)
        ArrayTypeTC  t       -> liftM ArrayTypeTC  (q t)
        FnTypeTC  ss t fx cc cs levels -> do
                ss' <- mapM q ss
                t' <- q t
                fx' <- q fx
                levels' <- mkLevels
                return $ FnTypeTC ss' t' fx' cc cs levels' -- TODO unify calling convention?
        ForAllTC  ktvs rho   -> do
                let prvNextPairs' = prvNextPairs `assocFilterOut` (map fst ktvs)
                rho' <- tcReplaceQuantifiedVars prvNextPairs' rho
                return $ ForAllTC  ktvs rho'
        RefinedTypeTC (TypedId t id) e args -> do
          t' <- q t
          return $ RefinedTypeTC (TypedId t' id) e args -- TODO recurse in e?
    
-- }}}

-- {{{
-- This function replaces bound type variables according to the given ctx/map.
-- This is needed to make sure that we can easily distinguish between well-
-- scoped terms and ill-scoped terms, and to ensure that intermediate types
-- are well-formed. If Infer.hs complains about being unable to unify a bound
-- type variable, the culprit may be a missing call to this function somewhere.
resolveType :: ExprAnnot -> Map T.Text TypeTC -> TypeTC -> Tc TypeTC
resolveType annot origSubst origType = go origSubst origType where
 go subst x0 = do
  let q x = go subst x
  x <- repr x0
  case x of
    PrimIntTC   _                  -> return x
    MetaTyVarTC   _                -> return x
    TyVarTC  (SkolemTyVar _ _ _) _  -> return x
    TyVarTC  (BoundTyVar name _sr) _ -> case Map.lookup name subst of
                                         Nothing -> tcFails [string $ "Typecheck.hs: ill-formed type with free bound variable " ++ T.unpack name
                                                            ,text "    " <> text "embedded within type " <> prettyT origType
                                                            ,text "    " <> text "with orig subst " <> prettyT (Map.toList origSubst)
                                                            , highlightFirstLineDoc (rangeOf annot)]
                                         Just ty -> return ty
    RefTypeTC     ty               -> liftM  RefTypeTC    (q ty)
    ArrayTypeTC   ty               -> liftM  ArrayTypeTC  (q ty)
    FnTypeTC    ss t fx cc cs lvls -> do (t':fx':ss') <- mapM q (t:fx:ss)
                                         return $ FnTypeTC  ss' t' fx' cc cs lvls
    TyConTC    nam                 -> return $ TyConTC nam
    TyAppTC    con types           -> liftM2 TyAppTC (q con) (mapM q types)
    RecordTypeTC labels types      -> liftM  (RecordTypeTC labels) (mapM q types)
    TupleTypeTC  kind types        -> liftM  (TupleTypeTC kind) (mapM q types)
    RefinedTypeTC v e args -> do v' <- fmapM_TID q v
                                 return $ RefinedTypeTC v' e args
    ForAllTC      ktvs rho         -> liftM (ForAllTC  ktvs) (go subst' rho)
                                       where
                                        subst' = foldl' ins subst ktvs
                                        ins m (tv@(BoundTyVar nm _sr), k) = Map.insert nm (TyVarTC tv (UniConst k)) m
                                        ins _     (SkolemTyVar {},    _k) = error "ForAll bound a skolem!"

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
                                 (map (\tv@(SkolemTyVar _ _ k) -> TyVarTC tv (UniConst k)) skolems)
     rho' <- tcReplaceQuantifiedVars tyvarsAndTys rho
     return (skolems, rho')
skolemize ty = return ([], ty)
-- }}}

getFreeTyVars :: [TypeTC] -> Tc [TyVar]
-- {{{
getFreeTyVars xs = do tvs <- concatMapM (go []) xs
                      return $ Set.toList (Set.fromList $ tvs)
                 where
  go :: [TyVar] -> SigmaTC -> Tc [TyVar]
  go bound x =
    case x of
        PrimIntTC         {} -> return []
        TyConTC           {} -> return []
        TyAppTC con types    -> concatMapM (go bound) (con:types)
        RecordTypeTC _labels types -> concatMapM (go bound) types
        TupleTypeTC _k types     -> concatMapM (go bound) types
        FnTypeTC ss r fx  _ _ _levels   -> concatMapM (go bound) (r:fx:ss)
        ForAllTC  tvs rho        -> go (tyvarsOf tvs ++ bound) rho
        TyVarTC   tv  _mbk       -> return $ if tv `elem` bound then [] else [tv]
        MetaTyVarTC  {}          -> do t <- repr x
                                       case t of
                                         MetaTyVarTC _ -> return []
                                         _ -> go bound t
        RefTypeTC    ty          -> (go bound) ty
        ArrayTypeTC  ty          -> (go bound) ty
        RefinedTypeTC v _e _args -> (go bound) (tidType v) -- TODO handle tyvars in expr/args?
-- }}}

-- {{{ Well-formedness checks
-- The judgement   G |- T
tcTypeWellFormed :: String -> Context SigmaTC -> TypeTC -> Tc ()
tcTypeWellFormed msg ctx typ = do
  let q = tcTypeWellFormed msg ctx
  case typ of
        PrimIntTC      {}     -> return ()
        MetaTyVarTC m  -> do tvar <- readTcMeta m
                             case tvar of
                               Unbound _ -> return ()
                               BoundTo t -> q t
        TyConTC "Float64" -> return ()
        TyConTC "Float32" -> return ()
        TyConTC nm -> case Map.lookup nm (contextDataTypes ctx) of
                                   Just  _ -> return ()
                                   Nothing -> tcFails [string $ "Unknown type "
                                                        ++ T.unpack nm ++ " " ++ msg]
        TyAppTC con types     -> mapM_ q (con:types)
        RecordTypeTC _labels types -> mapM_ q types
        TupleTypeTC _k types  -> mapM_ q types
        FnTypeTC  ss r fx _ _ _levels -> mapM_ q (r:fx:ss)
        RefTypeTC     ty      -> q ty
        ArrayTypeTC   ty      -> q ty
        RefinedTypeTC v _e  _ -> q (tidType v)
        ForAllTC   tvs rho    -> tcTypeWellFormed msg (extendTyCtx ctx (Seq.fromList tvs)) rho
        TyVarTC  (SkolemTyVar {}) _mbk -> return ()
        TyVarTC  tv@(BoundTyVar _ _) mbk ->
                 case seqAssocLookup tv (contextTypeBindings ctx) of
                   Nothing -> tcFails [string $ "Unbound type variable "
                                           ++ show tv ++ " " ++ msg]
                   Just kind -> do --tcLift $ putStrLn $ "giving " ++ show tv ++ " kind " ++ show kind
                                   tcUnifyKinds mbk (UniConst kind)

tcContext :: Context TypeTC -> Context TypeAST -> Tc (Context SigmaTC)
tcContext emptyCtx ctxAST = do
  sanityCheck (Map.null $ localTypeBindings ctxAST)
        "Expected to start typechecking with an empty lexical type environment"
  sanityCheck (null $ contextTypeBindings ctxAST)
        "Expected to start typechecking with an empty lexical type environment"

  debug2 "converting Context TypeAST to Context TypeTC"
  --debug2 (pretty ctxAST)
  ctx <- liftContextM (tcType emptyCtx) ctxAST
  debug2 "done converting Context TypeAST to Context TypeTC"

  -- For now, we disallow mutually recursive data types
  let checkDataType :: (T.Text, (Seq (DataType TypeTC))) -> Tc ()
      checkDataType (nm, dts) = do {
    case toList dts of
      [dt] -> do
         sanityCheck (nm == typeFormalName (dataTypeName dt))
                     ("Data type name mismatch for " `T.append` nm)
         let extctx = extendTyCtx ctx (Seq.fromList $
                        map convertTyFormal $ dataTypeTyFormals dt)
         mapM_ (tcDataCtor nm extctx) (dataTypeCtors dt)
      many -> tcFails $ [text "Data type name" <+> text nm
                        <+> text "didn't map to a single data type!"
                       ,text "Conflicting definitions:"] ++
                       map (indent 2) (numberedParenListDocs
                          (map (highlightFirstLineDoc . dataTypeRange) many))
  }

  debug2 (show (Map.keys $ contextDataTypes ctx))
  debug2 "Checking data types"
  mapM_ checkDataType (Map.toList $ contextDataTypes ctx)
  debug2 "Checking data ctors"

  let checkDataCtors :: (Seq (DataType TypeTC)) -> Tc ()
      checkDataCtors dts = do
        let ctorsOf dt = [(ctor, dt) | ctor <- dataTypeCtors dt]
        let ctors = concat $ fmap ctorsOf dts
        let dups = collectDuplicatesBy (\(ctor,_dt) -> dataCtorName ctor) ctors
        let complainAbout ctorsWithDts = do
              [text "These data type constructors have identical names: "]
              ++ map (indent 2) (numberedParenListDocs
                         [highlightFirstLineDoc (dataCtorRange ctor) | (ctor, _dt) <- ctorsWithDts])

        if null dups
          then return ()
          else tcFails (concatMap complainAbout dups)

  checkDataCtors (concatSeqList (Map.elems $ contextDataTypes ctx))

  return ctx

concatSeqList :: [Seq x] -> Seq x
concatSeqList [] = Seq.empty
concatSeqList xs = List.foldl1' (Seq.><) xs

numberedParenListDocs docs =
  [pretty n <> text ")" <+> hang (length (show n) + 2) d | (d, n) <- zip docs [1 :: Int ..]]

tcDataCtor :: T.Text -> Context SigmaTC -> DataCtor TypeTC -> Tc ()
tcDataCtor dtname ctx (DataCtor nm _tyfs tys _repr _lone _rng) = do
  let msg = "in field of data constructor " ++ T.unpack nm ++ " of type " ++ T.unpack dtname
  mapM_ (tcTypeWellFormed msg ctx) tys
-- }}}

-- {{{ Miscellaneous helpers.

substExprsForRefinedArgs raw argsTys argsExprs = do
  let argExprPairs = [ (tidIdent v,e) | (RefinedTypeTC v _ _, e) <- zip argsTys argsExprs]
  let subst = Map.fromList argExprPairs
  if null subst
    then raw
    else tcSubst subst raw

tcSubst subst typ = go typ
  where go typ = case typ of
            PrimIntTC  {}           -> typ
            TyConTC    {}           -> typ
            TyAppTC  con types      -> TyAppTC (go con) (map go types)
            RecordTypeTC labels types -> RecordTypeTC labels (map go types)
            TupleTypeTC  k  types   -> TupleTypeTC k (map go types)
            FnTypeTC  ss r fx cc fp levels -> FnTypeTC (map go ss) (go r) (go fx) cc fp levels
            ForAllTC  tvs rho       -> ForAllTC tvs (go rho)
            RefTypeTC     ty        -> RefTypeTC (go ty)
            ArrayTypeTC   ty        -> ArrayTypeTC (go ty)
            TyVarTC   _tv _k        -> typ -- TODO attach delayed subst?
            MetaTyVarTC   _m        -> typ
            RefinedTypeTC v e ids   ->
              RefinedTypeTC v (annSubst subst e) (ids `butnot` Map.keys subst)

annSubst subst expr = go expr
  where gt :: TypeTC -> TypeTC
        gt = tcSubst subst
        gf (Fn v vs e rec annot) = Fn (fmap gt v) (map (fmap gt) vs) (go e) rec annot
        gle = fmap go
        gb (CaseArm pat body guard vs rng) =
            CaseArm (gp pat) (go body) (fmap go guard) vs rng
        gp = fmap gt
        gai = fmap go
        go expr = do
          case expr of
            E_AnnFn annFn                        -> E_AnnFn (gf annFn)
            AnnCall _rng ty b exprs ca           -> AnnCall _rng (gt ty) (go b) (map go exprs) ca
            AnnAppCtor _rng ty cid exprs         -> AnnAppCtor _rng (gt ty) cid (map go exprs)
            AnnIf        _rng ty a b c           -> AnnIf        _rng (gt ty) (go a) (go b) (go c)
            AnnLetVar    _rng id a b             -> AnnLetVar    _rng id (go a) (go b)
            AnnLetRec    _rng ids exprs e        -> AnnLetRec    _rng ids (map go exprs) (go e)
            AnnLetFuns   _rng ids fns e          -> AnnLetFuns   _rng ids (map gf fns) (go e)
            AnnAlloc     _rng ty a amr           -> AnnAlloc     _rng (gt ty) (go a) amr
            AnnDeref     _rng ty a               -> AnnDeref     _rng (gt ty) (go a)
            AnnStore     _rng ty a b             -> AnnStore     _rng (gt ty) (go a) (go b)
            AnnAllocArray _rng tyA e tyB amr zi  -> AnnAllocArray _rng (gt tyA) (go e) (gt tyB) amr zi
            AnnArrayLit  _rng ty exprs           -> AnnArrayLit  _rng (gt ty) (map gle exprs)
            AnnArrayRead _rng ty ari             -> AnnArrayRead _rng (gt ty) (gai ari)
            AnnArrayPoke _rng ty ari c           -> AnnArrayPoke _rng (gt ty) (gai ari) (go c)
            AnnRecord _rng ty labels exprs       -> AnnRecord    _rng (gt ty) labels (map go exprs)
            AnnTuple _rng ty kind exprs          -> AnnTuple     _rng (gt ty) kind (map go exprs)
            AnnHandler _rng ty fx e bs mbe resid -> AnnHandler   _rng (gt ty) (gt fx) (go e) (map gb bs) (fmap go mbe) resid
            AnnCase _rng ty e bs                 -> AnnCase      _rng (gt ty) (go e) (map gb bs)
            E_AnnTyApp _rng ty a argtys          -> E_AnnTyApp   _rng (gt ty) (go a) (map gt argtys)
            AnnLiteral _rng ty lit               -> AnnLiteral   _rng (gt ty) lit
            AnnPrimitive _rng ty prim            -> AnnPrimitive _rng (gt ty) prim
            AnnKillProcess _rng ty txt           -> AnnKillProcess _rng (gt ty) txt
            E_AnnVar _rng (v, _mcid)             ->
              case Map.lookup (tidIdent v) subst of
                Nothing -> expr
                Just e  -> e
            AnnCompiles  _rng _ty (CompilesResult (OK      e)) ->
             AnnCompiles _rng _ty (CompilesResult (OK $ go e))
            AnnCompiles  {} -> expr

vname (E_AnnVar _rng (av, _)) n = show n ++ " for " ++ T.unpack (identPrefix $ tidIdent av)
vname _                       n = show n

varbind id ty = TermVarBinding (identPrefix id) (TypedId ty id, Nothing)
bindingForVar (TypedId ty id) = varbind id ty

genNonSigmaUnificationVarsLike :: [(a,Kind)] -> (Int -> T.Text) -> Tc [TypeTC]
genNonSigmaUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVar_ (nsConstraintForKind k) (namegen n) | ((_, k), n) <- zip spine [1..]]

nsConstraintForKind KindEffect = MTVEffect
nsConstraintForKind _          = MTVTau

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
        dups -> tcFails [string $ "Error when checking " ++ name ++ ": "
                              ++ "had duplicated bindings: " ++ show dups
                        , highlightFirstLineDoc rng]

verifyNonOverlappingBindings :: SourceRange -> String -> [ContextBinding ty] -> Tc ()
verifyNonOverlappingBindings rng name binders = do
    verifyNamesAreDistinct rng name (map bindingName binders)

tyvarsOf ktyvars = map (\(tv,_k) -> tv) ktyvars

isRho (ForAllTC _ _) = False
isRho _              = True

instance Show a => Show (Expected a) where
  show (Infer _) = "<infer>"
  show (Check a) = show a

instance (PrettyT a) => PrettyT (Expected a) where
  prettyT (Infer _) = text "<infer>"
  prettyT (Check a) = prettyT a

instance PrettyT ty => PrettyT (CtorInfo ty) where
  prettyT (CtorInfo cid dc) = parens (text "CtorInfo" <+> pretty cid <+> prettyT dc)

instance PrettyT ty => PrettyT (DataCtor ty) where
  prettyT (DataCtor name _tyformals _ctortyargs _repr _lone _range) =
        parens (text "DataCtor" <+> text name)

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

instance Expr (TypedId TypeAST) where freeVars (TypedId ty id) = freeVars ty `butnot` freeVars id
instance Expr Ident             where freeVars id = [identPrefix id]

-- The free-variable determination logic here is tested in
--      test/bootstrap/testcases/rec-fn-detection
instance Expr (ExprAST TypeAST) where
  freeVars e = case e of
    E_LetAST _rng (TermBinding v b) e ->
                                freeVars b ++ (freeVars e `butnot` [evarName v])
    E_LetRec _rng nest _ -> concatMap freeVars (childrenOf e) `butnot`
                                          [evarName v | TermBinding v _ <- nest]
    E_Case _rng e arms   -> freeVars e ++ (concatMap caseArmFreeVars arms)
    E_FnAST _rng f       -> let typdvars  = concatMap refiVars (map tidType $ fnFormals f) in
                            let typmvars  = concatMap freeVars (map tidType $ fnFormals f) in
                            let bodyvars  = freeVars (fnAstBody f) in
                            let boundvars = map (identPrefix.tidIdent) (fnFormals f) in
                            (typmvars `butnot` typdvars) ++ (bodyvars `butnot` boundvars)
    E_VarAST _rng v      -> freeVars (evarMaybeType v) ++ [evarName v]
    E_TyApp   _ e tys    -> freeVars e ++ concatMap freeVars tys
    E_TyCheck _ e ty     -> freeVars e ++ freeVars ty
    _                    -> concatMap freeVars (childrenOf e)

refiVars (RefinedTypeAST nm _ _) = [T.pack nm]
refiVars _ = []

instance Expr TypeAST where
  freeVars typ = case typ of
        PrimIntAST            {} -> []
        TyConAST              {} -> []
        TyAppAST          con types -> concatMap freeVars (con:types)
        RecordTypeAST    _ls  types -> concatMap freeVars types
        TupleTypeAST     _k   types -> concatMap freeVars types
        FnTypeAST    s t fx _cc _cs -> concatMap freeVars (t:fx:s)
        ForAllAST  _tvs rho      -> freeVars rho
        TyVarAST   {}            -> []
        RefTypeAST    ty         -> freeVars ty
        ArrayTypeAST  ty         -> freeVars ty
        RefinedTypeAST  nm ty e  -> freeVars ty ++ (freeVars e `butnot` [T.pack nm])
        MetaPlaceholderAST    {} -> []

typeTC :: AnnExpr TypeTC -> TypeTC
typeTC = typeOf

fnTypeShallow :: Context TypeTC -> FnAST TypeAST -> Tc TypeTC
fnTypeShallow ctx f = tcTypeAndResolve ctx fnTyAST (fnAstAnnot f)
  where
   fnTyAST0 = FnTypeAST (map tidType $ fnFormals f)
                        (MetaPlaceholderAST MTVSigma  ("ret type for " ++ (T.unpack $ fnAstName f)))
                        (MetaPlaceholderAST MTVEffect ("effectvar," ++ (T.unpack $ fnAstName f)))
                        FastCC
                        FT_Func
   fnTyAST = case fnTyFormals f of
                 [] -> fnTyAST0
                 tyformals -> ForAllAST (map convertTyFormal tyformals) fnTyAST0
-- }}}

-- {{{ Debug helpers
tcVERBOSE = False

dbgCalls = False
dbgVar   = False
dbgQuant = False
dbgSigma = False

debugIf c ~d = when c (tcLift $ putDocLn d)

debug    ~s = do when tcVERBOSE (tcLift $ putStrLn s)
debug2   ~s = do when tcVERBOSE (tcLift $ putStrLn s)
debugDoc ~d = do when tcVERBOSE (tcLift $ putDocLn d)
debugDoc2 ~d = do when tcVERBOSE (tcLift $ putDocLn d)
debugDoc3 ~d = do when tcVERBOSE (tcLift $ putDocLn d)

logged'' _msg action = do
  --tcLift $ putStrLn $ "{ " ++ _msg
  rv <- action
  --tcLift $ putStrLn $ "} :: " ++ show (pretty $ typeTC rv)
  return rv

logged' _msg action = do
  --tcLift $ putStrLn $ "{ " ++ _msg
  rv <- action
  --tcLift $ putStrLn $ "}"
  return rv

logged _expr _msg action = do
  --tcLift $ putStrLn $ "{ " ++ _msg
  rv <- action
  --tcLift $ putStrLn $ "} :: " ++ show (pretty $ typeTC _expr)
  return rv
-- }}}
