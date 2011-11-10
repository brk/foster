-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.Typecheck(typecheck) where

import List(length, zip)
import Control.Monad(liftM, forM_, forM)

import qualified Data.Text as T(Text, pack, unpack)
import qualified Data.Map as Map(lookup)

import Foster.Base
import Foster.Kind
import Foster.TypeAST
import Foster.ExprAST
import Foster.AnnExpr
import Foster.Infer
import Foster.Context
import Foster.TypecheckInt(sanityCheck, typecheckInt)
import Foster.Output(out, OutputOr(Errors), outToString)

-----------------------------------------------------------------------

typecheck :: Context TypeAST -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheck ctx expr maybeExpTy =
  tcWithScope expr $ do
    annexpr <- case expr of
        E_IfAST rng a b c              -> typecheckIf   ctx rng a b c maybeExpTy
        E_FnAST f                      -> typecheckFn   ctx f maybeExpTy
        E_IntAST rng txt               -> typecheckInt rng txt
        E_LetRec rng bindings e mt     -> typecheckLetRec ctx rng bindings e mt
        E_LetAST rng binding  e mt     -> typecheckLet   ctx rng binding e mt
        E_TupleAST (TupleAST rng exps) -> typecheckTuple ctx rng exps maybeExpTy
        E_VarAST rng v                 -> typecheckVar   ctx rng (evarName v)
        E_TyApp  rng e t               -> typecheckTyApp ctx rng e t maybeExpTy
        E_Case   rng a branches        -> typecheckCase  ctx rng a branches maybeExpTy
        E_CallAST rng base argtup      -> typecheckCall  ctx rng base
                                                (E_TupleAST argtup) maybeExpTy
        E_AllocAST rng a               -> typecheckAlloc ctx rng a maybeExpTy

        E_DerefAST rng a -> do
          ea <- typecheck ctx a Nothing -- TODO: match maybeExpTy?
          case typeAST ea of
            RefTypeAST t -> return (AnnDeref rng t ea)
            other        -> tcFails [out $ "Expected deref-ed expr "
                                     ++ "to have ref type, had " ++ show other ++ show rng]

        --  G |- e1 ::: tau
        --  G |- e2 ::: Ref tau
        --  --------------------
        --  G |- e1 >^ e2 ::: ()
        E_StoreAST rng e1 e2 -> do
          u_slot <- newTcUnificationVar $ "slot_type"
          u_expr <- newTcUnificationVar $ "expr_type"
          a2 <- typecheck ctx e2 (Just $ RefTypeAST u_slot)
          a1 <- typecheck ctx e1 (Just $            u_expr)
          equateTypes    u_slot                    u_expr    (Just "Store expression")
          equateTypes (typeAST a2) (RefTypeAST (typeAST a1)) (Just "Store expression")
          return (AnnStore rng a1 a2)

        E_SeqAST rng a b -> do
            ea <- typecheck ctx a Nothing --(Just TypeUnitAST)
            id <- tcFresh ".seq"
            eb <- typecheck ctx b maybeExpTy
            return (AnnLetVar rng id ea eb)

        E_BoolAST rng b ->
          case maybeExpTy of
            Nothing -> return (AnnBool rng b)
            Just  t | t == fosBoolType
                    -> return (AnnBool rng b)
            Just  t -> tcFails [out $ "Unable to check Bool constant in context"
                                   ++ " expecting non-Bool type " ++ show t
                                   ++ showSourceRange rng]
        E_UntilAST rng cond body -> do
                acond <- typecheck ctx cond (Just fosBoolType)
                abody <- typecheck ctx body Nothing
                equateTypes (typeAST acond) fosBoolType
                      (Just "E_Until: type of until conditional wasn't boolean")
                return $ AnnUntil rng (TupleTypeAST []) acond abody

        -- a[b]
        E_ArrayRead rng a b -> do
                ta <- typecheck ctx a Nothing
                tb <- typecheck ctx b Nothing
                typecheckArrayRead rng ta (typeAST ta) tb maybeExpTy

        -- a >^ b[c]
        E_ArrayPoke rng a b c -> do
                ta <- typecheck ctx a Nothing
                tb <- typecheck ctx b (Just $ ArrayTypeAST (typeAST ta))
                tc <- typecheck ctx c Nothing
                typecheckArrayPoke rng ta tb (typeAST tb) tc maybeExpTy

        E_CompilesAST rng Nothing ->
                return $ AnnCompiles rng (CompilesResult $
                                                   Errors [out $ "parse error"])
        E_CompilesAST rng (Just e) -> do
                outputOrE <- tcIntrospect (typecheck ctx e Nothing)
                return $ AnnCompiles rng (CompilesResult outputOrE)

    -- If the context provided an expected type,
    -- make sure it unifies with the actual type we computed!
    case maybeExpTy of
        Nothing -> return ()
        Just expTy -> equateTypes (typeAST annexpr) expTy
                       (Just $ outToString (textOf expr 0)
                               ++ "\n\t\thas type: " ++ (show $ typeAST annexpr)
                               ++ "\n\t\texpected: " ++ (show $ expTy)
                               ++ show (rangeOf expr))
    return annexpr

-----------------------------------------------------------------------
typecheckAlloc ctx rng a maybeExpTy = do
    let expTy = case maybeExpTy of Just (RefTypeAST t) -> Just t
                                   Just _              -> Nothing
                                   Nothing             -> Nothing
    ea <- typecheck ctx a expTy
    return (AnnAlloc rng ea)
-----------------------------------------------------------------------
-- Resolve the given name as either a variable or a primitive reference.
typecheckVar ctx rng name =
  case termVarLookup name (contextBindings ctx) of
    Just (TypedId t id) -> return $ E_AnnVar rng (TypedId t id)
    Nothing   ->
      case termVarLookup name (primitiveBindings ctx) of
        Just avar -> return $ AnnPrimitive rng avar
        Nothing   -> do msg <- getStructureContextMessage
                        tcFails [out $ "Unknown variable " ++ T.unpack name
                                 ++ showSourceRange rng
                                 ++ "ctx: "++ show (contextBindings ctx)
                                 ++ "\nhist: " , msg]
-----------------------------------------------------------------------

--  G         |- e1 ::: t1
--  G{x:::t1} |- e2 ::: t2
--  ----------------------------
--  G |- let x = e1 in e2 ::: t2
typecheckLet ctx0 rng (TermBinding v e1) e2 mt = do
-- {{{
    sanityCheck (notRecursive boundName e1) errMsg
    id     <- tcFreshT boundName
    a1     <- typecheck     ctx0 e1 maybeVarType
    let v   = TypedId (typeAST a1) id
    let ctx = prependContextBindings ctx0 [bindingForVar v]
    a2     <- typecheck     ctx  e2 mt
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

-----------------------------------------------------------------------

{-
  rec a = body_a;
      b = body_b;
      ...;
   in e end
-}
-- {{{
typecheckLetRec :: Context TypeAST -> SourceRange -> [TermBinding]
                -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheckLetRec ctx0 rng bindings e mt = do
    verifyNonOverlappingVariableNames rng "rec" (map termBindingName bindings)
    -- Generate unification variables for the overall type of
    -- each binding.
    unificationVars <- sequence [newTcUnificationVar $ T.unpack $
                                  "letrec_" `prependedTo` (evarName v)
                                | (TermBinding v _) <- bindings]
    ids <- sequence [tcFreshT (evarName v) | (TermBinding v _) <- bindings]
    -- Create an extended context for typechecking the bindings
    let ctxBindings = map (uncurry varbind) (zip ids unificationVars)
    let ctx = prependContextBindings ctx0 ctxBindings

    -- Typecheck each binding
    tcbodies <- forM (zip unificationVars bindings) $
       (\(u, TermBinding v b) -> do
           b' <- typecheck ctx b (evarMaybeType v) -- or (Just $ MetaTyVar u)?
           equateTypes u(typeAST b')
                       (Just $ "recursive binding " ++ T.unpack (evarName v))
           return b'
       )

    -- Typecheck the body as well
    e' <- typecheck ctx e mt

    let fns = [f | (E_AnnFn f) <- tcbodies]
    return $ AnnLetFuns rng ids fns e'
-- }}}

varbind id ty = TermVarBinding (identPrefix id) (TypedId ty id)

typecheckCase :: Context TypeAST -> SourceRange -> ExprAST
              -> [(EPattern, ExprAST)] -> Maybe TypeAST -> Tc AnnExpr
-- {{{
typecheckCase ctx rng scrutinee branches maybeExpTy = do
  -- (A) The expected type applies to the branches,
  -- not to the scrutinee.
  -- (B) Each pattern must check against the scrutinee type.
  -- (C) Each branch must check against the expected type,
  --  as well as successfully unify against the overall type.

  ascrutinee <- typecheck ctx scrutinee Nothing
  u <- newTcUnificationVar "case"
  let checkBranch (pat, body) = do
      p <- checkPattern pat
      bindings <- extractPatternBindings p (typeAST ascrutinee)
      verifyNonOverlappingVariableNames rng "case"
                                        [v | (TermVarBinding v _) <- bindings]
      abody <- typecheck (prependContextBindings ctx bindings) body maybeExpTy
      equateTypes u (typeAST abody)
                   (Just $ "Failed to unify all branches of case " ++ show rng)
      return (p, abody)
  abranches <- forM branches checkBranch
  return $ AnnCase rng u ascrutinee abranches
 where
    checkPattern :: EPattern -> Tc Pattern
    -- Make sure that each pattern has the proper arity.
    checkPattern p = case p of
      EP_Wildcard r   -> do return $ P_Wildcard r
      EP_Bool r b     -> do return $ P_Bool r b
      EP_Variable r v -> do id <- tcFreshT (evarName v)
                            return $ P_Variable r id
      EP_Int r str    -> do annint <- typecheckInt r str
                            return $ P_Int  r (aintLitInt annint)
      EP_Ctor r eps s -> do (CtorInfo cid _) <- getCtorInfoForCtor s
                            sanityCheck (ctorArity cid == List.length eps) $
                              "Incorrect pattern arity: expected " ++
                              (show $ ctorArity cid) ++ " pattern(s), but got "
                              ++ (show $ List.length eps) ++ show r
                            ps <- mapM checkPattern eps
                            return $ P_Ctor r ps cid
      EP_Tuple r eps  -> do ps <- mapM checkPattern eps
                            return $ P_Tuple r ps
    -----------------------------------------------------------------------

    emptyContext :: Context ty
    emptyContext = Context [] [] True []

    getCtorInfoForCtor :: T.Text -> Tc (CtorInfo TypeAST)
    getCtorInfoForCtor ctorName = do
      ctorInfos <- tcGetCtorInfo
      case Map.lookup ctorName ctorInfos of
        Just [info] -> return info
        elsewise -> tcFails [out $ "Typecheck.getCtorInfoForCtor: Too many or"
                                    ++ " too few definitions for $" ++ T.unpack ctorName
                                    ++ "\n\t" ++ show elsewise]

    -----------------------------------------------------------------------

    -- Recursively match a pattern against a type and extract the (typed)
    -- binders introduced by the pattern.
    extractPatternBindings :: Pattern -> TypeAST -> Tc [ContextBinding TypeAST]

    extractPatternBindings (P_Wildcard _   ) _  = return []
    extractPatternBindings (P_Variable _ id) ty = return [varbind id ty]

    -- TODO shouldn't ignore the _ty here -- bug when ctors from different types listed.
    extractPatternBindings (P_Ctor _ pats (CtorId _ ctorName _ _)) _ty = do
      CtorInfo _ (DataCtor _ _ types) <- getCtorInfoForCtor (T.pack ctorName)
      bindings <- sequence [extractPatternBindings p t | (p, t) <- zip pats types]
      return $ concat bindings

    extractPatternBindings (P_Bool r v) ty = do
      _ae <- typecheck emptyContext (E_BoolAST r v) (Just ty)
      -- literals don't bind anything, but we still need to check
      -- that we do not try matching e.g. a bool against an int.
      return []

    extractPatternBindings (P_Int r litint) ty = do
      _ae <- typecheck emptyContext (E_IntAST r (litIntText litint)) (Just ty)
      -- literals don't bind anything, but we still need to check
      -- that we do not try matching e.g. a bool against an int.
      return []

    extractPatternBindings (P_Tuple _rng [p]) ty = extractPatternBindings p ty
    extractPatternBindings (P_Tuple  rng ps)  ty =
       case ty of
         TupleTypeAST ts ->
            (if List.length ps == List.length ts
              then do bindings <- sequence [extractPatternBindings p t | (p, t) <- zip ps ts]
                      return $ concat bindings
              else tcFails [out $ "Cannot match pattern against tuple type"
                                  ++ " of different length."])
         _else  -> tcFails [out $ "Cannot check tuple pattern"
                                  ++ " against non-tuple type " ++ show ty
                                  ++ showSourceRange rng]
-- }}}

-----------------------------------------------------------------------

typecheckIf ctx rng a b c maybeExpTy = do
    ea <- typecheck ctx a (Just fosBoolType)
    eb <- typecheck ctx b maybeExpTy
    ec <- typecheck ctx c maybeExpTy
    equateTypes (typeAST ea) fosBoolType  (Just "IfAST: type of conditional wasn't boolean")
    equateTypes (typeAST eb) (typeAST ec) (Just "IfAST: types of branches didn't match")
    return (AnnIf rng (typeAST eb) ea eb ec)

-----------------------------------------------------------------------

listize (TupleTypeAST tys) = tys
listize ty                 = [ty]

tyvarsOf ktyvars = map (\(tv,_) -> TyVarAST tv) ktyvars

kindCheckSubsumption :: ((TyVar, Kind), TypeAST) -> Tc ()
kindCheckSubsumption ((tv, kind), ty) =
  case (kindOfTypeAST ty, kind) of
    (KindAnySizeType, KindAnySizeType)   -> return ()
    (KindPointerSized, KindPointerSized) -> return ()
    -- It's OK to give a pointer-sized type when any size is expected.
    (KindPointerSized, KindAnySizeType)  -> return ()
    -- It's not OK to give an unboxed type when a boxed type is required.
    (KindAnySizeType, KindPointerSized)  ->
      tcFails [out $ "Kind mismatch:\n"
                  ++ "cannot instantiate type variable " ++ show tv ++ " of kind " ++ show kind
                  ++ "\nwith type " ++ show ty ++ " of kind " ++ show (kindOfTypeAST ty)]

-- G |- e ::: forall a1..an, rho
-- ------------------------------------------
-- G |- e :[ t1..tn ]  ::: rho{t1..tn/a1..an}

typecheckTyApp ctx rng a t _maybeExpTyTODO = do
-- {{{
    let tys = listize t
    ea <- typecheck ctx a Nothing
    case (typeAST ea) of
      ForAllAST ktyvars rho -> do
        sanityCheck (List.length tys == List.length ktyvars)
                    "typecheckTyApp: arity mismatch"
        let tyvarsAndTys = List.zip (tyvarsOf ktyvars) tys
        mapM_ kindCheckSubsumption (List.zip ktyvars tys)
        return $ E_AnnTyApp rng (parSubstTy tyvarsAndTys rho) ea t
      MetaTyVar _ -> do
        tcFails [out $ "Cannot instantiate unknown type of term:"
                ,out $ highlightFirstLine $ rangeOf ea
                ,out $ "Try adding an explicit type annotation."
                ]
      _othertype ->
        tcFails [out $ "Cannot apply type args to expression of"
                   ++ " non-ForAll type "]
-- }}}

-----------------------------------------------------------------------

-- G |- e1 ::: Array t
-- ---------------------  e2 ::: t2 where t2 is a word-like type
-- G |- e1 [ e2 ]  ::: t
typecheckArrayRead :: SourceRange -> AnnExpr -> TypeAST -> AnnExpr -> Maybe TypeAST -> Tc AnnExpr
-- {{{
typecheckArrayRead rng _base (TupleTypeAST _) (AnnInt {}) _maybeExpTy =
    tcFails [out $ "ArrayReading tuples is not allowed;"
                ++ " use pattern matching instead!" ++ highlightFirstLine rng]

typecheckArrayRead rng base (ArrayTypeAST t) i@(AnnInt {}) (Just expTy) = do
    equateTypes t expTy (Just "arrayread[int] expected type")
    -- TODO make sure i is not negative or too big
    return (AnnArrayRead rng t base i)

typecheckArrayRead rng base (ArrayTypeAST t) i@(AnnInt {}) Nothing = do
    -- TODO make sure i is not negative or too big
    return (AnnArrayRead rng t base i)

-- base[aiexpr]
typecheckArrayRead rng base (ArrayTypeAST t) aiexpr maybeExpTy = do
    -- TODO check aiexpr type is compatible with Word
    equateTypes t (typeAST aiexpr) (Just "arrayread type")
    case maybeExpTy of
      Nothing -> return ()
      Just expTy -> equateTypes t expTy (Just "arrayread expected type")

    return (AnnArrayRead rng t base aiexpr)

typecheckArrayRead rng _base baseType index maybeExpTy =
    tcFails [out $ "Unable to arrayread expression of type " ++ show baseType
                ++ " with expression " ++ show index
                ++ " (context expected type " ++ show maybeExpTy ++ ")"
                ++ highlightFirstLine rng]
-- }}}

-----------------------------------------------------------------------

-- G |-  c   ::: t
-- G |- b[e] ::: Array t
-- ---------------------
-- G |- c >^ b[e] ::: ()
typecheckArrayPoke rng c base (ArrayTypeAST t) aiexpr maybeExpTy = do
-- {{{
    -- TODO check aiexpr type is compatible with Word
    equateTypes t (typeAST aiexpr) (Just "arraypoke type")
    case maybeExpTy of
      Nothing -> return ()
      Just expTy -> equateTypes t expTy (Just "arraypoke expected type")

    return (AnnArrayPoke rng t c base aiexpr)

typecheckArrayPoke rng _ _base baseType index maybeExpTy =
    tcFails [out $ "Unable to arraypoke expression of type " ++ show baseType
                ++ " with expression " ++ show index
                ++ " (context expected type " ++ show maybeExpTy ++ ")"
                ++ highlightFirstLine rng]
-- }}}

-----------------------------------------------------------------------

showtypes :: [AnnExpr] -> TypeAST -> String
showtypes args expectedTypes = concatMap showtypes' (zip3 [1..] args expTypes)
  where showtypes' (_n, expr, expty) =
            if show (typeAST expr) == show expty
              then ""
              else
                ("\n\tArg has type " ++ show (typeAST expr)
                        ++ ", expected " ++ show expty ++ ":\n"
                        ++ show (rangeOf expr)
                        ++ concatMap (\(n, a) -> "\narg " ++ show n ++ "\n"
                        ++ outToString (showStructure a)) (zip [0..] args)  ++ "\n")
        expTypes = (case expectedTypes of
                        (TupleTypeAST x) -> x
                        x -> [x]) ++ repeat (TyConAppAST "<unknown>" []) -- hack :(

-- For example,   foo (1, 2)   would produce:
-- eargs   = [1, 2]
-- argtype = (i32, i32)
-- eb       = foo
-- basetype = (?a -> ?b) ((for top level functions))
typecheckCallWithBaseFnType :: AnnTuple -> AnnExpr -> TypeAST -> SourceRange
                            -> Tc AnnExpr
typecheckCallWithBaseFnType argtup eb basetype range =
    case (basetype, typeAST (AnnTuple argtup))
      of
         (FnTypeAST formaltype restype _cc _cs, argtype) -> do
           -- Note use of implicit laziness to avoid unnecessary work.
           let errmsg = ("CallAST mismatch between formal & arg types\n"
                          ++ showtypes (annTupleExprs argtup) formaltype)
           equateTypes formaltype argtype (Just $ errmsg)
           return (AnnCall range restype eb argtup)

         _otherwise -> do
            ebStruct <- tcShowStructure eb
            tcFails $ (out $ "Called value was not a function: "):ebStruct:
                                       [out $ " :: " ++ (show $ typeAST eb)]

vname (E_VarAST _rng ev) n = show n ++ " for " ++ T.unpack (evarName ev)
vname _                  n = show n

genUnificationVarsLike :: [a] -> (Int -> String) -> Tc [TypeAST]
genUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVar (namegen n) | (_, n) <- zip spine [1..]]

-- Typecheck the function first, then the args.
-- Example the interior call to foo in
--           foo = { forall a, x : List a => if isnil x then 0 else 1 + foo nil }
-- results in a call to typecheckCall with expected type Int32,
--   base = foo :: ?foo
-- so the MetaTyVar case is taken, and we proceed to typecheckCallWithBaseFnType
-- using a bare function type...
--
typecheckCall :: Context TypeAST -> SourceRange
              -> ExprAST -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheckCall ctx rng base args maybeExpTy = do
   -- Do we infer a plain function type or a forall type?
   -- For now, we just punt and act in inference rather than checking mode.
   -- But we'd like to propagate more information down, by saying something
   -- like: If we have (e e_1 .. e_n) :: T, we infer that e :: (?1 ... ?n -> T)
   --                                               and e_n :: ?n
   let expectedLambdaType = Nothing

   eb <- typecheck ctx base expectedLambdaType
   case typeAST eb of
      (ForAllAST ktyvars rho) -> do
         -- eb ::[[??]] ea
         let (FnTypeAST argType retType _ _) = rho
         -- Example:            argtype =   ('a -> 'b)
         -- base has type ForAll ['a 'b]   (('a -> 'b) -> (Coro 'a 'b))
         -- The forall-bound vars won't unify with concrete types in the term arg,
         -- so we replace the forall-bound vars with unification variables
         -- when computing the type of the term argument.

         -- That is, instead of checking the args against ('a -> 'b),
         -- we must use unification variables instead:    (?a -> ?b)
         -- and then extract the types from unification
         -- to use as type arguments.

         -- Generate unification vars                 (?a, ?b)
         -- corresponding to the bound type variables ('a, 'b).
         unificationVars <- genUnificationVarsLike ktyvars
                                (\n -> "type parameter " ++ vname base n)

         let tyvarsAndMetavars = List.zip (tyvarsOf ktyvars) unificationVars

         -- Convert ('a -> 'b) to (?a -> ?b).
         let unifiableArgType = parSubstTy tyvarsAndMetavars argType
         let unifiableRetType = parSubstTy tyvarsAndMetavars retType

         -- Type check the args, unifying them with the expected arg type.
         ea@(AnnTuple eargs) <- typecheck ctx args (Just $ unifiableArgType)

         -- TODO should this be equateTypes instead of tcUnifyTypes?
         --tcLift $ putStrLn ("unifying: " ++ show unifiableArgType)
         --tcLift $ putStrLn ("   w ith: " ++ show (typeAST ea))
         --tcLift $ putStrLn ("     and: " ++ show unifiableRetType)
         --tcLift $ putStrLn ("   w ith: " ++ show maybeExpTy)
         --tcLift $ putStrLn ""

         unificationResults <- unifyFun unifiableArgType unifiableRetType
                                        (typeAST ea)     maybeExpTy
         case unificationResults of
           Nothing -> tcFails [out $ "Failed to determine type arguments to apply!" ++ show rng]
           Just tysub -> do
             -- Suppose the argument to the call has typeAST ea = (t1 -> t2):
             -- ((?a -> ?b) -> (Coro ?a ?b))
             let unifiableRhoType = parSubstTy tyvarsAndMetavars rho
              -- ((t1 -> t2) -> (Coro t1 t2))
             let substitutedFnType = tySubst tysub unifiableRhoType
             -- eb[tyProjTypes]::substitutedFnType

             --tcLift $ putStrLn ("typeAST eb: " ++ show (typeAST eb))
             --tcLift $ putStrLn ("substitutedFnType: " ++ show substitutedFnType)
             --tcLift $ putStrLn ("_maybeExpTy: " ++ show maybeExpTy)
             --tcLift $ putStrLn ("tysub: " ++ show tysub)

             tyProjTypes <- extractSubstTypes
                               (map (\(MetaTyVar m) -> m) unificationVars) tysub
             --tcLift $ putStrLn ("tcTyProjTypes: " ++ show tyProjTypes)
             let annTyApp = E_AnnTyApp rng substitutedFnType eb (minimalTupleAST tyProjTypes)
             --tcLift $ putStrLn ("annTyApp: " ++ show annTyApp)
             typecheckCallWithBaseFnType eargs annTyApp (typeAST annTyApp) rng

      -- (typeAST eb) ==
      fnty@(FnTypeAST formaltype _restype _cc _cs) -> do
            AnnTuple eargs <- typecheck ctx args (Just formaltype)
            typecheckCallWithBaseFnType eargs eb fnty rng

      m@(MetaTyVar (Meta _ _ desc)) -> do
            tcLift $ putStrLn ("typecheckCall ctx rng base args _maybeExpTy: " ++ show maybeExpTy)
            AnnTuple eargs <- typecheck ctx args Nothing

            ft <- newTcUnificationVar $ "ret type for " ++ desc
            rt <- newTcUnificationVar $ "arg type for " ++ desc
            -- TODO this should sometimes be proc, not func...
            let fnty = mkFuncTy ft rt

            equateTypes m fnty Nothing
            typecheckCallWithBaseFnType eargs eb fnty rng

      _ -> tcFails [out $ "Called expression had unexpected type: "
                          ++ show (typeAST eb) ++ highlightFirstLine rng]

unifyFun expArg _actRet actArg Nothing       = tcUnifyTypes expArg actArg
unifyFun expArg  actRet actArg (Just expRet) = tcUnifyTypes (TupleTypeAST [expArg, actRet])
                                                            (TupleTypeAST [actArg, expRet])

mkFuncTy a r = FnTypeAST a r FastCC FT_Func
-----------------------------------------------------------------------

-- Functions default to the fast calling convention.
typecheckFn ctx f Nothing =
                typecheckFn' ctx f FastCC Nothing  Nothing

typecheckFn ctx f (Just (FnTypeAST s t cc _cs)) =
                typecheckFn' ctx f     cc (Just s) (Just t)

typecheckFn _ctx f (Just t) = tcFails [out $
                "Context of function literal expects non-function type: "
                                ++ show t ++ highlightFirstLine (fnAstRange f)]

typecheckFn' :: Context TypeAST -> FnAST -> CallConv
             -> Maybe TypeAST -> Maybe TypeAST -> Tc AnnExpr
typecheckFn' ctx f cc expArgType expBodyType = do
    let fnProtoName = T.unpack (fnAstName f)
    uniquelyNamedFormals <- getUniquelyNamedFormals (fnAstRange f)
                                                    (fnFormals f) fnProtoName

    -- Typecheck the body of the function in a suitably extended context.
    extCtx <- extendContext ctx uniquelyNamedFormals expArgType
    annbody <- typecheck extCtx (fnAstBody f) expBodyType

    -- If the function has a return type annotation, use that;
    -- otherwise, we assume it has a monomorphic return type
    -- and determine the exact type via unification.
    fnProtoRetTy <- case fnRetType f of
                      Nothing -> do newTcUnificationVar $
                                         "inferred ret type for " ++ fnProtoName
                      Just t -> return t

    -- Make sure the body (forcibly) agrees with the return type annotation.
    equateTypes fnProtoRetTy (typeAST annbody)
                    (Just $ "return type/body type mismatch in " ++ fnProtoName)

    -- Note we collect free vars in the old context, since we can't possibly
    -- capture the function's arguments from the environment!
    freeVars <- computeFreeFnVars uniquelyNamedFormals annbody f ctx
    formalVars <- typeJoinVars uniquelyNamedFormals expArgType

    -- Compute "base" function type, ignoring any type parameters.
    let fnty0 = FnTypeAST argtypes (typeAST annbody) cc procOrFunc
                where argtypes   = TupleTypeAST (map tidType formalVars)
                      procOrFunc = if fnWasToplevel f then FT_Proc else FT_Func

    -- If we have type parameters, wrap fnty0 in a forall type.
    let fnty = case fnTyFormals f of
           []   -> fnty0
           tyformals ->
              let btv (TypeFormalAST name kind) = (BoundTyVar name, kind) in
              ForAllAST (map btv tyformals) fnty0

    -- If we're type checking a top-level function binding,
    -- update the type for the binding's unification variable.
    case termVarLookup (T.pack fnProtoName) (contextBindings ctx) of
      Nothing -> return ()
      Just av -> equateTypes fnty (tidType av)
                   (Just $ "overall type of function " ++ fnProtoName)

    return $ E_AnnFn (AnnFn fnty (GlobalSymbol $ T.pack fnProtoName)
                           formalVars annbody freeVars
                           (fnAstRange f))

computeFreeFnVars uniquelyNamedFormals annbody f ctx = do
    let identsFree = bodyvars `butnot` (boundvars ++ globalvars)
                     where
                     bodyvars   = freeIdents annbody
                     boundvars  = map tidIdent uniquelyNamedFormals
                     globalvars = concatMap tmBindingId (globalBindings ctx)
                     tmBindingId (TermVarBinding _ tid) = [tidIdent tid]
    freeAnns <- let rng = fnAstRange f in
                mapM (\id -> typecheckVar ctx rng (identPrefix id)) identsFree
    return $ [tid | E_AnnVar _ tid <- freeAnns]

-- | Verify that the given formals have distinct names,
-- | and return unique'd versions of each.
getUniquelyNamedFormals rng rawFormals fnProtoName = do
    _ <- verifyNonOverlappingVariableNames rng fnProtoName
                      (map (identPrefix.tidIdent) rawFormals)
    mapM uniquelyName rawFormals

-----------------------------------------------------------------------

typecheckTuple ctx rng exprs maybeExpectedType =
  case maybeExpectedType of
     Nothing                -> tcTuple ctx rng exprs [Nothing | _ <- exprs]
     Just (TupleTypeAST ts) -> tcTuple ctx rng exprs [Just t  | t <- ts]
     Just m@MetaTyVar {}    -> do
        tctup <- typecheckTuple ctx rng exprs Nothing
        equateTypes m (typeAST tctup) (Just $ highlightFirstLine rng)
        return tctup
     Just ty -> tcFails [out $ "typecheck: tuple (" ++ show exprs ++ ") "
                            ++ "cannot check against non-tuple type " ++ show ty]
  where
    tcTuple ctx rng es ts = do
        exprs <- typecheckExprsTogether ctx es ts
        return $ AnnTuple (E_AnnTuple rng exprs)

    -- Typechecks each expression in the same context
    typecheckExprsTogether ctx exprs expectedTypes = do
        sanityCheck (length exprs == length expectedTypes)
            ("typecheckExprsTogether: had different number of values ("
               ++ (show $ length exprs)
               ++ ") and expected types (" ++ (show $ length expectedTypes) ++
                 ")\n" ++ show exprs ++ " versus \n" ++ show expectedTypes)
        mapM (\(e,mt) -> typecheck ctx e mt) (List.zip exprs expectedTypes)

-----------------------------------------------------------------------

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

verifyNonOverlappingVariableNames :: SourceRange -> String -> [T.Text] -> Tc ()
verifyNonOverlappingVariableNames rng name varNames = do
    case detectDuplicates varNames of
        []   -> return ()
        dups -> tcFails [out $ "Error when checking " ++ name ++ ": "
                              ++ "had duplicated bindings: " ++ show dups
                              ++ highlightFirstLine rng]

-----------------------------------------------------------------------

-- equateTypes first attempts to unify the two given types.
-- If unification fails, the provided error message (if any)
-- is printed along with the unification failure error message.
-- If unification succeeds, each unification variable in the two
-- types is updated according to the unification solution.
equateTypes :: TypeAST -> TypeAST -> Maybe String -> Tc ()
equateTypes t1 t2 msg = do
  tcOnError (liftM out msg) (tcUnifyTypes t1 t2) (\(Just soln) -> do
     let univars = concatMap collectUnificationVars [t1, t2]
     forM_ univars (\m@(Meta u _ _) -> do
       case Map.lookup u soln of
         Nothing -> return ()
         Just t2 -> do mt1 <- readTcMeta m
                       case mt1 of Nothing -> writeTcMeta m t2
                                   Just t1 -> equateTypes t1 t2 msg))
  where
     collectUnificationVars :: TypeAST -> [MetaTyVar]
     collectUnificationVars x =
         case x of
             PrimIntAST _          -> []
             TyConAppAST _nm types -> concatMap collectUnificationVars types
             TupleTypeAST types    -> concatMap collectUnificationVars types
             FnTypeAST s r _ _     -> concatMap collectUnificationVars [s,r]
             CoroTypeAST s r       -> concatMap collectUnificationVars [s,r]
             ForAllAST _tvs rho    -> collectUnificationVars rho
             TyVarAST  _tv         -> []
             MetaTyVar     m       -> [m]
             RefTypeAST    ty      -> collectUnificationVars ty
             ArrayTypeAST  ty      -> collectUnificationVars ty

bindingForVar v = TermVarBinding (identPrefix $ tidIdent v) v

extendContext :: Context TypeAST -> [AnnVar] -> Maybe TypeAST -> Tc (Context TypeAST)
extendContext ctx [] Nothing = return ctx
extendContext ctx protoFormals expFormals = do
    bindings <- extractBindings protoFormals expFormals
    return $ prependContextBindings ctx bindings
  where
    extractBindings :: [AnnVar] -> Maybe TypeAST -> Tc [ContextBinding TypeAST]
    extractBindings fnProtoFormals maybeExpTy = do
        joinedVars <- typeJoinVars fnProtoFormals maybeExpTy
        return (map bindingForVar joinedVars)

typeJoinVars :: [AnnVar] -> (Maybe TypeAST) -> Tc [AnnVar]

typeJoinVars vars Nothing = return $ vars

typeJoinVars [var@(TypedId t _)] (Just u@(MetaTyVar _)) = do
    equateTypes t u Nothing
    return [var]

typeJoinVars []   (Just u@(MetaTyVar _)) = do
    equateTypes u (TupleTypeAST []) Nothing
    return []

typeJoinVars vars (Just (TupleTypeAST expTys)) = do
    sanityCheck (List.length vars == List.length expTys)
        ("Lengths of tuples must agree! Had " ++ show vars ++ " and " ++ show expTys)
    sequence [equateTypes t e Nothing >> return (TypedId t v)
             | ((TypedId t v), e) <- (List.zip vars expTys)]

typeJoinVars vars (Just t) =
    tcFails [out $ "typeJoinVars not yet implemented for type "
                 ++ show t ++ " against " ++ show vars]

