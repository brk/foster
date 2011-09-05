module Foster.Typecheck(typecheck) where

import List(length, zip, sort, group, head, elemIndex, reverse)
import Control.Monad(liftM, forM_, forM)

import Debug.Trace(trace)
import qualified Data.Text as T
import qualified Data.Map as Map(lookup)
import Data.Maybe(fromJust)
import Data.Char (toLower)

import System.Console.ANSI(Color(Red))

import Foster.Base
import Foster.TypeAST
import Foster.ExprAST
import Foster.AnnExpr
import Foster.Infer
import Foster.Context

-----------------------------------------------------------------------

sanityCheck :: Bool -> String -> Tc ()
sanityCheck cond msg = if cond then return () else tcFails [outCSLn Red msg]

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

        E_StoreAST rng a b -> do
          u_slot <- newTcUnificationVar $ "slot_type"
          u_expr <- newTcUnificationVar $ "expr_type"
          eb <- typecheck ctx b (Just $ RefTypeAST (MetaTyVar u_slot))
          ea <- typecheck ctx a (Just $            (MetaTyVar u_expr))
          equateTypes (MetaTyVar u_slot) (MetaTyVar u_expr)
                      (Just "Store expression")
          equateTypes (typeAST eb) (RefTypeAST (typeAST ea))
                      (Just "Store expression")
          return (AnnStore rng ea eb)

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

        E_CompilesAST rng maybeExpr -> case maybeExpr of
            Nothing -> return $ AnnCompiles rng (CompilesResult $
                                                  Errors [out $ "parse error"])
            Just e -> do
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
                        tcFails [out $ "Unknown variable " ++ name
                                 ++ showSourceRange rng
                                 ++ "ctx: "++ show (contextBindings ctx)
                                 ++ "\nhist: " , msg]
-----------------------------------------------------------------------
notRecursive boundName expr =
  not (boundName `elem` freeVars expr && isFnAST expr)
        where   isFnAST (E_FnAST _) = True
                isFnAST _           = False

-- First typecheck the bound expression, then typecheck the
-- scoped expression in an extended context.
typecheckLet ctx rng (TermBinding v a) e mt = do
    let boundName    = evarName v
    let maybeVarType = evarMaybeType v
    sanityCheck (notRecursive boundName a)
        ("Recursive bindings should use 'rec', not 'let'"
                         ++ highlightFirstLine rng)
    id <- tcFresh boundName
    ea <- typecheck ctx  a maybeVarType
    ctx' <- extendContext ctx [TypedId (typeAST ea) id] Nothing
    ee <- typecheck ctx' e mt
    return (AnnLetVar rng id ea ee)
-----------------------------------------------------------------------

{-
  rec a = body_a;
      b = body_b;
      ...;
   in e end
-}
typecheckLetRec :: Context TypeAST -> SourceRange -> [TermBinding]
                -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheckLetRec ctx0 rng bindings e mt = do
    verifyNonOverlappingVariableNames rng "rec" (map termBindingName bindings)
    -- Generate unification variables for the overall type of
    -- each binding.
    unificationVars <- sequence [newTcUnificationVar $
                                  "letrec_" ++ evarName v
                                | (TermBinding v _) <- bindings]
    ids <- sequence [tcFresh (evarName v)
                    | (TermBinding v _) <- bindings]
    -- Create an extended context for typechecking the bindings
    let makeTermVarBinding (u, id) =
           let mtv = MetaTyVar u in
           TermVarBinding (identPrefix id) (TypedId mtv id)
    let ctxBindings = map makeTermVarBinding (zip unificationVars ids)
    let ctx = prependContextBindings ctx0 ctxBindings

    -- Typecheck each binding
    tcbodies <- forM (zip unificationVars bindings) $
       (\(u, TermBinding v b) -> do
           b' <- typecheck ctx b (evarMaybeType v) -- or (Just $ MetaTyVar u)?
           equateTypes (MetaTyVar u) (typeAST b')
                       (Just $ "recursive binding " ++ evarName v)
           return b'
       )

    -- Typecheck the body as well
    e' <- typecheck ctx e mt

    let fns = [f | (E_AnnFn f) <- tcbodies]
    return $ AnnLetFuns rng ids fns e'

-----------------------------------------------------------------------

getCtorInfoForCtor :: String -> Tc (CtorInfo TypeAST)
getCtorInfoForCtor ctorName = do
  ctorInfos <- tcGetCtorInfo
  case Map.lookup ctorName ctorInfos of
    Just [info] -> return info
    elsewise -> tcFails [out $ "Typecheck.getCtorInfoForCtor: Too many or"
                                ++ " too few definitions for $" ++ ctorName
                                ++ "\n\t" ++ show elsewise]

checkPattern :: EPattern -> Tc Pattern
-- Make sure that each pattern has the proper arity.
checkPattern p = case p of
  EP_Wildcard r   -> do return $ P_Wildcard r
  EP_Bool r b     -> do return $ P_Bool r b
  EP_Variable r v -> do id <- tcFresh (evarName v)
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

typecheckCase :: Context TypeAST -> SourceRange -> ExprAST
              -> [(EPattern, ExprAST)] -> Maybe TypeAST -> Tc AnnExpr
typecheckCase ctx rng scrutinee branches maybeExpTy = do
  -- (A) The expected type applies to the branches,
  -- not to the scrutinee.
  -- (B) Each pattern must check against the scrutinee type.
  -- (C) Each branch must check against the expected type,
  --  as well as successfully unify against the overall type.

  ascrutinee <- typecheck ctx scrutinee Nothing
  m <- newTcUnificationVar "case"
  let checkBranch (pat, body) = do
      p <- checkPattern pat
      bindings <- extractPatternBindings p (typeAST ascrutinee)
      verifyNonOverlappingVariableNames rng "case"
                                        [v | (TermVarBinding v _) <- bindings]
      abody <- typecheck (prependContextBindings ctx bindings) body maybeExpTy
      equateTypes (MetaTyVar m) (typeAST abody)
                   (Just $ "Failed to unify all branches of case " ++ show rng)
      return (p, abody)
  abranches <- forM branches checkBranch
  return $ AnnCase rng (MetaTyVar m) ascrutinee abranches

varbind id ty = TermVarBinding (identPrefix id) (TypedId ty id)

extractPatternBindings :: Pattern -> TypeAST -> Tc [ContextBinding TypeAST]

extractPatternBindings (P_Wildcard _   ) _  = return []
extractPatternBindings (P_Variable _ id) ty = return [varbind id ty]

extractPatternBindings (P_Ctor _ pats (CtorId _ ctorName _ _)) _ty = do
  CtorInfo _ (DataCtor _ _smallId types) <- getCtorInfoForCtor ctorName
  bindings <- sequence [extractPatternBindings p t | (p, t) <- zip pats types]
  return $ concat bindings

extractPatternBindings (P_Bool r v) ty = do
  _ae <- typecheck emptyContext (E_BoolAST r v) (Just ty)
  -- literals don't bind anything, but we still need to check
  -- that we dont' try matching e.g. a bool against an int.
  return []

extractPatternBindings (P_Int r litint) ty = do
  _ae <- typecheck emptyContext (E_IntAST r (litIntText litint)) (Just ty)
  -- literals don't bind anything, but we still need to check
  -- that we dont' try matching e.g. a bool against an int.
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

typecheckTyApp ctx rng a t _maybeExpTy = do
    ea <- typecheck ctx a Nothing
    case (typeAST ea) of
      ForAllAST tyvars rho -> do
        let tys = listize t
        sanityCheck (List.length tys == List.length tyvars)
                    "typecheckTyApp: arity mismatch"
        let tyvarsAndTys = List.zip (map TyVarAST tyvars) tys
        return $ E_AnnTyApp rng (parSubstTy tyvarsAndTys rho) ea t
      _othertype ->
        tcFails [out $ "Cannot apply type args to expression of"
                   ++ " non-ForAll type "]

-----------------------------------------------------------------------

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

-----------------------------------------------------------------------

-- c >^ base[aiexpr]
typecheckArrayPoke rng c base (ArrayTypeAST t) aiexpr maybeExpTy = do
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
                        x -> [x]) ++ repeat (NamedTypeAST "<unknown>")

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

vname (E_VarAST _rng ev) n = show n ++ " for " ++ evarName ev
vname _                  n = show n

genUnificationVarsLike :: [a] -> (Int -> String) -> Tc [MetaTyVar]
genUnificationVarsLike spine namegen = do
  sequence [newTcUnificationVar (namegen n) | (_, n) <- zip spine [1..]]

-- Typecheck the function first, then the args.
typecheckCall :: Context TypeAST -> SourceRange
              -> ExprAST -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheckCall ctx rng base args _maybeExpTy = do
   -- Do we infer a plain function type or a forall type?
   -- For now, we just punt and act in inference rather than checking mode.
   -- But we'd like to propagate more information down, by saying something
   -- like: If we have (e e_1 .. e_n) :: T, we infer that e :: (?1 ... ?n -> T)
   --                                               and e_n :: ?n
   let expectedLambdaType = Nothing

   eb <- typecheck ctx base expectedLambdaType
   case (typeAST eb) of
      (ForAllAST tyvars rho) -> do
         let (FnTypeAST rhoArgType _ _ _) = rho
         -- Example:         rhoargtype =   ('a -> 'b)
         -- base has type ForAll ['a 'b]   (('a -> 'b) -> (Coro 'a 'b))
         -- The forall-bound vars won't unify with concrete types in the term arg,
         -- so we replace the forall-bound vars with unification variables
         -- when computing the type of the term argument.

         -- That is, instead of checking the args against ('a -> 'b),
         -- we must use unification variables instead:    (?a -> ?b)
         -- and then extract the types from unification
         -- to use as type arguments.

         -- Generate unification vars corresponding to the bound type variables
         unificationVars <- genUnificationVarsLike tyvars
                                (\n -> "type parameter" ++ vname base n)
         let tyvarsAndMetavars = (List.zip (map TyVarAST tyvars)
                                          (map MetaTyVar unificationVars))

         -- (?a -> ?b)
         let unifiableArgType = parSubstTy tyvarsAndMetavars rhoArgType

         -- Type check the args, unifying them
         -- with the expected arg type
         ea@(AnnTuple eargs) <- typecheck ctx args (Just $ unifiableArgType)

         -- TODO should this be equateTypes instead of tcUnifyTypes?
         unificationResults <- tcUnifyTypes unifiableArgType (typeAST ea)
         case unificationResults of
           Nothing -> tcFails [out $ "Failed to determine type arguments to apply!" ++ show rng]
           Just tysub ->
             -- Suppose typeAST ea = (t1 -> t2):
             -- ((?a -> ?b) -> (Coro ?a ?b))
             let unifiableRhoType = parSubstTy tyvarsAndMetavars rho in
              -- ((t1 -> t2) -> (Coro t1 t2))
             let substitutedFnType = tySubst tysub unifiableRhoType in
             -- eb[tyProjTypes]::substitutedFnType
             let annTyApp = E_AnnTyApp rng substitutedFnType eb (minimalTupleAST tyProjTypes)
                  where tyProjTypes = extractSubstTypes unificationVars tysub
             in typecheckCallWithBaseFnType eargs annTyApp (typeAST annTyApp) rng

      -- (typeAST eb) ==
      fnty@(FnTypeAST formaltype _restype _cc _cs) -> do
            AnnTuple eargs <- typecheck ctx args (Just formaltype)
            typecheckCallWithBaseFnType eargs eb fnty rng

      m@(MetaTyVar (Meta _ _ desc)) -> do
            AnnTuple eargs <- typecheck ctx args Nothing

            ft <- newTcUnificationVar $ "ret type for " ++ desc
            rt <- newTcUnificationVar $ "arg type for " ++ desc
            -- TODO this should sometimes be proc, not func...
            let fnty = mkFuncTy (MetaTyVar ft) (MetaTyVar rt)

            equateTypes m fnty Nothing
            typecheckCallWithBaseFnType eargs eb fnty rng

      _ -> tcFails [out $ "Called expression had unexpected type: "
                          ++ show (typeAST eb) ++ highlightFirstLine rng]

mkFuncTy a r = FnTypeAST a r FastCC FT_Func
-----------------------------------------------------------------------

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
    let fnProtoName = fnAstName f
    uniquelyNamedFormals <- getUniquelyNamedFormals (fnAstRange f)
                                                    (fnFormals f) fnProtoName

    -- Typecheck the body of the function in a suitably extended context.
    extCtx <- extendContext ctx uniquelyNamedFormals expArgType
    annbody <- typecheck extCtx (fnAstBody f) expBodyType

    -- If the function has a return type annotation, use that;
    -- otherwise, we assume it has a monomorphic return type
    -- and determine the exact type via unification.
    fnProtoRetTy <- case fnRetType f of
                      Nothing -> do u <- newTcUnificationVar $
                                         "inferred ret type for " ++ fnProtoName
                                    return $ MetaTyVar u
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
                 vars -> ForAllAST (map BoundTyVar vars) fnty0

    -- If we're type checking a top-level function binding,
    -- update the type for the binding's unification variable.
    case termVarLookup fnProtoName (contextBindings ctx) of
      Nothing -> return ()
      Just av -> equateTypes fnty (tidType av) (Just "overall function types")

    return $ E_AnnFn (AnnFn fnty (GlobalSymbol fnProtoName)
                           formalVars annbody freeVars
                           (fnAstRange f))

computeFreeFnVars uniquelyNamedFormals annbody f ctx = do
    let identsFree = bodyvars `butnot` (boundvars ++ globalvars)
                     where
                     bodyvars   = freeIdents annbody
                     boundvars  = map tidIdent uniquelyNamedFormals
                     globalvars = map bindingId (globalBindings ctx)
                     bindingId (TermVarBinding _ tid) = tidIdent tid
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

-- terrible, no good, very bad hack: we shouldn't just discard the meta ty var!
typecheckTuple ctx rng exprs (Just (MetaTyVar _)) =
 typecheckTuple ctx rng exprs Nothing

typecheckTuple ctx rng exprs Nothing                  = tcTuple ctx rng exprs [Nothing | _ <- exprs]
typecheckTuple ctx rng exprs (Just (TupleTypeAST ts)) = tcTuple ctx rng exprs (map Just ts)

typecheckTuple _ctx _rng es (Just ty)
    = tcFails [out $ "typecheck: tuple (" ++ show es ++ ") "
                ++ "cannot check against non-tuple type " ++ show ty]

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

typecheckInt :: SourceRange -> String -> Tc AnnExpr
typecheckInt rng originalText = do
    let goodBases = [2, 8, 10, 16]
    let maxBits = 32
    (clean, base) <- extractCleanBase originalText
    sanityCheck (base `Prelude.elem` goodBases)
                ("Integer base must be one of " ++ show goodBases
                                    ++ "; was " ++ show base)
    sanityCheck (onlyValidDigitsIn clean base)
                ("Cleaned integer must contain only hex digits: " ++ clean)
    let int = precheckedLiteralInt originalText maxBits clean base
    let activeBits = litIntMinBits int
    sanityCheck (activeBits <= maxBits)
                ("Integers currently limited to " ++ show maxBits ++ " bits, "
                                  ++ clean ++ " requires " ++ show activeBits)
    return (AnnInt rng (NamedTypeAST $ "Int" ++ show maxBits) int)
 where
        onlyValidDigitsIn :: String -> Int -> Bool
        onlyValidDigitsIn str lim =
            let validIndex mi = Just True == fmap (< lim) mi in
            Prelude.all validIndex (map indexOf str)

        indexOf x = (toLower x) `List.elemIndex` "0123456789abcdef"

        -- Given "raw" integer text like "123`456_10",
        -- return ("123456", 10)
        extractCleanBase :: String -> Tc (String, Int)
        extractCleanBase text = do
            let noticks = Prelude.filter (/= '`') text
            case splitString "_" noticks of
                [first, base] -> return (first, read base)
                [first]       -> return (first, 10)
                _otherwise    -> tcFails
                   [outLn $ "Unable to parse integer literal " ++ text]

        splitString :: String -> String -> [String]
        splitString needle haystack =
            let textParts = T.splitOn (T.pack needle) (T.pack haystack) in
            map T.unpack textParts

        -- Precondition: the provided string must be parseable in the given radix
        precheckedLiteralInt :: String -> Int -> String -> Int -> LiteralInt
        precheckedLiteralInt originalText _maxBits clean base =
            let integerValue = parseRadixRev (fromIntegral base) (List.reverse clean) in
            let activeBits = List.length (bitStringOf integerValue) in
            LiteralInt integerValue activeBits originalText base

        -- Precondition: string contains only valid hex digits.
        parseRadixRev :: Integer -> String -> Integer
        parseRadixRev _ ""     = 0
        parseRadixRev r (c:cs) =
                (r * parseRadixRev r cs) + (fromIntegral $ fromJust (indexOf c))

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

verifyNonOverlappingVariableNames :: SourceRange -> String -> [String] -> Tc ()
verifyNonOverlappingVariableNames rng name varNames = do
    let duplicates = [List.head dups
                     | dups <- List.group (List.sort varNames)
                     , List.length dups > 1]
    case duplicates of
        []    -> return ()
        _else -> tcFails [out $ "Error when checking " ++ name
                              ++ ": had duplicated bindings: "
                              ++ show duplicates
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
             NamedTypeAST _      -> []
             TupleTypeAST types  -> concatMap collectUnificationVars types
             FnTypeAST s r _ _   -> concatMap collectUnificationVars [s,r]
             CoroTypeAST s r     -> concatMap collectUnificationVars [s,r]
             ForAllAST _tvs rho  -> collectUnificationVars rho
             TyVarAST  _tv       -> []
             MetaTyVar     m     -> [m]
             RefTypeAST    ty    -> collectUnificationVars ty
             ArrayTypeAST  ty    -> collectUnificationVars ty


extendContext :: Context TypeAST -> [AnnVar] -> Maybe TypeAST -> Tc (Context TypeAST)
extendContext ctx [] Nothing = return ctx
extendContext ctx protoFormals expFormals = do
    bindings <- trace ("extendContext " ++ show protoFormals ++ "\n\t" ++ show expFormals) $
                extractBindings protoFormals expFormals
    return $ prependContextBindings ctx bindings
  where
    extractBindings :: [AnnVar] -> Maybe TypeAST -> Tc [ContextBinding TypeAST]
    extractBindings fnProtoFormals maybeExpTy = do
        joinedVars <- typeJoinVars fnProtoFormals maybeExpTy
        let bindingForVar v = TermVarBinding (identPrefix $ tidIdent v) v
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

