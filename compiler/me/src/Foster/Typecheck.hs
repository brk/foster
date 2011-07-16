module Foster.Typecheck where

import List(length, zip, sort, group, head)
import Control.Monad(liftM, forM_, forM)

import Debug.Trace(trace)
import qualified Data.Text as T
import qualified Data.Map as Map(lookup)

import System.Console.ANSI

import Foster.Base
import Foster.TypeAST
import Foster.ExprAST
import Foster.AnnExpr
import Foster.Infer
import Foster.Context

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
             (NamedTypeAST s)     -> []
             (TupleTypeAST types) -> concatMap collectUnificationVars types
             (FnTypeAST s r cc cs)-> concatMap collectUnificationVars [s,r]
             (CoroTypeAST s r)    -> concatMap collectUnificationVars [s,r]
             (ForAllAST tvs rho)  -> collectUnificationVars rho
             (TyVarAST tv)        -> []
             (MetaTyVar m)        -> [m]
             (RefTypeAST   ty)    -> collectUnificationVars ty
             (ArrayTypeAST  ty)   -> collectUnificationVars ty


typeJoinVars :: [AnnVar] -> (Maybe TypeAST) -> Tc [AnnVar]

typeJoinVars vars (Nothing) = return $ vars

typeJoinVars [var@(TypedId t v)] (Just u@(MetaTyVar m)) = do
    equateTypes t u Nothing
    return [var]

typeJoinVars []   (Just u@(MetaTyVar m)) = do
    equateTypes u (TupleTypeAST []) Nothing
    return []

typeJoinVars vars (Just (TupleTypeAST expTys)) =
    if (List.length vars) == (List.length expTys)
      then sequence [equateTypes t e Nothing >> return (TypedId t v)
                    | ((TypedId t v), e) <- (List.zip vars expTys)]
      else tcFails [out $ "Lengths of tuples must agree! Had " ++ show vars ++ " and " ++ show expTys]

typeJoinVars vars (Just t) =
  error $ "typeJoinVars not yet implemented for type " ++ show t ++ " against " ++ show vars


extractBindings :: [AnnVar] -> Maybe TypeAST -> Tc [ContextBinding TypeAST]
extractBindings fnProtoFormals maybeExpTy = do
    let bindingForVar v = TermVarBinding (identPrefix $ tidIdent v) v
    joinedVars <- typeJoinVars fnProtoFormals maybeExpTy
    let bindings = map bindingForVar joinedVars
    return bindings

extendContext :: Context TypeAST -> [AnnVar] -> Maybe TypeAST -> Tc (Context TypeAST)
extendContext ctx protoFormals expFormals = do
    bindings <- extractBindings protoFormals expFormals
    return $ prependContextBindings ctx bindings

sanityCheck :: Bool -> String -> Tc ()
sanityCheck cond msg = if cond then return () else tcFails [outCSLn Red msg]

isFnAST (E_FnAST _) = True
isFnAST _           = False

data RecursiveStatus = YesRecursive | NotRecursive
isRecursive :: String -> ExprAST -> RecursiveStatus
isRecursive boundName expr =
    if boundName `elem` freeVars expr && isFnAST expr then YesRecursive else NotRecursive

typecheck :: Context TypeAST -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheck ctx expr maybeExpTy =
  tcWithScope expr $
    do case expr of
        E_BoolAST rng b ->
          case maybeExpTy of
            Nothing -> return (AnnBool rng b)
            Just  t | t == fosBoolType
                    -> return (AnnBool rng b)
            Just  t -> tcFails [out $ "Unable to check Bool constant in context"
                                   ++ " expecting non-Bool type " ++ show t
                                   ++ showSourceRange rng]
        E_IfAST rng a b c -> typecheckIf ctx rng a b c maybeExpTy
        E_UntilAST rng a b -> do
                aa <- typecheck ctx a (Just fosBoolType)
                ab <- typecheck ctx b Nothing
                equateTypes (typeAST aa) fosBoolType  (Just "E_Until: type of conditional wasn't boolean")
                return $ AnnUntil rng (TupleTypeAST []) aa ab

        E_FnAST f ->
             typecheckFn ctx  f    maybeExpTy

        E_CallAST rng base argtup ->
             typecheckCall ctx rng base (E_TupleAST argtup) maybeExpTy

        E_IntAST rng txt -> typecheckInt rng txt

        E_LetRec rng bindings e mt ->
            typecheckLetRec ctx rng bindings e mt

        E_LetAST rng (TermBinding v a) e mt ->
            let boundName    = evarName v in
            let maybeVarType = evarMaybeType v in
            case (isRecursive boundName a, maybeVarType) of
                (YesRecursive, Nothing) ->
                    tcFails [outCS Red $ "Unification-based inference not yet supported for recursive let bindings. "
                                 ++ " Please add type annotation for let binding of " ++ boundName ++ ":"
                                 ++ highlightFirstLine rng]
                (YesRecursive, Just exptype) ->
                    do id <- tcFresh boundName
                       let exptupletype = Just $ TupleTypeAST [exptype]
                       boundCtx <- extendContext ctx [TypedId exptype id] exptupletype
                       eaf@(E_AnnFn ea) <- typecheck boundCtx  a maybeVarType
                       let annvar = TypedId (typeAST eaf) id
                       ctx' <- extendContext ctx [annvar] exptupletype
                       ee <- typecheck ctx' e mt
                       return (AnnLetFuns rng [id] [ea] ee)
                (NotRecursive, _) ->
                    do id <- tcFresh boundName
                       ea <- typecheck ctx  a maybeVarType
                       let annvar = TypedId (typeAST ea) id
                       let exptupletype = (fmap (\t -> TupleTypeAST [t]) maybeVarType)
                       ctx' <- extendContext ctx [annvar] exptupletype
                       ee <- typecheck ctx' e mt
                       return (AnnLetVar rng id ea ee)

        E_AllocAST rng a -> do
          ea <- typecheck ctx a Nothing
          return (AnnAlloc rng ea)

        E_DerefAST rng a -> do
          ea <- typecheck ctx a Nothing -- TODO: match maybeExpTy?
          case typeAST ea of
            RefTypeAST t -> return (AnnDeref rng t ea)
            other        -> tcFails [out $ "Expected deref-ed expr "
                                     ++ "to have ref type, had " ++ show other ++ show rng]

        E_StoreAST rng a b -> do
          ea <- typecheck ctx a Nothing
          eb <- typecheck ctx b Nothing
          -- TODO verify that the val is a pointer to the slot
          return (AnnStore rng (TupleTypeAST []) ea eb)

        E_SeqAST rng a b -> do
            ea <- typecheck ctx a Nothing --(Just TypeUnitAST)
            id <- tcFresh ".seq"
            eb <- typecheck ctx b maybeExpTy
            return (AnnLetVar rng id ea eb)

        E_SubscriptAST rng a b -> do ta <- typecheck ctx a Nothing
                                     tb <- typecheck ctx b Nothing
                                     typecheckSubscript ctx rng ta (typeAST ta) tb maybeExpTy
        E_TupleAST (TupleAST rng exprs) -> typecheckTuple ctx exprs maybeExpTy

        E_Primitive rng v -> case termVarLookup (evarName v) (primitiveBindings ctx) of
            Just avar     -> return $ AnnPrimitive rng avar
            Nothing       -> tcFails [out $ "Unknown primitive " ++ (evarName v)
                                         ++ showSourceRange rng]


        E_VarAST rng v -> case termVarLookup (evarName v) (contextBindings ctx) of
            Just avar  -> return $ E_AnnVar rng avar
            Nothing    -> tcFails [out $ "Unknown variable " ++ (evarName v)
                                      ++ showSourceRange rng]

        E_TyApp rng e t -> typecheckTyApp ctx rng e t maybeExpTy

        E_Case rng a branches -> typecheckCase ctx rng a branches maybeExpTy

        E_CompilesAST rng me -> case me of
            Nothing -> return $ AnnCompiles rng (CompilesResult $ Errors [out $ "parse error"])
            Just e -> do
                outputOrE <- tcIntrospect (typecheck ctx e Nothing)
                return $ AnnCompiles rng (CompilesResult outputOrE)

-----------------------------------------------------------------------

{-
  rec a = body_a;
      b = body_b;
      ...;
   in e end
-}
typecheckLetRec ctx0 rng bindings e mt = do
    -- Generate unification variables for the overall type of
    -- each binding.
    unificationVars <- sequence [newTcUnificationVar $
                                  "letrec_" ++ evarName v
                                | (TermBinding v _) <- bindings]
    ids <- sequence [tcFresh (evarName v)
                    | (TermBinding v _) <- bindings]
    -- Create an extended context for typechecking the bindings
    let makeTermVarBinding (u, id) = do
           let t = MetaTyVar u
           return $ TermVarBinding (identPrefix id) (TypedId t id)
    ctxBindings <- mapM makeTermVarBinding (zip unificationVars ids)
    let ctx = prependContextBindings ctx0 ctxBindings
    -- Typecheck each binding
    tcbodies <- forM (zip unificationVars bindings) $
       (\(u, TermBinding v b) -> do
           typecheck ctx b (evarMaybeType v)
       )

    -- Typecheck the body as well
    e' <- typecheck ctx e mt

    let fns = [f | (E_AnnFn f) <- tcbodies]
    return $ AnnLetFuns rng ids fns e'


-----------------------------------------------------------------------

checkPattern :: EPattern -> Tc Pattern
checkPattern p = case p of
  EP_Wildcard r  ->  do return $ P_Wildcard r
  EP_Variable r v -> do id <- tcFresh (evarName v)
                        return $ P_Variable r id
  EP_Bool r b     -> return $ P_Bool r b
  EP_Int r str    -> do annint <- typecheckInt r str
                        return $ P_Int  r (aintLitInt annint)
  EP_Tuple r eps  -> do ps <- mapM checkPattern eps
                        return $ P_Tuple r ps

typecheckCase ctx rng a branches maybeExpTy = do
  -- (A) The expected type applies to the branches,
  -- not to the scrutinee.
  -- (B) Each pattern must check against the scrutinee type.
  -- (C) Each branch must check against the expected type,
  --  as well as successfully unify against the overall type.

  aa <- typecheck ctx a Nothing
  m <- newTcUnificationVar "case"
  -- TODO: verify that all vars bound by pattern are unique
  abranches <- forM branches (\(pat, e) -> do
      p <- checkPattern pat
      bindings <- extractPatternBindings p (typeAST aa)
      let ectx = trace ("bindings: " ++ show bindings) $
                  prependContextBindings ctx bindings
      ae <- typecheck ectx e maybeExpTy
      equateTypes (MetaTyVar m) (typeAST ae)
        (Just $ "Failed to unify all branches of case " ++ show rng)
      return (p, ae)
    )
  return $ AnnCase rng (MetaTyVar m) aa abranches

varbind id ty = TermVarBinding (identPrefix id) (TypedId ty id)

extractPatternBindings :: Pattern -> TypeAST -> Tc [ContextBinding TypeAST]
extractPatternBindings (P_Wildcard _   ) ty = return []
extractPatternBindings (P_Variable _ id) ty = return [varbind id ty]

extractPatternBindings (P_Bool r v) ty = do
  ae <- typecheck emptyContext (E_BoolAST r v) (Just ty)
  -- literals don't bind anything, but we still need to check
  -- that we dont' try matching e.g. a bool against an int.
  return []
extractPatternBindings (P_Int r litint) ty = do
  ae <- typecheck emptyContext (E_IntAST r (litIntText litint)) (Just ty)
  -- literals don't bind anything, but we still need to check
  -- that we dont' try matching e.g. a bool against an int.
  return []

extractPatternBindings (P_Tuple r [p]) ty = extractPatternBindings p ty
extractPatternBindings (P_Tuple r ps)  ty =
   case ty of
     TupleTypeAST ts ->
        (if List.length ps == List.length ts
          then do bindings <- sequence [extractPatternBindings p t | (p, t) <- zip ps ts]
                  return $ concat bindings
          else tcFails [out $ "Cannot match pattern against tuple type"
                              ++ " of different length."])
     otherwise -> tcFails [out $ "Cannot check tuple pattern"
                              ++ " against non-tuple type " ++ show ty
                              ++ showSourceRange r]

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

typecheckTyApp ctx rng a t maybeExpTy = do
    ea <- typecheck ctx a Nothing
    case (typeAST ea) of
      (ForAllAST tyvars rho) -> do --
        let tys = listize t
        if (List.length tys /= List.length tyvars)
          then tcFails [out $ "typecheckTyApp: arity mismatch"]
          else let tyvarsAndTys = List.zip (map TyVarAST tyvars) tys in
               return $ E_AnnTyApp rng (parSubstTy tyvarsAndTys rho) ea t
      othertype ->
        tcFails [out $ "Cannot apply type args to expression of"
                   ++ " non-ForAll type "]

-----------------------------------------------------------------------

typecheckSubscript ctx rng base (TupleTypeAST types) i@(AnnInt _rng ty int) maybeExpTy =
    tcFails [out $ "Subscripting tuples is not allowed;"
                ++ " use pattern matching instead!"]

-- TODO make sure i is not negative or too big
typecheckSubscript ctx rng base (ArrayTypeAST t) i@(AnnInt _rng ty int) (Just expTy) = do
    equateTypes t expTy (Just "subscript expected type")
    return (AnnSubscript rng t base i)

typecheckSubscript ctx rng base (ArrayTypeAST t) i@(AnnInt _rng ty int) Nothing = do
    return (AnnSubscript rng t base i)

typecheckSubscript ctx rng base (ArrayTypeAST t) aiexpr maybeExpTy = do
    -- TODO check aiexpr type is compatible with Word
    case maybeExpTy of
      Nothing -> return ()
      Just expTy -> equateTypes t expTy (Just "subscript expected type")

    return (AnnSubscript rng t base aiexpr)

typecheckSubscript ctx rng base baseType index maybeExpTy =
    tcFails [out $ "Unable to subscript expression of type " ++ show baseType
                ++ " with expression " ++ show index
                ++ " (context expected type " ++ show maybeExpTy ++ ")"
                ++ highlightFirstLine rng]

-----------------------------------------------------------------------

-- Maps (a -> b)   or   ForAll [...] (a -> b)    to a.
getFnArgType :: TypeAST -> TypeAST
getFnArgType (FnTypeAST a r cc cs) = a
getFnArgType t@(ForAllAST tvs rho) =
    let fnargty = getFnArgType rho in
    trace ("getFnArgType " ++ show t ++ " ::> " ++ show fnargty) $ fnargty
getFnArgType x = error $ "Called argType on non-FnTypeAST: " ++ show x

showtypes :: [AnnExpr] -> TypeAST -> String
showtypes args expectedTypes = concatMap showtypes' (zip3 [1..] args expTypes)
  where showtypes' (n, expr, expty) =
            if show (typeAST expr) == show expty
              then ""
              else
                ("\n\tArg has type " ++ show (typeAST expr)
                        ++ ", expected " ++ show expty ++ ":"
                        ++ show (rangeOf expr))
        expTypes = (case expectedTypes of
                        (TupleTypeAST x) -> x
                        x -> [x]) ++ repeat (NamedTypeAST "<unknown>")

-- For example,   foo (1, 2)   would produce:
-- eargs   = [1, 2]
-- argtype = (i32, i32)
-- eb       = foo
-- basetype = (?a -> ?b) ((for top level functions))
typecheckCallWithBaseFnType argtup eb basetype range =
    case (basetype, typeAST (AnnTuple argtup))
      of
         (FnTypeAST formaltype restype cc cs, argtype) -> do
           -- Note use of implicit laziness to avoid unnecessary work.
           let errmsg = ("CallAST mismatch between formal & arg types\n"
                          ++ showtypes (annTupleExprs argtup) formaltype)
           equateTypes formaltype argtype (Just $ errmsg)
           return (AnnCall range restype eb argtup)

         otherwise -> do
            ebStruct <- tcShowStructure eb
            tcFails $ (out $ "CallAST w/o FnAST type: "):ebStruct:
                                       [out $ " :: " ++ (show $ typeAST eb)]

vname n (E_VarAST rng ev) = show n ++ " for " ++ evarName ev
vname n _                 = show n

-- If we have an explicit redex (call to a literal function),
-- we can determine the types of the formals based on the actuals.
typecheckCall ctx rng base@(E_FnAST f) args maybeExpTy = do
   ea@(AnnTuple eargtup) <- typecheck ctx args Nothing
   m <- newTcUnificationVar "call"
   let expectedLambdaType = Just $ case maybeExpTy of
        Nothing  -> mkFuncTy (typeAST ea) (MetaTyVar m)
        (Just t) -> mkFuncTy (MetaTyVar m)     t

   eb <- typecheck ctx base expectedLambdaType
   trace ("typecheckCall with literal fn base, exp ty " ++ (show expectedLambdaType)) $
    typecheckCallWithBaseFnType eargtup eb (typeAST eb) rng

-- Otherwise, typecheck the function first, then the args.
typecheckCall ctx rng base args maybeExpTy = do
   expectedLambdaType <- case maybeExpTy of
        Nothing  -> return $ Nothing
        (Just t) -> do m <- newTcUnificationVar "inferred arg type"
                       return $ Just $ mkFuncTy (MetaTyVar m) t
        -- If we have (e1 e2) :: T, we infer that e1 :: (? -> T) and e2 :: ?

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
         unificationVars <- sequence [newTcUnificationVar $ "type parameter" ++ vname n base | (_, n) <- zip tyvars [1..]]
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
             let substitutedFnType = tySubst unifiableRhoType tysub in
             -- eb[tyProjTypes]::substitutedFnType
             let annTyApp = E_AnnTyApp rng substitutedFnType eb (minimalTupleAST tyProjTypes)
                  where tyProjTypes = extractSubstTypes unificationVars tysub
             in typecheckCallWithBaseFnType eargs annTyApp (typeAST annTyApp) rng

      -- (typeAST eb) ==
      fnty@(FnTypeAST formaltype restype cc cs) -> do
            ea@(AnnTuple eargs) <- typecheck ctx args (Just formaltype)
            typecheckCallWithBaseFnType eargs eb fnty rng

      m@(MetaTyVar (Meta _ _ desc)) -> do
            ea@(AnnTuple eargs) <- typecheck ctx args Nothing

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
typecheckFn ctx f (Just (FnTypeAST s t cc cs')) =
                typecheckFn' ctx f     cc (Just s) (Just t)

typecheckFn ctx f (Just t) = tcFails [out $
                "Context of function literal expects non-function type: "
                                ++ show t ++ highlightFirstLine (fnAstRange f)]

typecheckFn' :: Context TypeAST -> FnAST -> CallConv -> Maybe TypeAST -> Maybe TypeAST -> Tc AnnExpr
typecheckFn' ctx f cc expArgType expBodyType = do
    let fnProtoRawFormals = fnFormals f
    let fnProtoName = fnAstName f
    -- If the function has a return type annotation, use that;
    -- otherwise, we assume it has a monomorphic return type
    -- and determine the exact type via unification.
    fnProtoRetTy <- case fnRetType f of
                          Nothing -> do u <- newTcUnificationVar $ "inf. ret type for " ++ fnProtoName
                                        return $ MetaTyVar u
                          Just t -> return t
    _ <- verifyNonOverlappingVariableNames fnProtoName
                                           (map (identPrefix.tidIdent) fnProtoRawFormals)
    uniquelyNamedFormals <- mapM uniquelyName fnProtoRawFormals
    extCtx <- extendContext ctx uniquelyNamedFormals expArgType
    annbody <- typecheck extCtx (fnBody f) expBodyType

    equateTypes fnProtoRetTy (typeAST annbody) (Just $ "return type/body type mismatch in " ++ fnProtoName)

    formalVars <- typeJoinVars uniquelyNamedFormals expArgType
    let argtypes = TupleTypeAST (map tidType formalVars)
    let procOrFunc = if fnWasToplevel f then FT_Proc else FT_Func
    let fnty = FnTypeAST argtypes (typeAST annbody) cc procOrFunc

    case termVarLookup fnProtoName (contextBindings ctx) of
      Nothing -> return ()
      Just av -> equateTypes fnty (tidType av) (Just "overall function types")

    return (E_AnnFn (AnnFn fnty (Ident fnProtoName irrelevantIdentNum)
                           formalVars annbody
                           (fnAstRange f)))

-----------------------------------------------------------------------
typecheckTuple ctx exprs Nothing =
  typecheckTuple' ctx exprs [Nothing | e <- exprs]

typecheckTuple ctx exprs (Just (TupleTypeAST ts)) =
    if length exprs /= length ts
      then tcFails [out $ "typecheckTuple: length of tuple (" ++ (show $ length exprs) ++
                        ") and expected tuple (" ++ (show $ length ts) ++
                        ") types did not agree:\n"
                            ++ show exprs ++ " versus \n" ++ show ts]
      else typecheckTuple' ctx exprs [Just t | t <- ts]

-- terrible, no good, very bad hack
typecheckTuple ctx exprs (Just (MetaTyVar mtv)) =
  typecheckTuple' ctx exprs [Nothing | _ <- exprs]

typecheckTuple ctx es (Just ty)
    = tcFails [out $ "typecheck: tuple (" ++ show es ++ ") "
                ++ "cannot check against non-tuple type " ++ show ty]

typecheckTuple' ctx es ts = do
        let ets = List.zip es ts -- :: [(ExprAST, TypeAST)]
        let subactions = map (\(e,t) -> typecheck ctx e t) ets
        results <- tcIntrospect (sequence subactions)
        case results of
          OK exprs -> let rng = rangeSpanOf (EMissingSourceRange "typecheckTuple'") es in
                      return (AnnTuple (E_AnnTuple rng exprs))
          Errors errs -> tcFails errs
-----------------------------------------------------------------------

typecheckInt :: ESourceRange -> String -> Tc AnnExpr
typecheckInt rng originalText = do
    let goodBases = [2, 8, 10, 16]
    let maxBits = 32
    (clean, base) <- extractCleanBase originalText
    sanityCheck (base `Prelude.elem` goodBases)
                ("Integer base must be one of " ++ show goodBases ++ "; was " ++ show base)
    sanityCheck (onlyValidDigitsIn clean base)
                ("Cleaned integer must contain only hex digits: " ++ clean)
    let int = precheckedLiteralInt originalText maxBits clean base
    let activeBits = litIntMinBits int
    sanityCheck (activeBits <= maxBits)
                ("Integers currently limited to " ++ show maxBits ++ " bits, "
                                                  ++ clean ++ " requires " ++ show activeBits)
    return (AnnInt rng (NamedTypeAST $ "i" ++ show maxBits) int)

-- Given "raw" integer text like "123`456_10",
-- return ("123456", 10)
extractCleanBase :: String -> Tc (String, Int)
extractCleanBase text = do
    let noticks = Prelude.filter (/= '`') text
    case splitString "_" noticks of
        [first, base] -> return (first, read base)
        [first]       -> return (first, 10)
        otherwise     -> tcFails [outLn $ "Unable to parse integer literal " ++ text]

-----------------------------------------------------------------------

splitString :: String -> String -> [String]
splitString needle haystack =
    let textParts = T.splitOn (T.pack needle) (T.pack haystack) in
    map T.unpack textParts

collectErrors :: Tc a -> Tc [Output]
collectErrors tce =
    Tc (\env -> do { result <- unTc env tce
                   ; case result of
                       OK expr     -> return (OK [])
                       Errors ss -> return   (OK ss)
                       })

rename :: Ident -> Uniq -> Ident
rename (Ident p i) u = (Ident p u)

uniquelyName :: TypedId t -> Tc (TypedId t)
uniquelyName (TypedId ty id) = do
    uniq <- newTcUniq
    return (TypedId ty (rename id uniq))

verifyNonOverlappingVariableNames :: String -> [String] -> Tc ()
verifyNonOverlappingVariableNames fnName varNames = do
    let duplicates = [List.head dups
                     | dups <- List.group (List.sort varNames)
                     , List.length dups > 1]
    case duplicates of
        []        -> return ()
        otherwise -> tcFails [out $ "Error when checking " ++ fnName
                                 ++ ": had duplicated formal parameter names: " ++ show duplicates]


