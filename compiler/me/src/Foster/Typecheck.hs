module Foster.Typecheck where

import List(length, zip, sort, group, head)
import Control.Monad(liftM, forM_)

import Debug.Trace(trace)
import qualified Data.Text as T
import qualified Data.Map as Map((!))

import System.Console.ANSI

import Foster.Base
import Foster.TypeAST
import Foster.ExprAST
import Foster.Infer
import Foster.Context

-----------------------------------------------------------------------

collectUnificationVars :: TypeAST -> [MetaTyVar]
collectUnificationVars x =
    case x of
        (NamedTypeAST s)     -> []
        (TupleTypeAST types) -> concat [collectUnificationVars t | t <- types]
        (FnTypeAST s r cs)   -> concat [collectUnificationVars t | t <- [s,r]]
        (CoroType s r)       -> concat [collectUnificationVars t | t <- [s,r]]
        (ForAll tvs rho)     -> collectUnificationVars rho
        (T_TyVar tv)         -> []
        (MetaTyVar m)        -> [m]
        (PtrTypeAST ty)      -> collectUnificationVars ty

-- equateTypes first attempts to unify the two given types.
-- If unification fails, the provided error message (if any)
-- is printed along with the unification failure error message.
-- If unification succeeds, each unification variable in the two
-- types is updated according to the unification solution.
equateTypes :: TypeAST -> TypeAST -> Maybe String -> Tc ()
equateTypes t1 t2 msg = do
  tcOnError (liftM out msg) (tcUnifyTypes t1 t2) (\(Just soln) -> do
     let univars = concat [collectUnificationVars t | t <- [t1, t2]]
     forM_ univars (\m@(Meta u _) -> do
       let t2 = (soln Map.! u)
       mt1 <- readTcRef m
       case mt1 of
         Nothing -> writeTcMeta m t2
         Just t1 -> if typesEqual t1 t2 then return ()
                      else tcFails (out $ "meta ty var " ++ show u ++ " had conflicting types (msg = " ++ show msg ++ ")")
                    ))

typeJoinVars :: [AnnVar] -> (Maybe TypeAST) -> Tc [AnnVar]

typeJoinVars vars (Nothing) = return $ vars

typeJoinVars [var@(AnnVar t v)] (Just u@(MetaTyVar m)) = do
    equateTypes t u Nothing
    return [var]

typeJoinVars vars (Just (TupleTypeAST expTys)) =
    if (List.length vars) == (List.length expTys)
      then sequence [equateTypes t e Nothing >> return (AnnVar t v)
                    | ((AnnVar t v), e) <- (List.zip vars expTys)]
      else tcFails $ out "Lengths of tuples must agree!"

typeJoinVars vars (Just t) =
  error $ "typeJoinVars not yet implemented for type " ++ show t ++ " against " ++ show vars


extractBindings :: [AnnVar] -> Maybe TypeAST -> Tc [ContextBinding]
extractBindings fnProtoFormals maybeExpTy = do
    let bindingForVar v = TermVarBinding (identPrefix $ avarIdent v) v
    joinedVars <- typeJoinVars fnProtoFormals maybeExpTy
    let bindings = map bindingForVar joinedVars
    return bindings

extendContext :: Context -> [AnnVar] -> Maybe TypeAST -> Tc Context
extendContext ctx protoFormals expFormals = do
    bindings <- extractBindings protoFormals expFormals
    return $ prependContextBindings ctx bindings

sanityCheck :: Bool -> String -> Tc ()
sanityCheck cond msg = if cond then return () else tcFails (outCSLn Red msg)

isFnAST (E_FnAST _) = True
isFnAST _           = False

data RecursiveStatus = YesRecursive | NotRecursive
isRecursive :: String -> ExprAST -> RecursiveStatus
isRecursive boundName expr =
    if boundName `elem` freeVars expr && isFnAST expr then YesRecursive else NotRecursive

typecheck :: Context -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheck ctx expr maybeExpTy =
  tcWithScope expr $
    do case expr of
        E_BoolAST rng b -> do return (AnnBool b)
        E_IfAST a b c   -> typecheckIf ctx a b c maybeExpTy
        E_FnAST f       -> typecheckFn ctx  f    maybeExpTy
        E_CallAST rng base args ->
                            typecheckCall ctx rng base args maybeExpTy
        E_IntAST rng txt -> typecheckInt rng txt

        E_LetAST rng (VarAST maybeVarType boundName) a b mt ->
            case (isRecursive boundName a, maybeVarType) of
                (YesRecursive, Nothing) ->
                    tcFails (outCS Red $ "Unification-based inference not yet supported for recursive let bindings. "
                                 ++ " Please add type annotation for let binding of " ++ boundName ++ ":"
                                 ++ highlightFirstLine rng)
                (YesRecursive, Just exptype) ->
                    do id <- tcFresh boundName
                       let exptupletype = Just $ TupleTypeAST [exptype]
                       boundCtx <- extendContext ctx [AnnVar exptype id] exptupletype
                       eaf@(E_AnnFn ea) <- typecheck boundCtx  a maybeVarType
                       let annvar = AnnVar (typeAST eaf) id
                       ctx' <- extendContext ctx [annvar] exptupletype
                       eb <- typecheck ctx' b mt
                       return (AnnLetFuns [id] [ea] eb)
                (NotRecursive, _) ->
                    do id <- tcFresh boundName
                       ea <- typecheck ctx  a maybeVarType
                       let annvar = AnnVar (typeAST ea) id
                       let exptupletype = (fmap (\t -> TupleTypeAST [t]) maybeVarType)
                       ctx' <- extendContext ctx [annvar] exptupletype
                       eb <- typecheck ctx' b mt
                       return (AnnLetVar id ea eb)

        E_SeqAST a b -> do
            ea <- typecheck ctx a Nothing --(Just TypeUnitAST)
            eb <- typecheck ctx b maybeExpTy
            id <- tcFresh ".seq"
            return (AnnLetVar id ea eb)
        E_SubscriptAST a b rng -> do ta <- typecheck ctx a Nothing
                                     tb <- typecheck ctx b Nothing
                                     typecheckSubscript rng ta (typeAST ta) tb maybeExpTy
        E_TupleAST exprs -> typecheckTuple ctx exprs maybeExpTy

        E_VarAST v -> case termVarLookup (evarName v) (contextBindings ctx) of
            Just avar  -> return $ E_AnnVar avar
            Nothing    -> tcFails $ out $ "Unknown variable " ++ (evarName v)

        E_CompilesAST e c -> case c of
            CS_WouldNotCompile -> return $ AnnCompiles CS_WouldNotCompile "parse error"
            CS_WouldCompile -> error "No support for re-type checking CompilesAST nodes."
            CS_NotChecked -> do
                maybeOutput <- extractErrors (typecheck ctx e Nothing)
                return $ case maybeOutput of
                            Nothing -> AnnCompiles CS_WouldCompile    ""
                            Just o  -> AnnCompiles CS_WouldNotCompile (outToString o)

-----------------------------------------------------------------------

typecheckIf ctx a b c maybeExpTy = do
    ea <- typecheck ctx a (Just fosBoolType)
    eb <- typecheck ctx b maybeExpTy
    ec <- typecheck ctx c maybeExpTy
    equateTypes (typeAST ea) fosBoolType  (Just "IfAST: type of conditional wasn't boolean")
    equateTypes (typeAST eb) (typeAST ec) (Just "IfAST: types of branches didn't match")
    return (AnnIf (typeAST eb) ea eb ec)

-----------------------------------------------------------------------

-- Tuple subscripts must have a literal integer subscript denoting the field;
-- looking up the field at runtime wouldn't make much sense.
typecheckSubscript rng base (TupleTypeAST types) i@(AnnInt ty int) maybeExpTy =
    let literalValue = read (litIntText int) :: Integer in
    case safeListIndex types (fromInteger literalValue) of
        Nothing -> tcFails $ out $ "Literal index " ++ litIntText int ++ " to subscript was out of bounds"
        Just t  -> return (AnnSubscript t base i)

typecheckSubscript rng base baseType index maybeExpTy =
    tcFails $ out $ "Unable to subscript expression of type " ++ show baseType
                ++ " with expression " ++ show index
                ++ " (context expected type " ++ show maybeExpTy ++ ")"
                ++ highlightFirstLine rng

-----------------------------------------------------------------------

-- Maps (a -> b)   or   ForAll [...] (a -> b)    to a.
getFnArgType :: TypeAST -> TypeAST
getFnArgType (FnTypeAST a r cs) = a
getFnArgType t@(ForAll tvs rho) =
    let fnargty = getFnArgType rho in
    trace ("getFnArgType " ++ show t ++ " ::> " ++ show fnargty) $ fnargty
getFnArgType x = error $ "Called argType on non-FnTypeAST: " ++ show x

irrelevantClosedOverVars = Nothing

typecheckCallWithBaseFnType eargs eb range =
    case (typeAST eb, typeAST (AnnTuple eargs)) of
         (FnTypeAST formaltype restype cs, argtype) -> do
           equateTypes formaltype argtype (Just $ "CallAST mismatch between formal & arg types" ++ show range)
           return (AnnCall range restype eb eargs)
         otherwise -> do
            ebStruct <- tcShowStructure eb
            tcFails $ (out $ "CallAST w/o FnAST type: ") ++ ebStruct
                                       ++ (out $ " :: " ++ (show $ typeAST eb))

-- If we have an explicit redex (call to a literal function),
-- we can determine the types of the formals based on the actuals.
typecheckCall ctx range base@(E_FnAST f) args maybeExpTy = do
   ea@(AnnTuple eargs) <- typecheck ctx (E_TupleAST args) Nothing
   m <- newTcUnificationVar
   let expectedLambdaType = case maybeExpTy of
        Nothing  -> (Just (FnTypeAST (typeAST ea) (MetaTyVar m) irrelevantClosedOverVars))
        (Just t) -> (Just (FnTypeAST (MetaTyVar m)     t        irrelevantClosedOverVars))

   eb <- typecheck ctx base expectedLambdaType
   trace ("typecheckCall with literal fn base, exp ty " ++ (show expectedLambdaType)) $
    typecheckCallWithBaseFnType eargs eb range

-- Otherwise, typecheck the function first, then the args.
typecheckCall ctx range base args maybeExpTy = do
   expectedLambdaType <- case maybeExpTy of
        Nothing  -> return $ Nothing
        (Just t) -> do m <- newTcUnificationVar
                       return $ Just (FnTypeAST (MetaTyVar m) t irrelevantClosedOverVars)
        -- If we have (e1 e2) :: T, we infer that e1 :: (? -> T) and e2 :: ?

   eb <- typecheck ctx base expectedLambdaType
   case (typeAST eb) of
      (ForAll tyvars rho) -> do
         let (FnTypeAST rhoArgType _ _) = trace ("forall: " ++ highlightFirstLine range) rho
         --                  rhoargtype =   ('a -> 'b)
         -- base has type ForAll ['a 'b]   (('a -> 'b) -> (Coro 'a 'b))
         -- The forall-bound vars won't unify with concrete types in the term arg,
         -- so we replace the forall-bound vars with unification variables
         -- when computing the type of the term argument.

         -- That is, instead of checking the args against ('a -> 'b),
         -- we must use unification variables instead:    (?a -> ?b)
         -- and then extract the types from unification
         -- to use as type arguments.

         -- Generate unification vars corresponding to the bound type variables
         unificationVars <- sequence [newTcUnificationVar | _ <- tyvars]
         let tyvarsAndMetavars = (List.zip [T_TyVar tv | tv <- tyvars]
                                          [MetaTyVar u | u <- unificationVars])

         -- (?a -> ?b)
         let unifiableArgType = parSubstTy tyvarsAndMetavars rhoArgType

         -- Type check the args, unifying them
         -- with the expected arg type
         ea@(AnnTuple eargs) <- typecheck ctx (E_TupleAST args) (Just $ unifiableArgType)

         unificationResults <- tcUnifyTypes unifiableArgType (typeAST ea)
         case unificationResults of
           Nothing -> tcFails $ out $ "Failed to determine type arguments to apply!" ++ show range
           Just tysub ->
             -- Suppose typeAST ea = (t1 -> t2):
             -- ((?a -> ?b) -> (Coro ?a ?b))
             let unifiableRhoType = parSubstTy tyvarsAndMetavars rho in
              -- ((t1 -> t2) -> (Coro t1 t2))
             let substitutedFnType = tySubst unifiableRhoType tysub in
             -- eb[tyProjTypes]::substitutedFnType
             let annTyApp = E_AnnTyApp substitutedFnType eb (minimalTuple tyProjTypes)
                  where tyProjTypes = extractSubstTypes unificationVars tysub
             in typecheckCallWithBaseFnType eargs annTyApp range

      (FnTypeAST formaltype restype cs) -> do
            ea@(AnnTuple eargs) <- typecheck ctx (E_TupleAST args) (Just $ getFnArgType (typeAST eb))
            typecheckCallWithBaseFnType eargs eb range

      _ -> tcFails $ out ("Called expression had unexpected type: "
                          ++ show (typeAST eb) ++ highlightFirstLine range)

-----------------------------------------------------------------------

typecheckFn ctx f Nothing =                    typecheckFn' ctx f Nothing  Nothing
typecheckFn ctx f (Just (FnTypeAST s t cs')) = typecheckFn' ctx f (Just s) (Just t)

typecheckFn ctx f (Just t) = tcFails $
                out ("Context of function literal expects non-function type: "
                                ++ show t ++ highlightFirstLine (fnAstRange f))

typecheckFn' :: Context -> FnAST -> Maybe TypeAST -> Maybe TypeAST -> Tc AnnExpr
typecheckFn' ctx f expArgType expBodyType = do
    let fnProtoRawFormals = fnFormals f
    let fnProtoName = fnAstName f
    let fnProtoRetTy = fnRetType f
    _ <- verifyNonOverlappingVariableNames fnProtoName
                                           (map (identPrefix.avarIdent) fnProtoRawFormals)
    uniquelyNamedFormals <- mapM uniquelyName fnProtoRawFormals
    extCtx <- extendContext ctx uniquelyNamedFormals expArgType
    annbody <- typecheck extCtx (fnBody f) expBodyType

    equateTypes fnProtoRetTy (typeAST annbody) (Just $ "return type/body type mismatch in " ++ fnProtoName)

    formalVars <- typeJoinVars uniquelyNamedFormals expArgType
    let argtypes = TupleTypeAST (map avarType formalVars)
    let fnClosedVars = if fnWasToplevel f then Nothing else Just []
    let fnty = FnTypeAST argtypes (typeAST annbody) fnClosedVars
    return (E_AnnFn (AnnFn fnty (Ident fnProtoName irrelevantIdentNum)
                           formalVars annbody fnClosedVars))

-----------------------------------------------------------------------
typecheckTuple ctx exprs Nothing = typecheckTuple' ctx exprs [Nothing | e <- exprs]

typecheckTuple ctx exprs (Just (TupleTypeAST ts)) =
    if length exprs /= length ts
      then tcFails $ out $ "typecheckTuple: length of tuple (" ++ (show $ length exprs) ++
                        ") and expected tuple (" ++ (show $ length ts) ++
                        ") types did not agree:\n"
                            ++ show exprs ++ " versus \n" ++ show ts
      else typecheckTuple' ctx exprs [Just t | t <- ts]

-- terrible, no good, very bad hack
typecheckTuple ctx exprs (Just (MetaTyVar mtv)) =
  typecheckTuple' ctx exprs [Nothing | _ <- exprs]

typecheckTuple ctx es (Just ty)
    = tcFails $ out $ "typecheck: tuple (" ++ show es ++ ") cannot check against non-tuple type " ++ show ty

typecheckTuple' ctx es ts = do
        let ets = List.zip es ts -- :: [(ExprAST, TypeAST)]
        let subparts = map (\(e,t) -> typecheck ctx e t) ets
        subAnnots <- sequence $ liftM wasSuccessful subparts

        if Prelude.and subAnnots
            then do { subexprs <- sequence subparts
                    ; return (AnnTuple subexprs)
                    }
            else do { errmsgs <- sequence $ map collectErrors subparts
                    ; tcFails $ concat errmsgs }
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
    return (AnnInt (NamedTypeAST $ "i" ++ show maxBits) int)

-- Given "raw" integer text like "123`456_10",
-- return ("123456", 10)
extractCleanBase :: String -> Tc (String, Int)
extractCleanBase text = do
    let noticks = Prelude.filter (/= '`') text
    case splitString "_" noticks of
        [first, base] -> return (first, read base)
        [first]       -> return (first, 10)
        otherwise     -> tcFails (outLn $ "Unable to parse integer literal " ++ text)

-----------------------------------------------------------------------

splitString :: String -> String -> [String]
splitString needle haystack =
    let textParts = T.splitOn (T.pack needle) (T.pack haystack) in
    map T.unpack textParts

collectErrors :: Tc a -> Tc Output
collectErrors tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       OK expr     -> return (OK [])
                       Errors ss -> return   (OK ss)
                       })

safeListIndex :: [a] -> Int -> Maybe a
safeListIndex lst idx =
    if List.length lst <= idx
        then Nothing
        else Just $ lst !! idx

rename :: Ident -> Uniq -> Ident
rename (Ident p i) u = (Ident p u)

uniquelyName :: AnnVar -> Tc AnnVar
uniquelyName (AnnVar ty id) = do
    uniq <- newTcUniq
    return (AnnVar ty (rename id uniq))

verifyNonOverlappingVariableNames :: String -> [String] -> Tc AnnExpr
verifyNonOverlappingVariableNames fnName varNames = do
    let duplicates = [List.head dups
                     | dups <- List.group (List.sort varNames)
                     , List.length dups > 1]
    case duplicates of
        []        -> return (AnnBool True)
        otherwise -> tcFails $ out $ "Error when checking " ++ fnName
                                    ++ ": had duplicated formal parameter names: " ++ show duplicates

