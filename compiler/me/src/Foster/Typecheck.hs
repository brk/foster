module Foster.Typecheck where

import Data.Map(Map)
import qualified Data.Map as Map
import List(length, zip, zip3, all, sort, group, head, elem, lookup, elemIndex)
import Monad(liftM)

import Debug.Trace(trace)
import Control.Exception(assert)
import Data.Maybe(isJust, fromJust)
import qualified Data.Text as T

import System.Console.ANSI

import Foster.Base
import Foster.TypeAST
import Foster.ExprAST
import Foster.Infer
import Foster.Context

-----------------------------------------------------------------------

typeJoinVars :: [AnnVar] -> (Maybe TypeAST) -> [AnnVar]
typeJoinVars vars (Nothing) = vars
typeJoinVars vars (Just (MissingTypeAST _)) = vars
typeJoinVars vars (Just (TupleTypeAST expTys)) =
    Control.Exception.assert ((List.length vars) == (List.length expTys)) $
    [(AnnVar (fromJust (typeJoin t e)) v) | ((AnnVar t v), e) <- (List.zip vars expTys)]


extractBindings :: [AnnVar] -> Maybe TypeAST -> [ContextBinding]
extractBindings fnProtoFormals maybeExpTy =
    let bindingForVar v = TermVarBinding (identPrefix $ avarIdent v) v in
    let bindings = map bindingForVar (typeJoinVars fnProtoFormals maybeExpTy) in
    trace ("extractBindings: " ++ show bindings) $
      bindings

extendContext :: Context -> [AnnVar] -> Maybe TypeAST -> Context
extendContext ctx protoFormals expFormals =
    prependContextBindings ctx (extractBindings protoFormals expFormals)


typeJoin :: TypeAST -> TypeAST -> Maybe TypeAST
typeJoin (MissingTypeAST _) x = Just x
typeJoin x (MissingTypeAST _) = Just x
typeJoin x y = if x == y then Just x else Nothing

sanityCheck :: Bool -> String -> Tc AnnExpr
sanityCheck cond msg = if cond then do return (AnnBool True)
                               else tcFails (outCSLn Red msg)

typecheck :: Context -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheck ctx expr maybeExpTy =
  tcWithScope expr $
    do case expr of
        E_BoolAST rng b -> do return (AnnBool b)
        E_IfAST ifast   -> typecheckIf ctx ifast maybeExpTy
        E_FnAST f       -> typecheckFn ctx  f    maybeExpTy
        E_CallAST rng call -> typecheckCall ctx rng call maybeExpTy
        E_IntAST rng txt -> typecheckInt rng txt
        E_SeqAST a b -> do
            ea <- typecheck ctx a Nothing --(Just TypeUnitAST)
            eb <- typecheck ctx b maybeExpTy
            return (AnnSeq ea eb)
        E_SubscriptAST  a b    -> do ta <- typecheck ctx a Nothing
                                     tb <- typecheck ctx b Nothing
                                     typecheckSubscript ta (typeAST ta) tb maybeExpTy
        E_TupleAST  exprs b   -> typecheckTuple ctx exprs b maybeExpTy
        E_VarAST mt s -> case termVarLookup s (contextBindings ctx) of
            Just avar  -> return $ E_AnnVar avar
            Nothing    -> tcFails $ out $ "Unknown variable " ++ s
        E_CompilesAST e c -> case c of
            CS_WouldNotCompile -> return $ AnnCompiles CS_WouldNotCompile "parse error"
            CS_WouldCompile -> error "No support for re-type checking CompilesAST nodes."
            CS_NotChecked -> do
                maybeOutput <- extractErrors (typecheck ctx e Nothing)
                return $ case maybeOutput of
                            Nothing -> AnnCompiles CS_WouldCompile    ""
                            Just o  -> AnnCompiles CS_WouldNotCompile (outToString o)

-----------------------------------------------------------------------
typecheckIf ctx (IfAST a b c) maybeExpTy = do
    ea <- typecheck ctx a (Just fosBoolType)
    eb <- typecheck ctx b maybeExpTy
    ec <- typecheck ctx c maybeExpTy
    _  <- sanityCheck (isJust $ typeJoin (typeAST ea) fosBoolType)
                      "IfAST: type of conditional wasn't boolean"
    _  <- sanityCheck (isJust $ typeJoin (typeAST eb) (typeAST ec))
                      "IfAST: types of branches didn't match"
    return (AnnIf (typeAST eb) ea eb ec)

safeListIndex :: [a] -> Int -> Maybe a
safeListIndex lst idx =
    if List.length lst <= idx
        then Nothing
        else Just $ lst !! idx

typecheckSubscript base (TupleTypeAST types) i@(AnnInt ty int) maybeExpTy =
    let literalValue = read (litIntText int) :: Integer in
    case safeListIndex types (fromInteger literalValue) of
        Nothing -> tcFails $ out $ "Literal index " ++ litIntText int ++ " to subscript was out of bounds"
        Just t  -> return (AnnSubscript t base i)

typecheckSubscript base baseType index maybeExpTy =
       tcFails $ out $ "SubscriptAST " ++ show baseType ++ "[" ++ show index ++ "]" ++ " (:: " ++ show maybeExpTy ++ ")"

getFnArgType :: TypeAST -> TypeAST
getFnArgType (FnTypeAST a r cs) = a
getFnArgType t@(ForAll tvs rho) =
    let fnargty = getFnArgType rho in
    trace ("getFnArgType " ++ show t ++ " ::> " ++ show fnargty) $ fnargty
getFnArgType x = error $ "Called argType on non-FnTypeAST: " ++ show x

irrelevantClosedOverVars = Nothing

-- Example: argtype:             ((Coro i32 i32), i32)
--          eb:
--  typeAST eb: (ForAll ['a,'b]. (((Coro 'a 'b), 'a) -> 'b))
--  getFnArgType $ typeAST eb:    ((Coro 'a 'b), 'a)
-- So we unify the type of the actual argument
-- with the arg type under the forall, and the
-- resulting substitution tells us what type application to produce.
-- Much of the complexity here comes from the fact that we distinguish between
-- forall-bound tyvars and meta type variables (aka unification variables).
implicitTypeProjection :: [TyVar] -> TypeAST -> AnnExpr -> TypeAST -> ESourceRange -> Tc AnnExpr
implicitTypeProjection tyvars rho eb argtype range = do
    unificationVars <- sequence [newTcUnificationVar | _ <- tyvars]
    let (FnTypeAST rhoArgType _ _) = rho
    let t_tyvars = [T_TyVar tv | tv <- tyvars]
    let unifiableArgType = parSubstTy (List.zip t_tyvars [MetaTyVar u | u <- unificationVars]) rhoArgType
    case unifyTypes unifiableArgType argtype of
        Nothing -> error $ "Failed to determine type arguments to apply!" ++ show range
        (Just tysub) ->
            let tyProjTypes = extractSubstTypes unificationVars tysub in
            let unifiableRhoType = parSubstTy (List.zip t_tyvars [MetaTyVar u | u <- unificationVars]) rho in
            let substRho = tySubst unifiableRhoType tysub in
            return $ E_AnnTyApp substRho eb (minimalTuple tyProjTypes)


typecheckCallWithBaseFnType ea eb range call =
    case (typeAST eb, typeAST ea) of
         (FnTypeAST formaltype restype cs, argtype) ->
            if isJust $ typeJoin formaltype argtype
                then return (AnnCall range restype eb ea)
                else do ebStruct <- tcShowStructure eb
                        eaStruct <- tcShowStructure ea
                        tcFails $ (out $ "CallAST mismatches:\n"
                                       ++ "base: ") ++ (ebStruct) ++ (out $ "\n"
                                       ++ "arg : ") ++ (eaStruct) ++ (out $ "\n"
                                       ++ show formaltype ++ "\nvs\n" ++ show argtype ++ "\nrange:\n" ++ show range)
         otherwise -> do
            ebStruct <- tcShowStructure eb
            tcFails $ (out $ "CallAST w/o FnAST type: ") ++ ebStruct
                                       ++ (out $ " :: " ++ (show $ typeAST eb))

typecheckCall ctx range call maybeExpTy =
      -- If we have an explicit redex (call to a literal function),
      -- we can determine the types of the formals based on the actuals.
      let (base, args) = (callASTbase call, callASTargs call) in
      case base of
        (E_FnAST f) -> do
           ea <- typecheck ctx args Nothing
           let expectedLambdaType = case maybeExpTy of
                Nothing  -> (Just (FnTypeAST (typeAST ea) (MissingTypeAST "typecheckCall-3")  irrelevantClosedOverVars))
                (Just t) -> (Just (FnTypeAST (MissingTypeAST "typecheckCall-2") t irrelevantClosedOverVars))

           eb <- typecheck ctx base expectedLambdaType
           trace ("typecheckCall with literal fn base, exp ty " ++ (show expectedLambdaType)) $
            typecheckCallWithBaseFnType ea eb range call

        -- Otherwise, typecheck the function first, then the args.
        _ -> do
           let expectedLambdaType = case maybeExpTy of
                Nothing  -> Nothing
                (Just t) -> (Just (FnTypeAST (MissingTypeAST "typecheckCall-1") t irrelevantClosedOverVars))
                -- If we have (e1 e2) :: T, we infer that e1 :: (? -> T) and e2 :: ?

           eb <- typecheck ctx base expectedLambdaType
           case (typeAST eb) of
              (ForAll tyvars rho) -> do
                    let (FnTypeAST rhoArgType _ _) = rho
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
                    ea <- typecheck ctx args (Just $ unifiableArgType)

                    case unifyTypes unifiableArgType (typeAST ea) of
                      Nothing -> tcFails $ out $ "Failed to determine type arguments to apply!" ++ show range
                      Just tysub ->
                        let tyProjTypes = extractSubstTypes unificationVars tysub in
                        let unifiableRhoType = parSubstTy tyvarsAndMetavars rho in
                        let substitutedFnType = tySubst unifiableRhoType tysub in
                        let annTyApp = E_AnnTyApp substitutedFnType eb (minimalTuple tyProjTypes) in
                        typecheckCallWithBaseFnType ea annTyApp range call

              (FnTypeAST formaltype restype cs) -> do
                    ea <- typecheck ctx args (Just $ getFnArgType (typeAST eb))
                    typecheckCallWithBaseFnType ea eb range call

-----------------------------------------------------------------------

typecheckFn ctx f Nothing = typecheckFn' ctx f Nothing Nothing
typecheckFn ctx f (Just (FnTypeAST s t cs')) =
    let proto = fnProto f in
    if isJust $ typeJoin (prototypeASTretType proto)   t
      then typecheckFn' ctx f (Just s) (Just t)
      else tcFails $ out $ "typecheck fn '" ++ prototypeASTname proto
                        ++ "': proto return type, " ++ show (prototypeASTretType proto)
                        ++ ", did not match return type of expected fn type " ++ show (FnTypeAST s t cs')

rename :: Ident -> Uniq -> Ident
rename (Ident p i) u = (Ident p u)

uniquelyName :: AnnVar -> Tc AnnVar
uniquelyName (AnnVar ty id) = do
    uniq <- newTcUniq
    return (AnnVar ty (rename id uniq))

typecheckFn' :: Context -> FnAST -> Maybe TypeAST -> Maybe TypeAST -> Tc AnnExpr
typecheckFn' ctx f expArgType expBodyType = do
    let (PrototypeAST fnProtoRetTy fnProtoName fnProtoRawFormals) = fnProto f
    _ <- verifyNonOverlappingVariableNames fnProtoName
                                           (map (identPrefix.avarIdent) fnProtoRawFormals)
    uniquelyNamedFormals <- mapM uniquelyName fnProtoRawFormals
    let extCtx = extendContext ctx uniquelyNamedFormals expArgType
    annbody <- typecheck extCtx (fnBody f) expBodyType
    case typeJoin fnProtoRetTy (typeAST annbody) of
        (Just someReturnType) ->
            let annproto = (AnnPrototype someReturnType
                                         (Ident fnProtoName irrelevantIdentNum)
                                         (typeJoinVars uniquelyNamedFormals expArgType)) in
            let argtypes = TupleTypeAST [avarType v | v <- (annProtoVars annproto)] in
            let fnty = FnTypeAST argtypes someReturnType (fnTypeCloses' f) in
            return (E_AnnFn (AnnFn fnty annproto annbody (fnClosedVars f)))
        otherwise ->
         tcFails $ out $ "typecheck '" ++ fnProtoName
                    ++ "': proto ret type " ++ show fnProtoRetTy
                    ++ " did not match body type " ++ show (typeAST annbody)

verifyNonOverlappingVariableNames :: String -> [String] -> Tc AnnExpr
verifyNonOverlappingVariableNames fnName varNames = do
    let duplicates = [List.head dups
                     | dups <- List.group (List.sort varNames)
                     , List.length dups > 1]
    case duplicates of
        []        -> return (AnnBool True)
        otherwise -> tcFails $ out $ "Error when checking " ++ fnName
                                    ++ ": had duplicated formal parameter names: " ++ show duplicates

-----------------------------------------------------------------------
typecheckTuple ctx exprs b Nothing = typecheckTuple' ctx exprs b [Nothing | e <- exprs]

typecheckTuple ctx exprs b (Just (TupleTypeAST ts)) =
    if length exprs /= length ts
      then tcFails $ out $ "typecheckTuple: length of tuple (" ++ (show $ length exprs) ++
                        ") and expected tuple (" ++ (show $ length ts) ++
                        ") types did not agree:\n"
                            ++ show exprs ++ " versus \n" ++ show ts
      else typecheckTuple' ctx exprs b [Just t | t <- ts]

typecheckTuple ctx es b (Just ty)
    = tcFails $ out $ "typecheck: tuple (" ++ show es ++ ") cannot check against non-tuple type " ++ show ty

typecheckTuple' ctx es b ts = do
        let ets = List.zip es ts -- :: [(ExprAST, TypeAST)]
        let subparts = map (\(e,t) -> typecheck ctx e t) ets
        subAnnots <- sequence $ liftM wasSuccessful subparts

        if Prelude.and subAnnots
            then do { subexprs <- sequence subparts
                    ; return (AnnTuple subexprs b)
                    }
            else do { errmsgs <- sequence $ map collectErrors subparts
                    ; tcFails $ concat errmsgs }
-----------------------------------------------------------------------
collectErrors :: Tc a -> Tc Output
collectErrors tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       OK expr     -> return (OK [])
                       Errors ss -> return   (OK ss)
                       })


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

splitString :: String -> String -> [String]
splitString needle haystack =
    let textParts = T.splitOn (T.pack needle) (T.pack haystack) in
    map T.unpack textParts
