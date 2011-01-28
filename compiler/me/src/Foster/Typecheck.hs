module Foster.Typecheck where

import Data.Map(Map)
import qualified Data.Map as Map
import List(length, zip, zip3, all, sort, group, head, elem, lookup)
import Monad(liftM)

import Debug.Trace(trace)
import Control.Exception(assert)
import Data.Maybe(isJust, fromJust)

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
        E_IntAST litInt -> do return (AnnInt (NamedTypeAST "i32") litInt)
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
            CS_NotChecked -> do
                success <- wasSuccessful (typecheck ctx e Nothing)
                return $ AnnCompiles $ case success of
                            True  -> CS_WouldCompile
                            False -> CS_WouldNotCompile
            otherwise -> return $ AnnCompiles c

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

typecheckCall' ea eb range call =
    case (typeAST eb, typeAST ea) of
         ((ForAll tvs rho), argtype) ->
            -- Example: argtype:             ((Coro i32 i32), i32)
            --          eb:
            --  typeAST eb: (ForAll ['a,'b]. (((Coro 'a 'b), 'a) -> 'b))
            --  getFnArgType $ typeAST eb:    ((Coro 'a 'b), 'a)
            -- So we unify the type of the actual argument
            -- with the arg type under the forall, and the
            -- resulting substitution tells us what type application to produce.
            --typecheckCall' ea (E_AnnTyApp eb argtype) range call

            do ebStruct <- tcShowStructure eb
               tcFails $ ebStruct ++ (out $ "CallAST against non-instantiated ForAll type: " ++ show (ForAll tvs rho)
                                ++ "\n :: " ++ (show $ typeAST eb)
                                ++ "\n" ++ "argType: " ++ show argtype
                                ++ "\n" ++ show range
                                ++ "\n" ++ "====================")

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
            typecheckCall' ea eb range call

        -- Otherwise, typecheck the function first, then the args.
        _ -> do
           let expectedLambdaType = case maybeExpTy of
                Nothing  -> Nothing
                (Just t) -> (Just (FnTypeAST (MissingTypeAST "typecheckCall-1") t irrelevantClosedOverVars))
                -- If we have (e1 e2) :: T, we infer that e1 :: (? -> T) and e2 :: ?
           eb <- typecheck ctx base expectedLambdaType
           ea <- typecheck ctx args (Just $ getFnArgType (typeAST eb))
           typecheckCall' ea eb range call

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
    uniq <- newUniq
    return (AnnVar ty (rename id uniq))

typecheckFn' :: Context -> FnAST -> Maybe TypeAST -> Maybe TypeAST -> Tc AnnExpr
typecheckFn' ctx f expArgType expBodyType = do
    let (PrototypeAST fnProtoRetTy fnProtoName fnProtoRawFormals) = fnProto f
    let cs = fnClosedVars f
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
            let fnty = FnTypeAST argtypes someReturnType (fmap (fmap (show.avarIdent)) cs) in
            return (E_AnnFn (AnnFn fnty annproto annbody cs))
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
        -- subparts :: [(TypecheckResult AnnExpr)]
        -- subparts :: [Tc AnnExpr]
        -- sequence subparts :: [AnnExpr]
        subAnnots <- sequence $ liftM wasSuccessful subparts

        if Prelude.and subAnnots
            then do { subexprs <- sequence subparts
                    ; return (AnnTuple subexprs b)
                    }
            else do { errmsgs <- sequence $ map collectErrors subparts
                    ; tcFails $ concat errmsgs }
-- have : cE :: m a -> m b
--              [m a]
-----------------------------------------------------------------------
collectErrors :: Tc a -> Tc Output
collectErrors tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       Annotated expr     -> return (Annotated [])
                       TypecheckErrors ss -> return (Annotated ss)
                       })

