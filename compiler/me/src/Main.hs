-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Main (
main
) where

import System.Environment(getArgs,getProgName)

import qualified Data.ByteString.Lazy as L(readFile)
import qualified Data.ByteString.Lazy.UTF8 as U(toString)
import qualified System.IO.UTF8 as U(putStrLn)

import Test.HUnit
import Debug.Trace(trace)
import Control.Exception(assert)

import List(length, zip, all, sort, group, head)
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Graph(Graph)
import qualified Data.Graph as Graph
import Data.Maybe(isJust, fromJust, fromMaybe)
import Data.Foldable(forM_)
import Control.Monad(forM)
import Monad(join,liftM)
import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Text.ProtocolBuffers(messageGet)

import System.Console.ANSI
import Foster.Base
import Foster.ProtobufUtils
import Foster.ExprAST
import Foster.TypeAST

-----------------------------------------------------------------------

typeJoinVars :: [AnnVar] -> (Maybe TypeAST) -> [AnnVar]
typeJoinVars vars (Nothing) = vars
typeJoinVars vars (Just (MissingTypeAST _)) = vars
typeJoinVars vars (Just (TupleTypeAST expTys)) =
    Control.Exception.assert ((List.length vars) == (List.length expTys)) $
    [(AnnVar (fromJust (typeJoin t e)) v) | ((AnnVar t v), e) <- (List.zip vars expTys)]


extractBindings :: [AnnVar] -> Maybe TypeAST -> Context
extractBindings fnProtoFormals maybeExpTy =
    let bindingForVar v = TermVarBinding (identPrefix $ avarIdent v) v in
    let bindings = map bindingForVar (typeJoinVars fnProtoFormals maybeExpTy) in
    trace ("extractBindings: " ++ show bindings) $
      bindings

data ContextBinding = TermVarBinding String AnnVar
type Context = [ContextBinding]


instance Show ContextBinding where
    show (TermVarBinding s ty) = "(termvar " ++ s ++ " :: " ++ show ty

extendContext :: Context -> [AnnVar] -> Maybe TypeAST -> Context
extendContext ctx protoFormals expFormals = (extractBindings protoFormals expFormals) ++ ctx

termVarLookup :: String -> Context -> Maybe AnnVar
termVarLookup name (bindings) =
    let termbindings = [(nm, annvar) | (TermVarBinding nm annvar) <- bindings] in
    lookup name termbindings

-- Either, with better names for the cases...
data TypecheckResult expr
    = Annotated        expr
    | TypecheckErrors  Output
    deriving (Eq)

-- Based on "Practical type inference for arbitrary rank types."
-- One significant difference is that we do not include the Gamma context
--   (mapping term variables to types) in the TcEnv, because we do not
--   want that part of the context "threaded through" type checking of
--   subexpressions. For example, we want each function in a SCC
--   of functions to be type checked in the same Gamma context. But
--   we do need to thread the supply of unique variables through...
data TcEnv = TcEnv { tcEnvUniqs :: IORef Uniq
                   }

newtype Tc a = Tc (TcEnv -> IO (TypecheckResult a))
unTc :: Tc a ->   (TcEnv -> IO (TypecheckResult a))
unTc   (Tc a) = a

instance Monad Tc where
    return x = Tc (\_env -> return (Annotated x))
    fail err = Tc (\_env -> return (TypecheckErrors (outLn err)))
    m >>= k = Tc (\env -> do { result <- unTc m env
                          ; case result of
                              Annotated expr -> unTc (k expr) env
                              TypecheckErrors ss -> return (TypecheckErrors ss)
                          })

newUniq :: Tc Uniq
newUniq = Tc (\tcenv -> do { let ref = tcEnvUniqs tcenv
                          ; uniq <- readIORef ref
                          ; writeIORef ref (uniq + 1)
                          ; return (Annotated uniq)
                          })

tcFails :: Output -> Tc a
tcFails errs = Tc (\_env -> return (TypecheckErrors errs))

wasSuccessful :: Tc a -> Tc Bool
wasSuccessful tce =
    Tc (\env -> do { result <- unTc tce env
                   ; case result of
                       Annotated expr     -> return (Annotated True)
                       TypecheckErrors ss -> return (Annotated False)
                       })

typeJoin :: TypeAST -> TypeAST -> Maybe TypeAST
typeJoin (MissingTypeAST _) x = Just x
typeJoin x (MissingTypeAST _) = Just x
typeJoin x y = if x == y then Just x else Nothing

sanityCheck :: Bool -> String -> Tc AnnExpr
sanityCheck cond msg = if cond then do return (AnnBool True)
                               else tcFails (outCSLn Red msg)

typecheck :: Context -> ExprAST -> Maybe TypeAST -> Tc AnnExpr
typecheck ctx expr maybeExpTy =
    case expr of
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
        E_VarAST mt s -> case termVarLookup s ctx of
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

            tcFails $ (out $ "CallAST against non-instantiated ForAll type: " ++ show (ForAll tvs rho)
                                ++ "\n") ++ (showStructure eb) ++ (out $ " :: " ++ (show $ typeAST eb)
                                ++ "\n" ++ "argType: " ++ show argtype
                                ++ "\n" ++ show range)

         (FnTypeAST formaltype restype cs, argtype) ->
            if isJust $ typeJoin formaltype argtype
                then return (AnnCall range restype eb ea)
                else tcFails $ (out $ "CallAST mismatches:\n"
                                       ++ "base: ") ++ (showStructure eb) ++ (out $ "\n"
                                       ++ "arg : ") ++ (showStructure ea) ++ (out $ "\n"
                                       ++ show formaltype ++ "\nvs\n" ++ show argtype ++ "\nrange:\n" ++ show range)
         otherwise -> tcFails $ (out $ "CallAST w/o FnAST type: ") ++ (showStructure eb)
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

isAnnotated :: TypecheckResult AnnExpr -> Bool
isAnnotated (Annotated _) = True
isAnnotated _ = False
{-
errsTypecheckResult :: TypecheckResult AnnExpr -> [String]
errsTypecheckResult (Annotated _) = []
errsTypecheckResult (TypecheckErrors es) = es

collectErrors :: [TypecheckResult AnnExpr] -> [String]
collectErrors results =
    [e | r <- results, e <- errsTypecheckResult r, e /= ""]
    -}

-----------------------------------------------------------------------

computeRootContext :: Uniq -> (Context, Uniq)
computeRootContext u =
    let pair2binding (nm, ty) uniq = (tvb, uniq + 1)
            where tvb = TermVarBinding nm (AnnVar ty (Ident nm (- uniq)))
    in
    stFold pair2binding rootContextPairs u

stFold :: (a -> s -> (b, s)) -> [a] -> s -> ([b], s)
stFold f [] u = ([], u)
stFold f (a:as) u = let (b,u') = f a u in
                    let (bs,ufin) = stFold f as u' in
                    ((b:bs), ufin)

isPrimitiveName name rootContext = isJust $ termVarLookup name rootContext

fnName :: FnAST -> String
fnName f = prototypeASTname (fnProto f)

fnFreeVariables :: FnAST -> Context -> [String]
fnFreeVariables f ctx =
    let allCalledFns = Set.fromList $ freeVariables (fnBody f) in
    -- remove names of primitive functions
    let nonPrimitives = Set.filter (\var -> not (isJust $ termVarLookup var ctx)) allCalledFns in
    -- remove recursive function name calls
    Set.toList $ Set.filter (\name -> prototypeASTname (fnProto f) /= name) nonPrimitives

buildCallGraph :: [FnAST] -> Context -> [Graph.SCC FnAST]
buildCallGraph asts ctx =
    let nodeList = (map (\ast -> (ast, fnName ast, fnFreeVariables ast ctx)) asts) in
    Graph.stronglyConnComp nodeList

fnNameA :: AnnFn -> String
fnNameA f = identPrefix $ annProtoIdent (annFnProto f)

annFnVar f = AnnVar (annFnType f) (annProtoIdent $ annFnProto f)

extendContextWithFnA :: AnnFn -> Context -> Context
extendContextWithFnA f ctx = (TermVarBinding (fnNameA f) (annFnVar f)):ctx

fnTypeFrom :: FnAST -> TypeAST
fnTypeFrom f =
    let intype = TupleTypeAST [avarType v | v <- prototypeASTformals (fnProto f)] in
    let outtype = prototypeASTretType (fnProto f) in
    FnTypeAST intype outtype (fmap (map $ show.avarIdent) (fnClosedVars f))

fnVar f = AnnVar (fnTypeFrom f) (Ident (fnName f) (-12345))

extendContextWithFn :: FnAST -> Context -> Context
extendContextWithFn f ctx = (TermVarBinding (fnName f) (fnVar f)):ctx

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Graph.SCC FnAST -> (Context, TcEnv) -> IO ([TypecheckResult AnnExpr], (Context, TcEnv))
typecheckFnSCC scc (ctx, tcenv) = do
    let fns = Graph.flattenSCC scc
    annfns <- forM fns $ \ast -> do
        let name = fnName ast
        putStrLn $ "typechecking " ++ name
        let extctx = extendContextWithFn ast ctx
        typechecked <- unTc (typecheck extctx (E_FnAST ast) Nothing) tcenv
        inspect typechecked (E_FnAST ast)
        return typechecked
    return $ if allAnnotated annfns
        then let fns = [f | (Annotated (E_AnnFn f)) <- annfns] in
             let newcontext = foldr extendContextWithFnA ctx fns in
             (annfns, (newcontext, tcenv))
        else ([TypecheckErrors (out $ "not all functions type checked correctly in SCC: "
                                ++ show [fnName f | f <- fns])
              ],(ctx, tcenv))

--foldMap :: [Graph.SCC FnAST] -> Context -> (Graph.SCC FnAST -> Context -> IO ([TypecheckResult AnnExpr], Context)) -> ...
--foldMap :: [[FnAST]] -> Context -> ([FnAST] -> Context -> IO ([TypecheckResult AnnExpr], Context)) -> IO ([TypecheckResult AnnExpr], Context)

mapFoldM :: (Monad m) => [a] -> b -> (a -> b -> m ([c], b)) -> m ([c], b)
mapFoldM []  b  f    = fail "mapFoldM must be given a non-empty list"
mapFoldM [a] b1 f    = f a b1
mapFoldM (a:as) b1 f = do
    (cs1, b2) <- f a b1
    (cs2, b3) <- mapFoldM as b2 f
    return (cs1 ++ cs2, b3)

typecheckModule :: ModuleAST FnAST -> TcEnv -> IO (Maybe (ModuleAST AnnFn))
typecheckModule mod tcenv = do
    let fns = moduleASTfunctions mod
    let (ctx, u) = computeRootContext 1
    let sortedFns = buildCallGraph fns ctx -- :: [SCC FnAST]
    putStrLn $ "Function SCC list : " ++ show [(fnName f, fnFreeVariables f ctx) | fns <- sortedFns, f <- Graph.flattenSCC fns]
    (annFns, _ctx) <- mapFoldM sortedFns (ctx, tcenv) typecheckFnSCC
    -- annFns :: [TypecheckResult AnnExpr]
    if allAnnotated annFns
        then return $ Just (ModuleAST [f | (Annotated (E_AnnFn f)) <- annFns] (moduleASTsourceLines mod))
        else return $ Nothing

allAnnotated :: [TypecheckResult AnnExpr] -> Bool
allAnnotated results = List.all isAnnotated results

inspect :: TypecheckResult AnnExpr -> ExprAST -> IO Bool
inspect typechecked ast =
    case typechecked of
        Annotated e -> do
            putStrLn $ "Successful typecheck!"
            runOutput $ showStructure e
            return True
        TypecheckErrors errs -> do
            runOutput $ showStructure ast
            forM_ errs $ \err -> do runOutput $ (outCSLn Red "Typecheck error: ") ++ [err]
            return False

-----------------------------------------------------------------------


main :: IO ()
main = do
  args <- getArgs
  (f, outfile) <- case args of
         ["--test"] -> do
                runUnitTests
                return (error $ "Done running unit tests...")
         [infile, outfile] -> do
                protobuf <- L.readFile infile
                return (protobuf, outfile)
         _ -> do
                self <- getProgName
                return (error $ "Usage: " ++ self ++ " path/to/infile.pb path/to/outfile.pb")

  case messageGet f of
    Left msg -> error ("Failed to parse protocol buffer.\n"++msg)
    Right (pb_exprs,_) -> do
        let sm = parseSourceModule pb_exprs
        uniqref <- newIORef 1
        let tcenv = TcEnv { tcEnvUniqs = uniqref }
        elabModule <- typecheckModule sm tcenv
        case elabModule of
            (Just mod) -> dumpModuleToProtobuf mod outfile
            Nothing    -> error $ "Unable to type check input module!"


-----------------------------------------------------------------------
{-
trMaybe :: TypecheckResult AnnExpr -> Maybe AnnExpr
trMaybe (TypecheckErrors _) = Nothing
trMaybe (Annotated ae) = Just $ ae

test1 = let term = (E_BoolAST (EMissingSourceRange "") True) in
        let expectedType = Nothing in
        let anticipated = (AnnBool True) in
        TestCase (do let taa = trMaybe $ typecheck rootContext term expectedType
                     assertEqual ("for " ++ show term ++ ", ")
                             (fmap showStructure (Just anticipated))
                             (fmap showStructure taa))

-- |- (\x.e) (coro_create_i32(...))  ==> (\x:Coro i32 i32.e)
--test2 = let proto = (PrototypeAST protoRetTy "f" [(VarAST "v" )] ) in
--        let body = in
--        let term = (FnAST proto body Nothing) in
--        let expectedType = Nothing in
--        let anticipated = (AnnBool True) in
--        TestCase (do let taa = trMaybe $ typecheck rootContext term expectedType
--                     assertEqual ("for " ++ show term ++ ", ")
--                             (fmap showStructureA (Just anticipated))
--                             (fmap showStructureA taa))
--
tests = TestList [TestLabel "test1" test1
                 --,TestLabel "test2" test2
                 ]
-}
runUnitTests = do return ()
--    runTestTT tests
