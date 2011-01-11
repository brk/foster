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
--import Data.IORef(IORef,newIORef,readIORef,writeIORef)

import Text.ProtocolBuffers(messageGet)

import Foster.ProtobufUtils
import Foster.ExprAST
import Foster.TypeAST

-----------------------------------------------------------------------

_typesEqual :: TypeAST -> TypeAST -> Bool
_typesEqual (TupleTypeAST as) (TupleTypeAST bs) =
    List.length as == List.length bs && Prelude.and [_typesEqual a b | (a, b) <- Prelude.zip as bs]
_typesEqual (FnTypeAST s1 t1 c1) (FnTypeAST s2 t2 c2) =
    _typesEqual s1 s2 && _typesEqual t1 t2 -- ignore c1 and c2 for now...
_typesEqual ta tb = ta == tb


typeJoinVars :: [AnnVar] -> (Maybe TypeAST) -> [AnnVar]
typeJoinVars vars (Nothing) = vars
typeJoinVars vars (Just (MissingTypeAST _)) = vars
typeJoinVars vars (Just (TupleTypeAST expTys)) =
    Control.Exception.assert ((List.length vars) == (List.length expTys)) $
    [(AnnVar (fromJust (typeJoin t e)) v) | ((AnnVar t v), e) <- (List.zip vars expTys)]


getBindings :: PrototypeAST -> Maybe TypeAST -> Context
getBindings (PrototypeAST t s vars) maybeExpTy =
    let bindingForVar v = TermVarBinding (avarName v) (avarType v) in
    let bindings = map bindingForVar (typeJoinVars vars maybeExpTy) in
    trace ("getBindings: " ++ show bindings) $
      bindings

data ContextBinding = TermVarBinding String TypeAST
type Context = [ContextBinding]


instance Show ContextBinding where
    show (TermVarBinding s ty) = "(termvar " ++ s ++ " :: " ++ show ty

extendContext :: Context -> PrototypeAST -> Maybe TypeAST -> Context
extendContext ctx proto expFormals = (getBindings proto expFormals) ++ ctx

termVarLookup :: String -> Context -> Maybe TypeAST
termVarLookup name (bindings) =
    let termbindings = [(nm, ty) | (TermVarBinding nm ty) <- bindings] in
    lookup name termbindings


data TypecheckResult expr
    = Annotated        expr
    | TypecheckErrors [String]
    deriving (Show, Eq)

instance Functor TypecheckResult where
    fmap f (Annotated e)        = Annotated (f e)
    fmap _ (TypecheckErrors ss) = TypecheckErrors ss

instance Monad TypecheckResult where
    return                   = Annotated
    (TypecheckErrors ss) >>= _ = (TypecheckErrors ss)
    (Annotated e)        >>= f = f e
    fail msg                 = TypecheckErrors [msg]

typeJoin :: TypeAST -> TypeAST -> Maybe TypeAST
typeJoin (MissingTypeAST _) x = Just x
typeJoin x (MissingTypeAST _) = Just x
typeJoin x y = if _typesEqual x y then Just x else Nothing

throwError :: String -> TypecheckResult AnnExpr
throwError s = TypecheckErrors [s]

sanityCheck :: Bool -> String -> TypecheckResult AnnExpr
sanityCheck cond msg = if cond then do return (AnnBool True)
                               else throwError msg

typecheck :: Context -> ExprAST -> Maybe TypeAST -> TypecheckResult AnnExpr
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
            Just t  -> Annotated $ E_AnnVar (AnnVar t s)
            Nothing -> throwError $ "Unknown variable " ++ s
        E_CompilesAST e c -> case c of
            CS_NotChecked ->
              return $ AnnCompiles $ case typecheck ctx e Nothing of
                Annotated ae -> CS_WouldCompile
                otherwise    -> CS_WouldNotCompile
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
        Nothing -> throwError $ "Literal index " ++ litIntText int ++ " to subscript was out of bounds"
        Just t  -> return (AnnSubscript t base i)

typecheckSubscript base baseType index maybeExpTy =
       throwError $ "SubscriptAST " ++ show baseType ++ "[" ++ show index ++ "]" ++ " (:: " ++ show maybeExpTy ++ ")"

argType :: TypeAST -> TypeAST
argType (FnTypeAST a r cs) = a
argType x = error $ "Called argType on non-FnTypeAST: " ++ show x

irrelevantClosedOverVars = Nothing

typecheckCall' ea eb range call =
    case (typeAST eb, typeAST ea) of
         (FnTypeAST formaltype restype cs, argtype) ->
            if isJust $ typeJoin formaltype argtype
                then Annotated (AnnCall range restype eb ea)
                else throwError $ "CallAST mismatches:\n"
                                       ++ "base: " ++ (showStructure eb) ++ "\n"
                                       ++ "arg : " ++ (showStructure ea) ++ "\n"
                                       ++ show formaltype ++ "\nvs\n" ++ show argtype ++ "\nrange:\n" ++ show range
         otherwise -> throwError $ "CallAST w/o FnAST type: " ++ (showStructure eb)
                                       ++ " :: " ++ (show $ typeAST eb)

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
           ea <- typecheck ctx args (Just $ argType (typeAST eb))
           typecheckCall' ea eb range call

-----------------------------------------------------------------------

typecheckFn ctx f Nothing = typecheckFn' ctx f Nothing Nothing
typecheckFn ctx f (Just (FnTypeAST s t cs')) =
    let proto = fnProto f in
    if isJust $ typeJoin (prototypeASTretType proto)   t
      then typecheckFn' ctx f (Just s) (Just t)
      else throwError  $ "typecheck fn '" ++ prototypeASTname proto
                        ++ "': proto return type, " ++ show (prototypeASTretType proto)
                        ++ ", did not match return type of expected fn type " ++ show (FnTypeAST s t cs')

typecheckFn' :: Context -> FnAST -> Maybe TypeAST -> Maybe TypeAST -> TypecheckResult AnnExpr
typecheckFn' ctx f expArgType expBodyType = do
    let proto = fnProto f
    let cs = fnClosedVars f
    _ <- verifyNonOverlappingVariableNames (prototypeASTname proto)
                                           (map avarName (prototypeASTformals proto))
    let extCtx = extendContext ctx proto expArgType
    annbody <- typecheck extCtx (fnBody f) expBodyType
    case typeJoin (prototypeASTretType proto) (typeAST annbody) of
        (Just someReturnType) ->
            let annproto = case proto of
                            (PrototypeAST t s vars) ->
                              (AnnPrototype someReturnType s (typeJoinVars vars expArgType)) in
            let argtypes = TupleTypeAST [avarType v | v <- (annProtoVars annproto)] in
            let fnty = FnTypeAST argtypes someReturnType (fmap (fmap avarName) cs) in
            return (E_AnnFn (AnnFn fnty annproto annbody cs))
        otherwise ->
         throwError $ "typecheck '" ++ prototypeASTname proto
                    ++ "': proto ret type " ++ show (prototypeASTretType proto)
                    ++ " did not match body type " ++ show (typeAST annbody)

verifyNonOverlappingVariableNames :: String -> [String] -> TypecheckResult AnnExpr
verifyNonOverlappingVariableNames fnName varNames = do
    let duplicates = [List.head dups
                     | dups <- List.group (List.sort varNames)
                     , List.length dups > 1]
    case duplicates of
        []        -> return (AnnBool True)
        otherwise -> throwError $ "Error when checking " ++ fnName
                                    ++ ": had duplicated formal parameter names: " ++ show duplicates

-----------------------------------------------------------------------
typecheckTuple ctx exprs b Nothing = typecheckTuple' ctx exprs b [Nothing | e <- exprs]

typecheckTuple ctx exprs b (Just (TupleTypeAST ts)) =
    if length exprs /= length ts
      then throwError $ "typecheckTuple: length of tuple (" ++ (show $ length exprs) ++
                        ") and expected tuple (" ++ (show $ length ts) ++
                        ") types did not agree:\n"
                            ++ show exprs ++ " versus \n" ++ show ts
      else typecheckTuple' ctx exprs b [Just t | t <- ts]

typecheckTuple ctx es b (Just ty)
    = throwError $ "typecheck: tuple (" ++ show es ++ ") cannot check against non-tuple type " ++ show ty

typecheckTuple' ctx es b ts = do
        let ets = List.zip es ts
        let subparts = map (\(e,t) -> typecheck ctx e t) ets
        if Prelude.and (map isAnnotated subparts)
            then return (AnnTuple [part | (Annotated part) <- subparts] b)
            else TypecheckErrors $ collectErrors subparts
-----------------------------------------------------------------------

isAnnotated :: TypecheckResult AnnExpr -> Bool
isAnnotated (Annotated _) = True
isAnnotated _ = False

errsTypecheckResult :: TypecheckResult AnnExpr -> [String]
errsTypecheckResult (Annotated _) = []
errsTypecheckResult (TypecheckErrors es) = es

collectErrors :: [TypecheckResult AnnExpr] -> [String]
collectErrors results =
    [e | r <- results, e <- errsTypecheckResult r, e /= ""]
-----------------------------------------------------------------------

minimalTuple []    = TupleTypeAST []
minimalTuple [arg] = arg
minimalTuple args  = TupleTypeAST args

mkFnType   args rets = FnTypeAST (TupleTypeAST args) (minimalTuple rets) Nothing
mkCoroType args rets =  CoroType (minimalTuple args) (minimalTuple rets)
i32 = (NamedTypeAST "i32")
i64 = (NamedTypeAST "i64")
i1  = (NamedTypeAST "i1")

coroInvokeType args rets = mkFnType ((mkCoroType args rets) : args) rets
coroYieldType  args rets = mkFnType rets args
coroCreateType args rets = mkFnType [mkFnType args rets] [mkCoroType args rets]

rootContext :: Context
rootContext =
    [TermVarBinding "llvm_readcyclecounter" $ mkFnType [] [i64]
    ,TermVarBinding "expect_i32"  $ mkFnType [i32] [i32]
    ,TermVarBinding  "print_i32"  $ mkFnType [i32] [i32]
    ,TermVarBinding "expect_i32b" $ mkFnType [i32] [i32]
    ,TermVarBinding  "print_i32b" $ mkFnType [i32] [i32]
    ,TermVarBinding "expect_i64"  $ mkFnType [i64] [i32]
    ,TermVarBinding  "print_i64"  $ mkFnType [i64] [i32]
    ,TermVarBinding "expect_i64b" $ mkFnType [i64] [i32]
    ,TermVarBinding  "print_i64b" $ mkFnType [i64] [i32]
    ,TermVarBinding   "read_i32"  $ mkFnType  []   [i32]
    ,TermVarBinding "expect_i1"   $ mkFnType [i1] [i32]
    ,TermVarBinding  "print_i1"   $ mkFnType [i1] [i32]

    ,TermVarBinding "coro_create_i32_i32" $ coroCreateType [i32] [i32]
    ,TermVarBinding "coro_invoke_i32_i32" $ coroInvokeType [i32] [i32]
    ,TermVarBinding "coro_yield_i32_i32"  $ coroYieldType  [i32] [i32]

    ,TermVarBinding "coro_create_i32x2_i32" $ coroCreateType [i32, i32] [i32]
    ,TermVarBinding "coro_invoke_i32x2_i32" $ coroInvokeType [i32, i32] [i32]
    ,TermVarBinding "coro_yield_i32x2_i32"  $ coroYieldType  [i32, i32] [i32]

    ,TermVarBinding "coro_create_i32_i32x2" $ coroCreateType [i32] [i32,i32]
    ,TermVarBinding "coro_invoke_i32_i32x2" $ coroInvokeType [i32] [i32,i32]
    ,TermVarBinding "coro_yield_i32_i32x2"  $ coroYieldType  [i32] [i32,i32]


    ,TermVarBinding "primitive_sext_i64_i32" $ mkFnType [i32] [i64]
    ,TermVarBinding "primitive_negate_i32"   $ mkFnType [i32] [i32]
    ,TermVarBinding "primitive_bitnot_i1"    $ mkFnType [i1] [i1]
    ,TermVarBinding "primitive_bitshl_i32"   $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_bitashr_i32"  $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_bitlshr_i32"  $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_bitor_i32"    $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_bitand_i32"   $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_bitxor_i32"   $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "force_gc_for_debugging_purposes" $ mkFnType [] []

    ,TermVarBinding "primitive_<_i64"  $ mkFnType [i64, i64] [i1]
    ,TermVarBinding "primitive_-_i64"  $ mkFnType [i64, i64] [i64]
    ,TermVarBinding "primitive_-_i32"  $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_*_i32"  $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_+_i32"  $ mkFnType [i32, i32] [i32]
    ,TermVarBinding "primitive_<_i32"  $ mkFnType [i32, i32] [i1]
    ,TermVarBinding "primitive_<=_i32" $ mkFnType [i32, i32] [i1]
    ,TermVarBinding "primitive_==_i32" $ mkFnType [i32, i32] [i1]
    ]

isPrimitiveName name = isJust $ termVarLookup name rootContext

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
fnNameA f = annProtoName (annFnProto f)

extendContextWithFnA :: AnnFn -> Context -> Context
extendContextWithFnA f ctx = (TermVarBinding (fnNameA f) (annFnType f)):ctx

fnTypeFrom :: FnAST -> TypeAST
fnTypeFrom f =
    let intype = TupleTypeAST [avarType v | v <- prototypeASTformals (fnProto f)] in
    let outtype = prototypeASTretType (fnProto f) in
    FnTypeAST intype outtype (fmap (map avarName) (fnClosedVars f))

extendContextWithFn :: FnAST -> Context -> Context
extendContextWithFn f ctx = (TermVarBinding (fnName f) (fnTypeFrom f)):ctx

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Graph.SCC FnAST -> Context -> IO ([TypecheckResult AnnExpr], Context)
typecheckFnSCC scc ctx = do
    let fns = Graph.flattenSCC scc
    annfns <- forM fns $ \ast -> do
        let name = fnName ast
        let extctx = extendContextWithFn ast ctx
        let typechecked = typecheck extctx (E_FnAST ast) Nothing
        putStrLn $ "typechecking " ++ name
        inspect typechecked (E_FnAST ast)
        return typechecked
    return $ if allAnnotated annfns
        then (annfns, foldr extendContextWithFnA ctx [f | (Annotated (E_AnnFn f)) <- annfns])
        else ([TypecheckErrors [ "not all functions type checked correctly in SCC: "
                                ++ show [fnName f | f <- fns]]], ctx)

--foldMap :: [Graph.SCC FnAST] -> Context -> (Graph.SCC FnAST -> Context -> IO ([TypecheckResult AnnExpr], Context)) -> ...
--foldMap :: [[FnAST]] -> Context -> ([FnAST] -> Context -> IO ([TypecheckResult AnnExpr], Context)) -> IO ([TypecheckResult AnnExpr], Context)

mapFoldM :: (Monad m) => [a] -> b -> (a -> b -> m ([c], b)) -> m ([c], b)
mapFoldM []  b  f    = fail "mapFoldM must be given a non-empty list"
mapFoldM [a] b1 f    = f a b1
mapFoldM (a:as) b1 f = do
    (cs1, b2) <- f a b1
    (cs2, b3) <- mapFoldM as b2 f
    return (cs1 ++ cs2, b3)

typecheckModule :: ModuleAST FnAST -> IO (Maybe (ModuleAST AnnFn))
typecheckModule mod = do
    let fns = moduleASTfunctions mod
    let ctx = rootContext
    let sortedFns = buildCallGraph fns ctx -- :: [SCC FnAST]
    putStrLn $ "Function SCC list : " ++ show [(fnName f, fnFreeVariables f ctx) | fns <- sortedFns, f <- Graph.flattenSCC fns]
    (annFns, _ctx) <- mapFoldM sortedFns ctx typecheckFnSCC
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
            putStrLn $ "Successful typecheck!\n" ++ showStructure e
            return True
        TypecheckErrors errs -> do
            putStrLn $ showStructure ast
            forM_ errs $ \err -> do putStrLn $ "Typecheck error: " ++ err
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
        elabModule <- typecheckModule sm
        case elabModule of
            (Just mod) -> dumpModuleToProtobuf mod outfile
            Nothing    -> error $ "Unable to type check input module!"


-----------------------------------------------------------------------

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

runUnitTests = do
    runTestTT tests
