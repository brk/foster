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


getBindings :: PrototypeAST -> Maybe TypeAST -> [(String, TypeAST)]
getBindings (PrototypeAST t s vars) maybeExpTy =
    let bindings = map (\v -> (avarName v, avarType v)) (typeJoinVars vars maybeExpTy) in
    trace ("getBindings: " ++ show bindings) $
      bindings



type Context = [(String, TypeAST)]

extendContext :: Context -> PrototypeAST -> Maybe TypeAST -> Context
extendContext ctx proto expFormals = (getBindings proto expFormals) ++ ctx

--
--extendContextA :: Context -> AnnPrototype -> Context
--extendContextA ctx proto = (getBindingsA proto) ++ ctx
--
--getBindingsA :: AnnPrototype -> [(String, TypeAST)]
--getBindingsA (AnnPrototype t s vars) =
--    map (\v -> (avarName v, avarType v)) vars
--
--extendContextWithFn :: AnnFn -> Context -> Context
--extendContextWithFn (AnnFn proto body) ctx = extendContextA ctx proto

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

getTypeCheckedType :: TypecheckResult AnnExpr -> TypeAST
getTypeCheckedType (Annotated e) = typeAST e
getTypeCheckedType (TypecheckErrors _) = MissingTypeAST "getTypeCheckedType"

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
        BoolAST b    -> do return (AnnBool b)
        IfAST a b c  -> do ea <- typecheck ctx a (Just fosBoolType)
                           eb <- typecheck ctx b maybeExpTy
                           ec <- typecheck ctx c maybeExpTy
                           _  <- sanityCheck (isJust $ typeJoin (typeAST ea) fosBoolType)
                                             "IfAST: type of conditional wasn't boolean"
                           _  <- sanityCheck (isJust $ typeJoin (typeAST eb) (typeAST ec))
                                             "IfAST: types of branches didn't match"
                           return (AnnIf (typeAST eb) ea eb ec)
        E_FnAST (FnAST proto body cs) -> typecheckFn ctx proto body cs maybeExpTy
        CallAST r b a -> typecheckCall ctx r b a maybeExpTy
        IntAST i s1 s2 i2    -> do return (AnnInt (NamedTypeAST "i32") i s1 s2 i2)
        SeqAST a b -> do
            ea <- typecheck ctx a Nothing --(Just TypeUnitAST)
            eb <- typecheck ctx b maybeExpTy
            return (AnnSeq ea eb)
        SubscriptAST  a b    -> do ta <- typecheck ctx a Nothing
                                   tb <- typecheck ctx b Nothing
                                   typecheckSubscript ta (typeAST ta) tb maybeExpTy
        E_PrototypeAST (PrototypeAST t s es) -> throwError "PrototypeAST"
        TupleAST  exprs b   -> typecheckTuple ctx exprs b maybeExpTy
        VarAST mt s -> case lookup s ctx of
            Just t  -> Annotated $ E_AnnVar (AnnVar t s)
            Nothing -> throwError $ "Unknown variable " ++ s
        CompilesAST e c -> case c of
            CS_NotChecked ->
              return $ AnnCompiles $ case typecheck ctx e Nothing of
                Annotated ae -> CS_WouldCompile
                otherwise    -> CS_WouldNotCompile
            otherwise -> return $ AnnCompiles c
-----------------------------------------------------------------------
safeListIndex :: [a] -> Int -> Maybe a
safeListIndex lst idx =
    if List.length lst <= idx
        then Nothing
        else Just $ lst !! idx

typecheckSubscript base (TupleTypeAST types) i@(AnnInt _ _ _ _ _) maybeExpTy =
    let literalValue = read (aintText i) :: Integer in
    case safeListIndex types (fromInteger literalValue) of
        Nothing -> throwError $ "Literal index " ++ aintText i ++ " to subscript was out of bounds"
        Just t  -> return (AnnSubscript t base i)

typecheckSubscript base baseType index maybeExpTy =
       throwError $ "SubscriptAST " ++ show baseType ++ "[" ++ show index ++ "]" ++ " (:: " ++ show maybeExpTy ++ ")"

argType :: TypeAST -> TypeAST
argType (FnTypeAST a r cs) = a
argType x = error $ "Called argType on non-FnTypeAST: " ++ show x

irrelevantClosedOverVars = Nothing

typecheckCall' ea eb range base arg =
    case (typeAST eb, typeAST ea) of
         (FnTypeAST formaltype restype cs, argtype) ->
            if isJust $ typeJoin formaltype argtype
                then Annotated (AnnCall range restype eb ea)
                else throwError $ "CallAST mismatches:\n"
                                       ++ "base: " ++ (showStructureA eb) ++ "\n"
                                       ++ "arg : " ++ (showStructureA ea) ++ "\n"
                                       ++ show formaltype ++ "\nvs\n" ++ show argtype ++ "\nrange:\n" ++ show range
         otherwise -> throwError $ "CallAST w/o FnAST type: " ++ (showStructureA eb)
                                       ++ " :: " ++ (show $ typeAST eb)

typecheckCall ctx range base arg maybeExpTy =
      -- If we have an explicit redex (call to a literal function),
      -- we can determine the types of the formals based on the actuals.
      case base of
        (E_FnAST (FnAST p b mv)) -> do
           ea <- typecheck ctx arg Nothing
           let expectedLambdaType = case maybeExpTy of
                Nothing  -> (Just (FnTypeAST (typeAST ea) (MissingTypeAST "typecheckCall-3")  irrelevantClosedOverVars))
                (Just t) -> (Just (FnTypeAST (MissingTypeAST "typecheckCall-2") t irrelevantClosedOverVars))

           eb <- typecheck ctx base expectedLambdaType
           trace ("typecheckCall with literal fn base, exp ty " ++ (show expectedLambdaType)) $
            typecheckCall' ea eb range base arg

        -- Otherwise, typecheck the function first, then the args.
        _ -> do
           let expectedLambdaType = case maybeExpTy of
                Nothing  -> Nothing
                (Just t) -> (Just (FnTypeAST (MissingTypeAST "typecheckCall-1") t irrelevantClosedOverVars))
                -- If we have (e1 e2) :: T, we infer that e1 :: (? -> T) and e2 :: ?
           eb <- typecheck ctx base expectedLambdaType
           ea <- typecheck ctx arg (Just $ argType (typeAST eb))
           typecheckCall' ea eb range base arg

--typecheckCall ctx base arg maybeExpTy = error $ "TODO make use of maybeExpTy (" ++ (show maybeExpTy) ++ ") in typecheckCall"
-----------------------------------------------------------------------

typecheckFn ctx proto body cs Nothing = typecheckFn' ctx proto body cs Nothing Nothing
typecheckFn ctx proto body cs (Just (FnTypeAST s t cs')) =
    if isJust $ typeJoin (prototypeASTretType proto) t
      then typecheckFn' ctx proto body cs (Just s) (Just t)
      else throwError  $ "typecheck fn '" ++ prototypeASTname proto
                        ++ "': proto return type, " ++ show (prototypeASTretType proto)
                        ++ ", did not match return type of expected fn type " ++ show (FnTypeAST s t cs')

typecheckFn' ctx proto body cs expArgType expBodyType = do
    _ <- verifyNonOverlappingVariableNames proto
    let extCtx = extendContext ctx proto expArgType
    annbody <- typecheck extCtx body expBodyType
    case typeJoin (prototypeASTretType proto) (typeAST annbody) of
        (Just x) ->
            let annproto = case proto of
                            (PrototypeAST t s vars) ->
                              (AnnPrototype x s (typeJoinVars vars expArgType)) in
            return (E_AnnFn (AnnFn annproto annbody cs))
        otherwise ->
         throwError $ "typecheck '" ++ prototypeASTname proto
                    ++ "': proto ret type " ++ show (prototypeASTretType proto)
                    ++ " did not match body type " ++ show (typeAST annbody)

verifyNonOverlappingVariableNames :: PrototypeAST -> TypecheckResult AnnExpr
verifyNonOverlappingVariableNames proto = do
    let varNames = [avarName v | v <- prototypeASTformals proto]
    let duplicates = [List.head dups | dups <- List.group (List.sort varNames), List.length dups > 1]
    case duplicates of
        []        -> return (AnnBool True)
        otherwise -> throwError $ "Error when checking " ++ prototypeASTname proto
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

i32 = (NamedTypeAST "i32")
i64 = (NamedTypeAST "i64")
fosi64toi32 = FnTypeAST (TupleTypeAST [i64]) i32 Nothing
fosi32toi32 = FnTypeAST (TupleTypeAST [i32]) i32 Nothing
fosi64toi64 = FnTypeAST (TupleTypeAST [i64]) i64 Nothing
fosi1toi32  = FnTypeAST (TupleTypeAST [(NamedTypeAST "i1")]) i32 Nothing
fosi64i64toi1 = FnTypeAST (TupleTypeAST [i64, i64]) (NamedTypeAST "i1") Nothing
fosi32i32toi1 = FnTypeAST (TupleTypeAST [i32, i32]) (NamedTypeAST "i1") Nothing

coroInvokeType args ret =
    (FnTypeAST   (TupleTypeAST ([(CoroType (minimalTuple args)   ret)] ++ args)
                 )                                               ret Nothing)

coroYieldType args ret = (FnTypeAST (TupleTypeAST [ret])
                                    (minimalTuple args) Nothing)

coroCreateType args ret =
    (FnTypeAST (TupleTypeAST [(FnTypeAST (TupleTypeAST args) ret  Nothing)])
                               (CoroType (minimalTuple args) ret) Nothing)

rootContext :: Context
rootContext =
    [("llvm_readcyclecounter", FnTypeAST (TupleTypeAST []) (NamedTypeAST "i64") Nothing)
    ,("expect_i32", fosi32toi32)
    ,( "print_i32", fosi32toi32)
    ,("expect_i32b", fosi32toi32)
    ,( "print_i32b", fosi32toi32)
    ,("expect_i64b", fosi64toi32)
    ,( "print_i64b", fosi64toi32)
    ,(  "read_i32", FnTypeAST (TupleTypeAST []) (NamedTypeAST "i32") Nothing)
    ,("expect_i1", fosi1toi32)
    ,( "print_i1", fosi1toi32)

    ,("coro_create_i32_i32", coroCreateType [i32] i32)
    ,("coro_invoke_i32_i32", coroInvokeType [i32] i32)
    ,("coro_yield_i32_i32",  coroYieldType  [i32] i32)


    ,("coro_create_i32x2_i32", coroCreateType [i32, i32] i32)
    ,("coro_invoke_i32x2_i32", coroInvokeType [i32, i32] i32)
    ,("coro_yield_i32x2_i32",  coroYieldType  [i32, i32] i32)
    ,("primitive_sext_i64_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32")]) (NamedTypeAST "i64") Nothing)
    ,("primitive_negate_i32", fosi32toi32)
    ,("primitive_bitnot_i1", FnTypeAST (TupleTypeAST [(NamedTypeAST "i1")]) (NamedTypeAST "i1") Nothing)
    ,("primitive_bitshl_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_bitashr_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_bitlshr_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_bitor_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_bitand_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_bitxor_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing )
    ,("force_gc_for_debugging_purposes", FnTypeAST (TupleTypeAST []) (TupleTypeAST []) Nothing)

    ,("primitive_<_i64", FnTypeAST (TupleTypeAST [(NamedTypeAST "i64"), (NamedTypeAST "i64")]) (NamedTypeAST "i1")  Nothing)
    ,("primitive_-_i64", FnTypeAST (TupleTypeAST [(NamedTypeAST "i64"), (NamedTypeAST "i64")]) (NamedTypeAST "i64") Nothing)
    ,("primitive_-_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_*_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_+_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32") Nothing)
    ,("primitive_<_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i1")  Nothing)
    ,("primitive_<=_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i1") Nothing )
    ,("primitive_==_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i1") Nothing )
    ]

isPrimitiveName name = isJust $ lookup name rootContext

fnName :: FnAST -> String
fnName (FnAST proto body cs) = prototypeASTname proto

fnFreeVariables :: FnAST -> Context -> [String]
fnFreeVariables (FnAST proto body cs) ctx =
    let allCalledFns = Set.fromList $ freeVariables body in
    -- remove names of primitive functions
    let nonPrimitives = Set.filter (\f -> not (isJust $ lookup f ctx)) allCalledFns in
    -- remove recursive function name calls
    Set.toList $ Set.filter (\f -> prototypeASTname proto /= f) nonPrimitives

buildCallGraph :: [FnAST] -> Context -> [Graph.SCC FnAST]
buildCallGraph asts ctx =
    let nodeList = (map (\ast -> (ast, fnName ast, fnFreeVariables ast ctx)) asts) in
    Graph.stronglyConnComp nodeList

extendContextWithFnA :: AnnFn -> Context -> Context
extendContextWithFnA f@(AnnFn proto body cs) ctx = (annProtoName proto, fnTypeFromA f):ctx

fnTypeFrom :: FnAST -> TypeAST
fnTypeFrom (FnAST p b cs) =
    let intype = TupleTypeAST [avarType v | v <- prototypeASTformals p] in
    let outtype = prototypeASTretType p in
    FnTypeAST intype outtype (fmap (map avarName) cs)

extendContextWithFn :: FnAST -> Context -> Context
extendContextWithFn f ctx = (fnName f, fnTypeFrom f):ctx

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
            putStrLn $ "Successful typecheck!\n" ++ showStructureA e
            return True
        TypecheckErrors errs -> do
            forM_ errs $ \err -> do putStrLn $ "Typecheck error: " ++ err
            putStrLn $ showStructure ast
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

-- Formats a single-line tag for the given ExprAST node.
-- Example:  textOf (VarAST "x")      ===     "VarAST x"
textOfA :: AnnExpr -> Int -> String
textOfA e width =
    let spaces = Prelude.replicate width '\SP'  in
    case e of
        AnnBool         b    -> "AnnBool      " ++ (show b)
        AnnCall  r t b a     -> "AnnCall      " ++ " :: " ++ show t
        AnnCompiles     c    -> "AnnCompiles  "
        AnnIf      t  a b c  -> "AnnIf        " ++ " :: " ++ show t
        AnnInt ty i t c base -> "AnnInt       " ++ t ++ " :: " ++ show ty
        E_AnnFn (AnnFn a b cs)  -> "AnnFn        "
        AnnSeq          a b  -> "AnnSeq       " ++ " :: " ++ show (typeAST b)
        AnnSubscript  t a b  -> "AnnSubscript " ++ " :: " ++ show t
        E_AnnPrototype t (AnnPrototype rt s es) -> "PrototypeAST " ++ s ++ " :: " ++ show t
        AnnTuple     es b    -> "AnnTuple     "
        E_AnnVar (AnnVar t v) -> "AnnVar       " ++ v ++ " :: " ++ show t

-----------------------------------------------------------------------

showStructureA :: AnnExpr -> String
showStructureA e = showStructureP e "" False where
    showStructureP e prefix isLast =
        let children = childrenOfA e in
        let thisIndent = prefix ++ if isLast then "└─" else "├─" in
        let nextIndent = prefix ++ if isLast then "  " else "│ " in
        let padding = max 6 (60 - Prelude.length thisIndent) in
        -- [ (child, index, numchildren) ]
        let childpairs = Prelude.zip3 children [1..]
                               (Prelude.repeat (Prelude.length children)) in
        let childlines = map (\(c, n, l) ->
                                showStructureP c nextIndent (n == l))
                             childpairs in
        thisIndent ++ (textOfA e padding ++ "\n") ++ Prelude.foldl (++) "" childlines

-----------------------------------------------------------------------

trMaybe :: TypecheckResult AnnExpr -> Maybe AnnExpr
trMaybe (TypecheckErrors _) = Nothing
trMaybe (Annotated ae) = Just $ ae

test1 = let term = (BoolAST True) in
        let expectedType = Nothing in
        let anticipated = (AnnBool True) in
        TestCase (do let taa = trMaybe $ typecheck rootContext term expectedType
                     assertEqual ("for " ++ show term ++ ", ")
                             (fmap showStructureA (Just anticipated))
                             (fmap showStructureA taa))

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
