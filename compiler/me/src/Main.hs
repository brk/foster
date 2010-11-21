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

import List(length, zip, all)
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
_typesEqual TypeUnitAST (TupleTypeAST []) = True
_typesEqual (TupleTypeAST as) (TupleTypeAST bs) = Prelude.and [_typesEqual a b | (a, b) <- Prelude.zip as bs]
_typesEqual ta tb = ta == tb

getBindings :: PrototypeAST -> [(String, TypeAST)]
getBindings (PrototypeAST t s vars) =
    map (\v -> (avarName v, avarType v)) vars

type Context = [(String, TypeAST)]

extendContext :: Context -> PrototypeAST -> Context
extendContext ctx proto = (getBindings proto) ++ ctx


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
    deriving (Show)

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
        E_FnAST (FnAST proto body) -> typecheckFn ctx proto body maybeExpTy
        CallAST r b a -> typecheckCall ctx r b a maybeExpTy
        IntAST i s1 s2 i2    -> do return (AnnInt (NamedTypeAST "i32") i s1 s2 i2)
        SeqAST a b -> do
            ea <- typecheck ctx a Nothing --(Just TypeUnitAST)
            eb <- typecheck ctx b maybeExpTy
            return (AnnSeq ea eb)
        SubscriptAST  a b    -> do ta <- typecheck ctx a Nothing
                                   tb <- typecheck ctx b Nothing
                                   throwError $ "SubscriptAST"
        E_PrototypeAST (PrototypeAST t s es) -> throwError "PrototypeAST"
        TupleAST      es b   -> typecheckTuple ctx es b maybeExpTy
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
argType :: TypeAST -> TypeAST
argType (FnTypeAST a r) = a
argType x = error $ "Called argType on non-FnTypeAST: " ++ show x

typecheckCall ctx range base arg maybeExpTy =
   let expectedLambdaType = case maybeExpTy of
        Nothing  -> Nothing
        (Just t) -> (Just (FnTypeAST (MissingTypeAST "typecheckCall") t)) in
        -- If we have (e1 e2) :: T, we infer that e1 :: (? -> T) and e2 :: ?
   do eb <- typecheck ctx base expectedLambdaType
      ea <- typecheck ctx arg (Just $ argType (typeAST eb))
      case (typeAST eb, typeAST ea) of
         (FnTypeAST formaltype restype, argtype) ->
            if isJust $ typeJoin formaltype argtype
                then return $ AnnCall range restype eb ea
                else throwError $ "CallAST mismatches:\n"
                                       ++ show formaltype ++ "\nvs\n" ++ show argtype ++ "\nrange:\n" ++ show range
         otherwise -> throwError $ "CallAST w/o FnAST type: " ++ (showStructureA eb)
                                       ++ " :: " ++ (show $ typeAST eb)
--typecheckCall ctx base arg maybeExpTy = error $ "TODO make use of maybeExpTy (" ++ (show maybeExpTy) ++ ") in typecheckCall"
-----------------------------------------------------------------------
typecheckFn ctx proto body Nothing = typecheckFn' ctx proto body Nothing
typecheckFn ctx proto body (Just (FnTypeAST s t)) =
    if isJust $ typeJoin (prototypeASTretType proto) t
      then typecheckFn' ctx proto body (Just t)
      else throwError  $ "typecheck fn '" ++ prototypeASTname proto
                        ++ "': proto return type, " ++ show (prototypeASTretType proto)
                        ++ ", did not match return type of expected fn type " ++ show (FnTypeAST s t)
typecheckFn' ctx proto body expBodyType =
    let extCtx = extendContext ctx proto in
    do annbody <- typecheck extCtx body expBodyType
       case typeJoin (prototypeASTretType proto) (typeAST annbody) of
        (Just x) ->
           let annproto = case proto of
                            (PrototypeAST t s vars) -> (AnnPrototype x s vars) in
           return (E_AnnFn (AnnFn annproto annbody))
        otherwise ->
             throwError $ "typecheck '" ++ prototypeASTname proto
                        ++ "': proto ret type " ++ show (prototypeASTretType proto)
                        ++ " did not match body type " ++ show (typeAST annbody)
-----------------------------------------------------------------------
typecheckTuple ctx es b Nothing = typecheckTuple' ctx es b [Nothing | e <- es]

typecheckTuple ctx es b (Just (TupleTypeAST ts)) =
    if length es /= length ts
      then throwError $ "typecheck: length of tuple and expected tuple type did not agree: "
                            ++ show es ++ " versus " ++ show ts
      else typecheckTuple' ctx es b [Just t | t <- ts]

typecheckTuple ctx [] b (Just TypeUnitAST) = do return (AnnTuple [] b)

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

rootContext :: Context
rootContext =
    [("llvm_readcyclecounter", FnTypeAST TypeUnitAST (NamedTypeAST "i64"))
    ,("expect_i32", FnTypeAST (NamedTypeAST "i32") (NamedTypeAST "i32"))
    ,( "print_i32", FnTypeAST (NamedTypeAST "i32") (NamedTypeAST "i32"))
    ,(  "read_i32", FnTypeAST TypeUnitAST (NamedTypeAST "i32"))
    ,("expect_i1", FnTypeAST (NamedTypeAST "i1") (NamedTypeAST "i32"))
    ,( "print_i1", FnTypeAST (NamedTypeAST "i1") (NamedTypeAST "i32"))
    ,("primitive_sext_i64_i32", FnTypeAST (NamedTypeAST "i32") (NamedTypeAST "i64"))

    ,("primitive_<_i64", FnTypeAST (TupleTypeAST [(NamedTypeAST "i64"), (NamedTypeAST "i64")]) (NamedTypeAST "i1"))
    ,("primitive_-_i64", FnTypeAST (TupleTypeAST [(NamedTypeAST "i64"), (NamedTypeAST "i64")]) (NamedTypeAST "i64"))
    ,("primitive_-_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32"))
    ,("primitive_+_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i32"))
    ,("primitive_<_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i1"))
    ,("primitive_==_i32", FnTypeAST (TupleTypeAST [(NamedTypeAST "i32"), (NamedTypeAST "i32")]) (NamedTypeAST "i1"))
    ]

fnName :: FnAST -> String
fnName (FnAST proto body) = prototypeASTname proto

fnCalledNames :: FnAST -> Context -> [String]
fnCalledNames (FnAST proto body) ctx =
    let allCalledFns = Set.fromList $ calledNames body in
    let nonPrimitives = Set.filter (\f -> not (isJust $ lookup f ctx)) allCalledFns in
    Set.toList $ Set.filter (\f -> prototypeASTname proto /= f) nonPrimitives

buildCallGraph :: [FnAST] -> Context -> [Graph.SCC FnAST]
buildCallGraph asts ctx =
    let nodeList = (map (\ast -> (ast, fnName ast, fnCalledNames ast ctx)) asts) in
    Graph.stronglyConnComp nodeList

extendContextWithFnA :: AnnFn -> Context -> Context
extendContextWithFnA (AnnFn proto body) ctx = (annProtoName proto, fnTypeFromA proto body):ctx

fnTypeFrom :: PrototypeAST -> TypeAST
fnTypeFrom p =
    let intype = normalizeTypes [avarType v | v <- prototypeASTformals p] in
    let outtype = prototypeASTretType p in
    FnTypeAST intype outtype

extendContextWithFn :: FnAST -> Context -> Context
extendContextWithFn f@(FnAST proto body) ctx = (fnName f, fnTypeFrom proto):ctx

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
        E_AnnFn (AnnFn a b)  -> "AnnFn        "
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
