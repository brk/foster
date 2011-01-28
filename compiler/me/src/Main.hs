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
import Foster.Typecheck
import Foster.Context

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
