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
import Foster.ProtobufFE
import Foster.ProtobufIL
import Foster.ExprAST
import Foster.TypeAST
import Foster.ILExpr
import Foster.Typecheck
import Foster.Context

-----------------------------------------------------------------------
class FnLike f where
    fnName :: f -> String
    fnFreeVariables :: f -> [ContextBinding] -> [String]

instance FnLike FnAST where
    fnName f = prototypeASTname (fnProto f)
    fnFreeVariables f bindings =
        let allCalledFns = Set.fromList $ freeVars (fnBody f) in
        -- remove names of primitive functions
        let nonPrimitives = Set.filter (\var -> not (isJust $ termVarLookup var bindings)) allCalledFns in
        -- remove recursive function name calls
        Set.toList $ Set.filter (\name -> fnName f /= name) nonPrimitives

instance FnLike AnnFn where
    fnName = fnNameA
    fnFreeVariables f bindings =
        let allCalledFns = Set.fromList $ freeVars (annFnBody f) in
        -- remove names of primitive functions
        let nonPrimitives = Set.filter (\var -> not (isJust $ termVarLookup var bindings)) allCalledFns in
        -- remove recursive function name calls
        Set.toList $ Set.filter (\name -> fnName f /= name) nonPrimitives

computeRootContextBindings :: Uniq -> ([ContextBinding], Uniq)
computeRootContextBindings u =
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

buildCallGraph :: FnLike f => [f] -> [ContextBinding] -> [Graph.SCC f]
buildCallGraph asts bindings =
    let nodeList = (map (\ast -> (ast, fnName ast, fnFreeVariables ast bindings)) asts) in
    Graph.stronglyConnComp nodeList

annFnVar f = AnnVar (annFnType f) (annProtoIdent $ annFnProto f)

fnTypeFrom :: FnAST -> TypeAST
fnTypeFrom f =
    let intype = TupleTypeAST [avarType v | v <- prototypeASTformals (fnProto f)] in
    let outtype = prototypeASTretType (fnProto f) in
    FnTypeAST intype outtype (fnTypeCloses' f)


bindingForAnnFn :: AnnFn -> ContextBinding
bindingForAnnFn f = TermVarBinding (fnNameA f) (annFnVar f)

bindingForFnAST :: FnAST -> ContextBinding
bindingForFnAST f = TermVarBinding (fnName f) (fnVar f)

fnVar f = AnnVar (fnTypeFrom f) (Ident (fnName f) (-12345))

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Graph.SCC FnAST -> (Context, TcEnv) -> IO ([OutputOr AnnExpr], (Context, TcEnv))
typecheckFnSCC scc (ctx, tcenv) = do
    let fns = Graph.flattenSCC scc
    annfns <- forM fns $ \fn -> do
        let ast = (E_FnAST fn)
        let name = fnName fn
        putStrLn $ "typechecking " ++ name
        runOutput $ showStructure ast
        let extctx = prependContextBinding ctx (bindingForFnAST fn)
        typechecked <- unTc (typecheck extctx ast Nothing) tcenv
        inspect extctx typechecked ast
        return typechecked
    return $ if allOK annfns
        then let fns = [f | (OK (E_AnnFn f)) <- annfns] in
             let newbindings = foldr (\f b -> (bindingForAnnFn f):b) [] fns in
             (annfns, (prependContextBindings ctx newbindings, tcenv))
        else ([Errors (out $ "not all functions type checked correctly in SCC: "
                                ++ show [fnName f | f <- fns])
              ],(ctx, tcenv))

mapFoldM :: (Monad m) => [a] -> b ->
                         (a -> b -> m ([c], b))
                                 -> m ([c], b)
mapFoldM []  b  f    = fail "mapFoldM must be given a non-empty list"
mapFoldM [a] b1 f    = f a b1
mapFoldM (a:as) b1 f = do
    (cs1, b2) <- f a b1
    (cs2, b3) <- mapFoldM as b2 f
    return (cs1 ++ cs2, b3)

typecheckModule :: ModuleAST FnAST -> TcEnv -> IO (Maybe (Context, ModuleAST AnnFn))
typecheckModule mod tcenv = do
    let fns = moduleASTfunctions mod
    let (bindings, u) = computeRootContextBindings 1
    let sortedFns = buildCallGraph fns bindings -- :: [SCC FnAST]
    putStrLn $ "Function SCC list : " ++ show [(fnName f, fnFreeVariables f bindings) | fns <- sortedFns, f <- Graph.flattenSCC fns]
    let ctx = Context bindings
    (annFns, (extctx, tcenv')) <- mapFoldM sortedFns (ctx, tcenv) typecheckFnSCC
    -- annFns :: [OutputOr AnnExpr]
    if allOK annFns
        then return $ Just (extctx,
                            ModuleAST [f | (OK (E_AnnFn f)) <- annFns]
                                      (moduleASTsourceLines mod))
        else return $ Nothing

allOK :: [OutputOr AnnExpr] -> Bool
allOK results = List.all isOK results

inspect :: Context -> OutputOr AnnExpr -> ExprAST -> IO Bool
inspect ctx typechecked ast =
    case typechecked of
        OK e -> do
            putStrLn $ "Successful typecheck!"
            runOutput $ showStructure e
            return True
        Errors errs -> do
            runOutput $ showStructure ast
            runOutput $ (outCSLn Red "Typecheck error: ")
            forM_ errs $ \(output) ->
                do {-runOutput $ (outLn $ "hist len: " ++ (show $ Prelude.length hist))
                   forM_ (Prelude.reverse hist) $ \expr ->
                        do runOutput $ textOf expr 60
                           runOutput $ outLn ""
                    -}
                   runOutput $ [output]

            do runOutput $ (outLn "")
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
        uniqref <- newIORef 1
        let tcenv = TcEnv { tcEnvUniqs = uniqref, tcParents = [] }
        modResults  <- typecheckModule sm tcenv
        case modResults of
            (Just (extctx, mod)) ->
                      do runOutput $ (outLn "vvvv ===================================")
                         runOutput $ (outCSLn Yellow (joinWith "\n" $ map show (contextBindings extctx)))
                         let prog = closureConvertAndLift extctx mod
                         let fns = moduleASTfunctions mod
                         let (ILProgram procs) = prog
                         dumpModuleToProtobufIL prog (outfile ++ ".ll.pb")
                         runOutput $ (outLn "/// ===================================")
                         runOutput $ showProgramStructure prog
                         runOutput $ (outLn "^^^ ===================================")
            Nothing    -> error $ "Unable to type check input module!"

