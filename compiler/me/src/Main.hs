-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Main (
main
) where

import System.Environment(getArgs,getProgName)
import System.Console.GetOpt
import System.Console.ANSI

import qualified Data.ByteString.Lazy as L(readFile)

import List(all)
import qualified Data.Set as Set
import qualified Data.Graph as Graph
import Data.Maybe(isJust)
import Data.Foldable(forM_)
import Control.Monad.State
import Data.IORef(newIORef, readIORef)

import Text.ProtocolBuffers(messageGet)

import Foster.Base
import Foster.ProtobufFE
import Foster.ProtobufIL
import Foster.ExprAST
import Foster.TypeAST
import Foster.AnnExpr
import Foster.AnnExprIL
import Foster.TypeIL
import Foster.ILExpr
import Foster.Typecheck
import Foster.Context
import Foster.Smallstep

-----------------------------------------------------------------------
class FnLike f where
    fnName :: f -> String
    fnFreeVariables :: f -> [ContextBinding ty] -> [String]

instance FnLike FnAST where
    fnName f = fnAstName f
    fnFreeVariables f bindings =
        let allCalledFns = Set.fromList $ freeVars (fnBody f) in
        -- remove names of primitive functions
        let nonPrimitives = Set.filter (\var -> not (isJust $ termVarLookup var bindings)) allCalledFns in
        -- remove recursive function name calls
        Set.toList $ Set.filter (\name -> fnName f /= name) nonPrimitives

instance Expr AnnExpr where
    freeVars e = map identPrefix (freeIdents e)

instance FnLike AnnFn where
    fnName = fnNameA
    fnFreeVariables f bindings =
        let allCalledFns = Set.fromList $ freeVars (annFnBody f) in
        -- remove names of primitive functions
        let nonPrimitives = Set.filter (\var -> not (isJust $ termVarLookup var bindings)) allCalledFns in
        -- remove recursive function name calls
        Set.toList $ Set.filter (\name -> fnName f /= name) nonPrimitives

fnNames f = [fnName f]

pair2binding (nm, ty) = TermVarBinding nm (TypedId ty (GlobalSymbol nm))

computeContextBindings :: [(String, TypeAST)] -> [ContextBinding TypeAST]
computeContextBindings decls = map pair2binding decls

buildCallGraph :: FnLike f => [f] -> [ContextBinding ty] -> [Graph.SCC f]
buildCallGraph asts bindings = Graph.stronglyConnComp nodeList where
  nodeList = map (\ast -> (ast, fnName ast,
                           fnFreeVariables ast bindings)) asts

bindingForAnnFn :: AnnFn -> ContextBinding TypeAST
bindingForAnnFn f = TermVarBinding (fnNameA f) (annFnVar f)
 where annFnVar f = TypedId (annFnType f) (annFnIdent f)

bindingForFnAST :: FnAST -> TypeAST -> ContextBinding TypeAST
bindingForFnAST f t = let n = fnName f in pair2binding (n, t)

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Graph.SCC FnAST
               -> (Context TypeAST, TcEnv)
               -> IO ([OutputOr AnnExpr], (Context TypeAST, TcEnv))
typecheckFnSCC scc (ctx, tcenv) = do
    let fns = Graph.flattenSCC scc
    annfns <- forM fns $ \fn -> do
        let ast = (E_FnAST fn)
        let name = fnName fn
        putStrLn $ "typechecking " ++ name
        annfn <- unTc tcenv $
                    do uRetTy <- newTcUnificationVar $ "toplevel fn type for " ++ name
                       let extctx = prependContextBinding ctx (bindingForFnAST fn (MetaTyVar uRetTy))
                       typecheck extctx ast Nothing
        -- We can't convert AnnExpr to AIExpr here because
        -- the output context is threaded through further type checking.
        inspect ctx annfn ast
        return annfn
    if allOK annfns
     then let fns = [f | (OK (E_AnnFn f)) <- annfns] in
          let newbindings = foldr (\f b -> (bindingForAnnFn f):b) [] fns in
          return (annfns, (prependContextBindings ctx newbindings, tcenv))
     else return ([Errors [out $ "not all functions type checked correctly in SCC: "
                             ++ show [fnName f | f <- fns]]
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

typecheckModule :: Bool -> ModuleAST FnAST TypeAST -> TcEnv
                        -> IO (OutputOr (Context TypeIL, ModuleAST AIFn TypeIL))
typecheckModule verboseMode mod tcenv0 = do
    let fns = moduleASTfunctions mod
    let primBindings = computeContextBindings primitiveDecls
    let declBindings = computeContextBindings (moduleASTdecls mod)
    let sortedFns = buildCallGraph fns declBindings -- :: [SCC FnAST]
    putStrLn $ "Function SCC list : " ++ show [(fnName f, fnFreeVariables f declBindings) | fns <- sortedFns, f <- Graph.flattenSCC fns]
    let ctx0 = Context declBindings primBindings verboseMode
    (annFns, (ctx, tcenv)) <- mapFoldM sortedFns (ctx0, tcenv0) typecheckFnSCC
    unTc tcenv (convertTypeILofAST mod ctx annFns)

convertTypeILofAST :: ModuleAST FnAST TypeAST
                   -> Context TypeAST
                   -> [OutputOr AnnExpr]
                   -> Tc (Context TypeIL, ModuleAST AIFn TypeIL)
convertTypeILofAST mod ctx_ast oo_annfns = do
  decls <- mapM convertDecl (moduleASTdecls mod)
  ctx_il <- liftContextM ilOf ctx_ast
  let knownProcNames = Set.fromList $ concatMap fnNames (moduleASTfunctions mod)
  aiFns <- mapM (\ae -> tcInject ae (ail knownProcNames)) oo_annfns
  let m = ModuleAST [f | (E_AIFn f) <- aiFns]
                    decls (moduleASTsourceLines mod)
  return (ctx_il, m)

convertDecl :: (String, TypeAST) -> Tc (String, TypeIL)
convertDecl (s, ty) = do
  t <- ilOf ty
  return (s, t)

liftBinding :: Monad m => (t1 -> m t2) -> ContextBinding t1 -> m (ContextBinding t2)
liftBinding f (TermVarBinding s (TypedId t i)) = do
  t2 <- f t
  return $ TermVarBinding s (TypedId t2 i)

liftContextM :: Monad m => (t1 -> m t2) -> Context t1 -> m (Context t2)
liftContextM f (Context cb pb vb) = do
  cb' <- mapM (liftBinding f) cb
  pb' <- mapM (liftBinding f) pb
  return $ Context cb' pb' vb

liftOutput :: (a -> OutputOr b) -> OutputOr a -> OutputOr b
liftOutput f ooa =
  case ooa of
    OK a     -> f a
    Errors o -> Errors o

allOK :: [OutputOr ty] -> Bool
allOK results = List.all isOK results

printOutputs :: [Output] -> IO ()
printOutputs outs =
  Data.Foldable.forM_ outs $ \(output) ->
    do
       runOutput $ output
       runOutput $ (outLn "")

inspect :: Context TypeAST -> OutputOr AnnExpr -> ExprAST -> IO Bool
inspect ctx typechecked ast =
    case typechecked of
        OK e -> do
            when (contextVerbose ctx) (do
                runOutput $ showStructure ast
                putStrLn $ "Successful typecheck!"
                runOutput $ showStructure e)
            return True
        Errors errs -> do
            runOutput $ showStructure ast
            runOutput $ (outCSLn Red "Typecheck error: ")
            printOutputs errs

            do runOutput $ (outLn "")
            return False

-----------------------------------------------------------------------

data Flag = Interpret String | Verbose

options :: [OptDescr Flag]
options =
 [ Option []     ["interpret"]  (ReqArg Interpret "DIR")  "interpret in DIR"
 , Option []     ["verbose"]    (NoArg  Verbose)          "verbose mode"
 ]

parseOpts :: [String] -> IO ([Flag], [String])
parseOpts argv =
  case getOpt Permute options argv of
    (o,n,[]  ) -> return (o,n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
  where header = "Usage: me [OPTION...] files..."

getInterpretFlag ([], _) = Nothing
getInterpretFlag ((f:fs), bs) =
        case f of
                Interpret d -> Just d
                otherwise   -> getInterpretFlag (fs, bs)

getVerboseFlag ([], _) = False
getVerboseFlag ((f:fs), bs) =
        case f of
                Verbose -> True
                otherwise   -> getVerboseFlag (fs, bs)

main :: IO ()
main = do
  args <- getArgs
  (f, outfile, flagVals) <- case args of
         (infile : outfile : rest) -> do
                protobuf <- L.readFile infile
                flagVals <- parseOpts rest
                return (protobuf, outfile, flagVals)
         _ -> do
                self <- getProgName
                return (error $ "Usage: " ++ self ++ " path/to/infile.pb path/to/outfile.pb")

  case messageGet f of
    Left msg -> error ("Failed to parse protocol buffer.\n"++msg)
    Right (pb_module, _) -> do
        let sm = parseSourceModule pb_module
        uniqref <- newIORef 1
        varlist <- newIORef []
        let tcenv = TcEnv { tcEnvUniqs = uniqref,
                     tcUnificationVars = varlist,
                             tcParents = [] }
        let verboseMode = getVerboseFlag flagVals
        modResults  <- typecheckModule verboseMode sm tcenv
        case modResults of
            (OK (ctx_il, mod)) -> do
                         when verboseMode (do
                           metaTyVars <- readIORef varlist
                           runOutput $ (outLn $ "generated " ++ (show $ length metaTyVars) ++ " meta type variables:")
                           forM metaTyVars (\mtv@(Meta _ r _) -> do
                               t <- readIORef r
                               runOutput (outLn $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t))

                           runOutput $ (outLn "vvvv contextBindings:====================")
                           runOutput $ (outCSLn Yellow (joinWith "\n" $ map show (contextBindings ctx_il))))
                         let prog = closureConvertAndLift ctx_il mod
                         dumpModuleToProtobufIL prog (outfile ++ ".ll.pb")
                         when verboseMode (do
                             runOutput $ (outLn "/// ===================================")
                             runOutput $ showProgramStructure prog
                             runOutput $ (outLn "^^^ ==================================="))
                         (case getInterpretFlag flagVals of
                           Nothing -> return ()
                           Just tmpDir -> do
                              _unused <- interpretProg prog tmpDir
                              return ())
            Errors os -> do runOutput (outCSLn Red $ "Unable to type check input module:")
                            printOutputs os
                            error "compilation failed"

