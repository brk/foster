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
import Data.Maybe(isNothing)
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
import Foster.KNExpr
import Foster.Typecheck
import Foster.Context
import Foster.Smallstep

-----------------------------------------------------------------------

pair2binding (nm, ty) = TermVarBinding nm (TypedId ty (GlobalSymbol nm))

-----------------------------------------------------------------------

fnAstFreeVariables f bindings =
   let allCalledFns = Set.fromList $ freeVars (fnAstBody f) in
   -- remove names of primitive functions
   let nonPrimitives = Set.filter (\var -> isNothing $ termVarLookup var bindings) allCalledFns in
   -- remove recursive function name calls
   Set.toList $ Set.filter (\name -> fnAstName f /= name) nonPrimitives

buildCallGraph :: [FnAST] -> [ContextBinding ty] -> [Graph.SCC FnAST]
buildCallGraph asts bindings = Graph.stronglyConnComp nodeList where
  nodeList = map (\ast -> (ast, fnAstName ast,
                           fnAstFreeVariables ast bindings)) asts

-----------------------------------------------------------------------

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
        let name = fnAstName fn
        putStrLn $ "typechecking " ++ name
        annfn <- unTc tcenv $
                    do uRetTy <- newTcUnificationVar $ "toplevel fn type for " ++ name
                       let extctx = prependContextBinding ctx (bindingForFnAST fn (MetaTyVar uRetTy))
                       typecheck extctx ast Nothing
        -- We can't convert AnnExpr to AIExpr here because
        -- the output context is threaded through further type checking.
        inspect ctx annfn ast
        return annfn
    if List.all isOK annfns
     then let fns = [f | (OK (E_AnnFn f)) <- annfns] in
          let newbindings = foldr (\f b -> (bindingForAnnFn f):b) [] fns in
          return (annfns, (prependContextBindings ctx newbindings, tcenv))
     else return ([Errors [out $ "not all functions type checked correctly in SCC: "
                             ++ show [fnAstName f | f <- fns]]
           ],(ctx, tcenv))

   where
        bindingForAnnFn :: AnnFn -> ContextBinding TypeAST
        bindingForAnnFn f = TermVarBinding (fnNameA f) (annFnVar f)
         where annFnVar f = TypedId (annFnType f) (annFnIdent f)

        bindingForFnAST :: FnAST -> TypeAST -> ContextBinding TypeAST
        bindingForFnAST f t = pair2binding (fnAstName f, t)

-- | Typechecking a module proceeds as follows:
-- |  #. Build separate binding lists for the globally-defined primitiveDecls
-- |     and the module's top-level (function) declarations.
-- |  #. Build a (conservative) dependency graph on the module's top-level
-- |     declarations, yielding a list of SCCs of declarations.
-- |  #. Typecheck the SCCs bottom-up, propagating results as we go along.
-- |  #. Make sure that all unification variables have been properly eliminated,
-- |     or else we consider type checking to have failed
-- |     (no implicit instantiation at the moment!)
typecheckModule :: Bool -> ModuleAST FnAST TypeAST -> TcEnv
                        -> IO (OutputOr (Context TypeIL, ModuleAST (Fn AIExpr) TypeIL))
typecheckModule verboseMode mod tcenv0 = do
    let fns = moduleASTfunctions mod
    let primBindings = computeContextBindings primitiveDecls
    let declBindings = computeContextBindings (moduleASTdecls mod)
    let sortedFns = buildCallGraph fns declBindings -- :: [SCC FnAST]
    putStrLn $ "Function SCC list : " ++
                        show [(fnAstName f, fnAstFreeVariables f declBindings)
                             | fns <- sortedFns, f <- Graph.flattenSCC fns]
    let ctx0 = Context declBindings primBindings verboseMode (knownProcNames mod)
    (annFns, (ctx, tcenv)) <- mapFoldM sortedFns (ctx0, tcenv0) typecheckFnSCC
    unTc tcenv (convertTypeILofAST mod ctx annFns)
 where
   computeContextBindings :: [(String, TypeAST)] -> [ContextBinding TypeAST]
   computeContextBindings decls = map pair2binding decls

   knownProcNames mod =
     Set.fromList $ concatMap fnNames (moduleASTfunctions mod) ++
                    concatMap procNames (moduleASTdecls mod)
        where
           fnNames f = [fnAstName f]
           isProcType (FnTypeAST _ _ _ FT_Proc) = True
           isProcType  _                        = False
           procNames (name, ty) | isProcType ty = [name]
                                | otherwise     = []

   convertTypeILofAST :: ModuleAST FnAST TypeAST
                      -> Context TypeAST
                      -> [OutputOr AnnExpr]
                      -> Tc (Context TypeIL, ModuleAST (Fn AIExpr) TypeIL)
   convertTypeILofAST mod ctx_ast oo_annfns = do
     decls  <- mapM convertDecl (moduleASTdecls mod)
     ctx_il <- liftContextM ilOf ctx_ast
     aiFns  <- mapM (tcInject ail) oo_annfns
     let m = ModuleAST [f | (E_AIFn f) <- aiFns]
                       decls (moduleASTsourceLines mod)
     return (ctx_il, m)
       where
        convertDecl :: (String, TypeAST) -> Tc (String, TypeIL)
        convertDecl (s, ty) = do
          t <- ilOf ty
          return (s, t)

        liftContextM :: Monad m => (t1 -> m t2) -> Context t1 -> m (Context t2)
        liftContextM f (Context cb pb vb kp) = do
          cb' <- mapM (liftBinding f) cb
          pb' <- mapM (liftBinding f) pb
          return $ Context cb' pb' vb kp

        liftBinding :: Monad m => (t1 -> m t2) -> ContextBinding t1 -> m (ContextBinding t2)
        liftBinding f (TermVarBinding s (TypedId t i)) = do
          t2 <- f t
          return $ TermVarBinding s (TypedId t2 i)

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
                         let kmod = kNormalizeModule mod
                         let prog = closureConvertAndLift ctx_il kmod
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

