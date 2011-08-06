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
import System.Console.ANSI(Color(..))

import qualified Data.ByteString.Lazy as L(readFile)

import List(all)
import Data.Map(Map)
import qualified Data.Map as Map(fromList, unionsWith)
import qualified Data.Set as Set(filter, toList, fromList)
import qualified Data.Graph as Graph(SCC, flattenSCC, stronglyConnComp)
import Data.Maybe(isNothing)
import Control.Monad.State(forM, when, forM_)
import Data.IORef(newIORef, readIORef)

import Text.ProtocolBuffers(messageGet)

import Foster.Base
import Foster.ProtobufFE(parseSourceModule)
import Foster.ProtobufIL(dumpModuleToProtobufIL)
import Foster.ExprAST
import Foster.TypeAST
import Foster.AnnExpr(AnnExpr, AnnExpr(E_AnnFn), AnnFn,
                      fnNameA, annFnType, annFnIdent)
import Foster.AnnExprIL(AIExpr, fnOf)
import Foster.TypeIL(TypeIL, ilOf)
import Foster.ILExpr(showProgramStructure, closureConvertAndLift)
import Foster.KNExpr(kNormalizeModule)
import Foster.Typecheck
import Foster.Context
import Foster.Monomo
import Foster.Smallstep

-----------------------------------------------------------------------

pair2binding (nm, ty) = TermVarBinding nm (TypedId ty (GlobalSymbol nm))

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

fmapOO :: (a -> b) -> OutputOr a -> OutputOr b
fmapOO f (OK e)     = OK (f e)
fmapOO f (Errors o) = Errors o

-- | Typechecking a module proceeds as follows:
-- |  #. Build separate binding lists for the globally-defined primitiveDecls
-- |     and the module's top-level (function) declarations.
-- |  #. Build a (conservative) dependency graph on the module's top-level
-- |     declarations, yielding a list of SCCs of declarations.
-- |  #. Typecheck the SCCs bottom-up, propagating results as we go along.
-- |  #. Make sure that all unification variables have been properly eliminated,
-- |     or else we consider type checking to have failed
-- |     (no implicit instantiation at the moment!)
typecheckModule :: Bool
                -> ModuleAST FnAST TypeAST
                -> TcEnv
                -> IO (OutputOr (Context TypeIL, ModuleIL AIExpr TypeIL))
typecheckModule verboseMode mod tcenv0 = do
    let fns = moduleASTfunctions mod
    let primBindings = computeContextBindings primitiveDecls
    let declBindings = computeContextBindings (moduleASTdecls mod)
                    ++ computeContextBindings (concatMap extractCtorTypes $
                                               moduleASTdataTypes mod)
    let callGraphList = buildCallGraphList fns declBindings
    let sortedFns = Graph.stronglyConnComp callGraphList -- :: [SCC FnAST]
    putStrLn $ "Function SCC list : " ++
                   show [(name, frees) | (_, name, frees) <- callGraphList]
    let ctx0 = Context declBindings primBindings verboseMode
    (annFns, (ctx, tcenv)) <- mapFoldM sortedFns (ctx0, tcenv0) typecheckFnSCC
    unTc tcenv (convertTypeILofAST mod ctx annFns)
 where
   computeContextBindings :: [(String, TypeAST)] -> [ContextBinding TypeAST]
   computeContextBindings decls = map pair2binding decls

   extractCtorTypes :: DataType TypeAST -> [(String, TypeAST)]
   extractCtorTypes (DataType datatypeName ctors) = map nmCTy ctors
     where nmCTy (DataCtor name _smallId types) =
                          (name, ctorTypeAST datatypeName types)

   ctorTypeAST dtName types =
        FnTypeAST (TupleTypeAST types) (NamedTypeAST dtName) FastCC FT_Proc

   buildCallGraphList :: [FnAST] -> [ContextBinding ty]
                      -> [(FnAST, String, [String])]
   buildCallGraphList asts declBindings =
     map (\ast -> (ast, fnAstName ast, fnAstFreeVariables ast)) asts
       where
         fnAstFreeVariables f =
            let allCalledFns = Set.fromList $ freeVars (fnAstBody f) in
            -- Remove everything that isn't a top-level binding.
            let notTopLevel var = isNothing $ termVarLookup var declBindings in
            let nonPrimitives = Set.filter notTopLevel allCalledFns in
            -- remove recursive function name calls
            Set.toList $ Set.filter (\name -> fnAstName f /= name) nonPrimitives

   convertTypeILofAST :: ModuleAST FnAST TypeAST
                      -> Context TypeAST
                      -> [OutputOr AnnExpr]
                      -> Tc (Context TypeIL, ModuleIL AIExpr TypeIL)
   convertTypeILofAST mod ctx_ast oo_annfns = do
     decls     <- mapM convertDecl (moduleASTdecls mod)
     datatypes <- mapM convertDataType (moduleASTdataTypes mod)
     ctx_il    <- liftContextM ilOf ctx_ast
     aiFns     <- mapM (tcInject fnOf) (map (fmapOO (\(E_AnnFn f) -> f)) oo_annfns)
     let m = ModuleIL aiFns decls datatypes (moduleASTsourceLines mod)
     return (ctx_il, m)
       where
        convertDecl :: (String, TypeAST) -> Tc (String, TypeIL)
        convertDecl (s, ty) = do
          t <- ilOf ty
          return (s, t)

        convertDataType :: DataType TypeAST -> Tc (DataType TypeIL)
        convertDataType (DataType s ctors) = do
          cts <- mapM convertDataCtor ctors
          return $ DataType s cts
            where
              convertDataCtor :: DataCtor TypeAST -> Tc (DataCtor TypeIL)
              convertDataCtor (DataCtor s n types) = do
                tys <- mapM ilOf types
                return $ DataCtor s n tys


        liftContextM :: Monad m => (t1 -> m t2) -> Context t1 -> m (Context t2)
        liftContextM f (Context cb pb vb) = do
          cb' <- mapM (liftBinding f) cb
          pb' <- mapM (liftBinding f) pb
          return $ Context cb' pb' vb

        liftBinding :: Monad m => (t1 -> m t2) -> ContextBinding t1 -> m (ContextBinding t2)
        liftBinding f (TermVarBinding s (TypedId t i)) = do
          t2 <- f t
          return $ TermVarBinding s (TypedId t2 i)

printOutputs :: [Output] -> IO ()
printOutputs outs =
  forM_ outs $ \(output) ->
    do
       runOutput $ output
       runOutput $ (outLn "")

-----------------------------------------------------------------------

getCtorInfo :: [DataType TypeAST] -> Map CtorName [CtorInfo TypeAST]
getCtorInfo datatypes = Map.unionsWith (++) $ map getCtorInfoList datatypes
  where
    getCtorInfoList :: DataType TypeAST -> Map CtorName [CtorInfo TypeAST]
    getCtorInfoList (DataType name ctors) =
          Map.fromList $ map (buildCtorInfo name) ctors

    buildCtorInfo :: DataTypeName -> DataCtor TypeAST
                            -> (CtorName, [CtorInfo TypeAST])
    buildCtorInfo name ctor =
      case ctorIdFor name ctor of (n, c) -> (n, [CtorInfo c ctor])

-----------------------------------------------------------------------

ctorIdFor name ctor = (ctorNameOf ctor, ctorId name ctor)
  where
    ctorNameOf (DataCtor ctorName _n _) = ctorName
    ctorId name (DataCtor ctorName n types) =
      CtorId name ctorName (Prelude.length types) n

-----------------------------------------------------------------------

dataTypeSigs :: [DataType TypeIL] -> Map CtorName DataTypeSig
dataTypeSigs datatypes = Map.fromList $ map ctorIdSet datatypes where
  ctorIdSet :: DataType TypeIL -> (DataTypeName, DataTypeSig)
  ctorIdSet (DataType name ctors) =
      let ctorNameToIdMap = map (ctorIdFor name) ctors in
      (name, DataTypeSig (Map.fromList ctorNameToIdMap))

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

-----------------------------------------------------------------------

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
                return (error $ "Usage: " ++ self
                        ++ " path/to/infile.pb path/to/outfile.pb")

  case messageGet f of
    Left msg -> error $ "Failed to parse protocol buffer.\n" ++ msg
    Right (pb_module, _) -> do
        let verboseMode = getVerboseFlag flagVals
        typecheckSourceModule (parseSourceModule pb_module)
                              outfile flagVals verboseMode

typecheckSourceModule sm outfile flagVals verboseMode = do
    uniqref <- newIORef 1
    varlist <- newIORef []
    let tcenv = TcEnv { tcEnvUniqs = uniqref,
                 tcUnificationVars = varlist,
                         tcParents = [],
                        tcCtorInfo = getCtorInfo (moduleASTdataTypes sm) }
    modResults  <- typecheckModule verboseMode sm tcenv
    case modResults of
      Errors os -> do runOutput (outCSLn Red $ "Unable to type check input module:")
                      printOutputs os
                      error "compilation failed"
      OK (ctx_il, mod) -> do
          when verboseMode (do
              metaTyVars <- readIORef varlist
              runOutput $ (outLn $ "generated " ++ (show $ length metaTyVars) ++ " meta type variables:")
              forM metaTyVars (\mtv@(Meta _ r _) -> do
                  t <- readIORef r
                  runOutput (outLn $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t))

              runOutput $ (outLn "vvvv contextBindings:====================")
              runOutput $ (outCSLn Yellow (joinWith "\n" $ map show (contextBindings ctx_il)))
              )
          lowerModule mod ctx_il
  where
    lowerModule m ctx_il = do
         let kmod = kNormalizeModule m ctx_il

         when verboseMode (do
            forM_ (moduleILfunctions kmod) (\fn -> do
                     runOutput (outLn $ "vvvv k-normalized :====================")
                     runOutput (outLn $ show (fnVar fn))
                     runOutput (showStructure (fnBody fn))))

         let dataSigs = dataTypeSigs (moduleILdataTypes m)

         let prog0 = closureConvertAndLift ctx_il dataSigs kmod

         let monoprog = monomorphize prog0

         when verboseMode (do
             runOutput $ (outLn "/// Monomorphized program =============")
             runOutput $ showProgramStructure monoprog
             runOutput $ (outLn "^^^ ==================================="))

         maybeInterpretProgram monoprog

         dumpModuleToProtobufIL monoprog (outfile ++ ".ll.pb")

         return ()

    maybeInterpretProgram prog = do
        case getInterpretFlag flagVals of
            Nothing -> return ()
            Just tmpDir -> do
                _unused <- interpretProg prog tmpDir
                return ()

