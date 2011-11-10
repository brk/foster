-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Main (main) where

import System.Environment(getArgs,getProgName)
import System.Console.GetOpt
import System.Console.ANSI(Color(..))

import qualified Data.ByteString.Lazy as L(readFile)
import qualified Data.Text as T

import List(all)
import qualified Data.Set as Set(filter, toList, fromList, empty, member, insert)
import qualified Data.Graph as Graph(SCC, flattenSCC, stronglyConnComp)
import Data.Maybe(isNothing)
import Control.Monad.State(forM, when, forM_, StateT, runStateT, gets, liftIO)
import Data.IORef(IORef, newIORef, readIORef)

import Text.ProtocolBuffers(messageGet)

import Foster.Base
import Foster.CFG
import Foster.Fepb.SourceModule(SourceModule)
import Foster.ProtobufFE(parseSourceModule)
import Foster.ProtobufIL(dumpMonoModuleToProtobuf)
import Foster.ExprAST
import Foster.TypeAST
import Foster.AnnExpr(AnnExpr, AnnExpr(E_AnnFn), AnnFn,
                      fnNameA, annFnType, annFnIdent)
import Foster.AnnExprIL(AIExpr, fnOf)
import Foster.TypeIL(TypeIL, ilOf)
import Foster.ILExpr(closureConvertAndLift)
import Foster.MonoExpr(MonoProgram, showMonoProgramStructure)
import Foster.KNExpr(kNormalizeModule)
import Foster.Typecheck
import Foster.Context
import Foster.Monomo
import Foster.KSmallstep
import Foster.Output
import Foster.MainCtorHelpers

-----------------------------------------------------------------------

-- TODO shouldn't claim successful typechecks until we reach AnnExprIL.

pair2binding (nm, ty) = TermVarBinding nm (TypedId ty (GlobalSymbol nm))

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Graph.SCC FnAST   ->    (Context TypeAST, TcEnv)
               -> IO ([OutputOr AnnExpr], (Context TypeAST, TcEnv))
typecheckFnSCC scc (ctx, tcenv) = do
    let fns = Graph.flattenSCC scc
    annfns <- forM fns $ \fn -> do
        let ast = (E_FnAST fn)
        let name = T.unpack $ fnAstName fn
        putStrLn $ "typechecking " ++ name
        annfn <- unTc tcenv $
                    do binding <- bindingForFnAST fn
                       typecheck (prependContextBinding ctx binding) ast Nothing
        -- We can't convert AnnExpr to AIExpr here because
        -- the output context is threaded through further type checking.
        _ <- inspect annfn ast
        return annfn
    if List.all isOK annfns
     then let afns = [f | (OK (E_AnnFn f)) <- annfns] in
          let newbindings = map bindingForAnnFn afns in
          return (annfns, (prependContextBindings ctx newbindings, tcenv))
     else return ([Errors [out $ "not all functions type checked correctly in SCC: "
                             ++ show [fnAstName f | f <- fns]]
           ],(ctx, tcenv))

   where
        bindingForAnnFn :: AnnFn -> ContextBinding TypeAST
        bindingForAnnFn f = TermVarBinding (fnNameA f) annFnVar
         where   annFnVar = TypedId (annFnType f) (annFnIdent f)

        -- Start with the most specific binding possible (i.e. sigma, not tau).
        -- Otherwise, if we blindly used a meta type variable, we'd be unable
        -- to type check a recursive & polymorphic function.
        bindingForFnAST :: FnAST -> Tc (ContextBinding TypeAST)
        bindingForFnAST f = do t <- fnTypeTemplate f
                               return $ pair2binding (fnAstName f, t)

        typeTemplate :: Maybe TypeAST -> String -> Tc TypeAST
        typeTemplate Nothing    name = newTcUnificationVar name
        typeTemplate (Just ty) _name = return ty

        annVarTemplate :: TypedId TypeAST -> Tc TypeAST
        annVarTemplate v = typeTemplate (Just $ tidType v) (show $ tidIdent v)

        fnTypeTemplate :: FnAST -> Tc TypeAST
        fnTypeTemplate f = do
          retTy  <- typeTemplate (fnRetType f) ("ret type for " ++ (T.unpack $ fnAstName f))
          argTys <- mapM annVarTemplate (fnFormals f)
          let fnTy = mkFnType argTys [retTy]
          case fnTyFormals f of
            []        -> return $ fnTy
            tyformals -> return $ ForAllAST (map ktyvarFor tyformals) fnTy
                         where ktyvarFor (TypeFormalAST s k) = (BoundTyVar s, k)

        inspect :: OutputOr AnnExpr -> ExprAST -> IO Bool
        inspect typechecked ast =
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

detectDuplicates :: Ord a => [a] -> [a]
detectDuplicates xs = go xs Set.empty Set.empty
  where go []    _seen dups = Set.toList dups
        go (x:xs) seen dups =
          if Set.member x seen then go xs seen (Set.insert x dups)
                               else go xs (Set.insert x seen) dups

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
typecheckModule verboseMode modast tcenv0 = do
    let fns = moduleASTfunctions modast
    let primBindings = computeContextBindings primitiveDecls
    let declBindings = computeContextBindings (moduleASTdecls modast) ++
                       computeContextBindings (concatMap extractCtorTypes $
                                               moduleASTdataTypes modast)
    case detectDuplicates (map fnAstName fns) of
      [] -> do
        let callGraphList = buildCallGraphList fns declBindings
        let sortedFns = Graph.stronglyConnComp callGraphList -- :: [SCC FnAST]
        putStrLn $ "Function SCC list : " ++
                       show [(name, frees) | (_, name, frees) <- callGraphList]
        let ctx0 = mkContext declBindings primBindings
        (annFns, (ctx, tcenv)) <- mapFoldM sortedFns (ctx0, tcenv0) typecheckFnSCC
        unTc tcenv (convertTypeILofAST modast ctx annFns)
      dups -> return (Errors [out $ "Unable to check module due to "
                                 ++ "duplicate bindings: " ++ show dups])
 where
   mkContext declBindings primBindings =
     Context declBindings primBindings verboseMode globalvars
       where globalvars   = declBindings ++ primBindings

   computeContextBindings :: [(String, TypeAST)] -> [ContextBinding TypeAST]
   computeContextBindings decls = map (\(s,t) -> pair2binding (T.pack s, t)) decls

   -- Given a data type  T (A1::K1) ... (An::Kn)
   -- returns the type   T A1 .. An   (with A1..An free).
   typeOfDataType :: DataType TypeAST -> TypeAST
   typeOfDataType dt =
     let boundTyVarFor (TypeFormalAST name _kind) = TyVarAST $ BoundTyVar name in
     TyConAppAST (dataTypeName dt) (map boundTyVarFor $ dataTypeTyFormals dt)

   extractCtorTypes :: DataType TypeAST -> [(String, TypeAST)]
   extractCtorTypes dt = map nmCTy (dataTypeCtors dt)
     where nmCTy (DataCtor name _tag types) =
                 (T.unpack name, ctorTypeAST (dataTypeTyFormals dt) dt types)

   ctorTypeAST [] dt ctorArgTypes =
       FnTypeAST (TupleTypeAST ctorArgTypes) (typeOfDataType dt) FastCC FT_Proc

   ctorTypeAST tyformals dt ctorArgTypes =
     let convertTyFormal (TypeFormalAST name kind) = (BoundTyVar name, kind) in
     ForAllAST (map convertTyFormal tyformals)
      (FnTypeAST (TupleTypeAST ctorArgTypes) (typeOfDataType dt) FastCC FT_Proc)

   buildCallGraphList :: [FnAST] -> [ContextBinding ty]
                      -> [(FnAST, T.Text, [T.Text])]
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
   convertTypeILofAST mAST ctx_ast oo_annfns = do
     decls     <- mapM convertDecl (moduleASTdecls mAST)
     datatypes <- mapM convertDataType (moduleASTdataTypes mAST)
     ctx_il    <- liftContextM ilOf ctx_ast
     aiFns     <- mapM (tcInject fnOf)
                       (map (fmapOO (\(E_AnnFn f) -> f)) oo_annfns)
     let m = ModuleIL aiFns decls datatypes (moduleASTsourceLines mAST)
     return (ctx_il, m)
       where
        fmapOO :: (a -> b) -> OutputOr a -> OutputOr b
        fmapOO  f (OK e)     = OK (f e)
        fmapOO _f (Errors o) = Errors o

        convertDecl :: (String, TypeAST) -> Tc (String, TypeIL)
        convertDecl (s, ty) = do t <- ilOf ty ; return (s, t)

        convertDataType :: DataType TypeAST -> Tc (DataType TypeIL)
        convertDataType (DataType dtName tyformals ctors) = do
          cts <- mapM convertDataCtor ctors
          return $ DataType dtName tyformals cts
            where
              convertDataCtor :: DataCtor TypeAST -> Tc (DataCtor TypeIL)
              convertDataCtor (DataCtor dataCtorName n types) = do
                tys <- mapM ilOf types
                return $ DataCtor dataCtorName n tys

        liftContextM :: (Monad m, Show t1, Show t2)
                     => (t1 -> m t2) -> Context t1 -> m (Context t2)
        liftContextM f (Context cb pb vb gb) = do
          cb' <- mapM (liftBinding f) cb
          pb' <- mapM (liftBinding f) pb
          gb' <- mapM (liftBinding f) gb
          return $ Context cb' pb' vb gb'

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

getInterpretFlag (flags, _) =
   foldr (\f a -> case f of Interpret d -> Just d  ; _ -> a) Nothing flags

getVerboseFlag (flags, _) =
   foldr (\f a -> case f of Verbose     -> True    ; _ -> a) False flags

-----------------------------------------------------------------------

main = do
  args <- getArgs
  (protobuf, outfile, flagVals) <- case args of
         (infile : outfile : rest) -> do
                protobuf <- L.readFile infile
                flagVals <- parseOpts rest
                return (protobuf, outfile, flagVals)
         _ -> do
                self <- getProgName
                return (error $ "Usage: " ++ self
                        ++ " path/to/infile.pb path/to/outfile.pb")

  case messageGet protobuf of
    Left msg -> error $ "Failed to parse protocol buffer.\n" ++ msg
    Right (pb_module, _) -> do
        uniqref <- newIORef 1
        (monoprog, _) <- runStateT (compile pb_module) $ CompilerContext {
                                ccVerbose  = getVerboseFlag flagVals
                              , ccFlagVals = flagVals
                              , ccUnique   = uniqref
                         }
        dumpMonoModuleToProtobuf monoprog outfile

compile :: SourceModule -> Compiled MonoProgram
compile pb_module =
    (return $ parseSourceModule pb_module)
     >>= typecheckSourceModule
     >>= (uncurry lowerModule)

typecheckSourceModule :: ModuleAST FnAST TypeAST
                      -> Compiled (ModuleIL AIExpr TypeIL, Context TypeIL)
typecheckSourceModule sm = do
    uniqref <- gets ccUnique
    varlist <- liftIO $ newIORef []
    let tcenv = TcEnv { tcEnvUniqs = uniqref,
                 tcUnificationVars = varlist,
                         tcParents = [],
                        tcCtorInfo = getCtorInfo (moduleASTdataTypes sm) }
    verboseMode <- gets ccVerbose
    modResults <- liftIO $ typecheckModule verboseMode sm tcenv
    case modResults of
        Errors os -> liftIO $ do
            runOutput (outCSLn Red $ "Unable to type check input module:")
            printOutputs os
            error "compilation failed"
        OK (ctx_il, ai_mod) -> do
            showGeneratedMetaTypeVariables varlist ctx_il
            return (ai_mod, ctx_il)

lowerModule :: ModuleIL AIExpr TypeIL
            -> Context TypeIL
            -> Compiled MonoProgram
lowerModule ai_mod ctx_il = do
     let kmod = kNormalizeModule ai_mod ctx_il

     whenVerbose $ do
        forM_ (moduleILfunctions kmod) (\fn -> do
           runOutput (outLn $ "vvvv k-normalized :====================")
           runOutput (outLn $ show (fnVar fn))
           runOutput (showStructure (fnBody fn)))

     cfgmod   <- cfgModule      kmod
     prog0    <- closureConvert cfgmod
     let monoprog = monomorphize prog0

     whenVerbose $ do
         runOutput $ (outLn "/// Monomorphized program =============")
         runOutput $ showMonoProgramStructure monoprog
         runOutput $ (outLn "^^^ ===================================")

     maybeInterpretKNormalModule kmod
     return monoprog

  where
    cfgModule kmod = do
        uniqref <- gets ccUnique
        liftIO $ do
            cfgFuncs <- mapM (computeCFGIO uniqref) (moduleILfunctions kmod)
            return $ kmod { moduleILfunctions = cfgFuncs }

    closureConvert cfgmod = do
        uniqref <- gets ccUnique
        liftIO $ do
            let dataSigs = dataTypeSigs (moduleILdataTypes cfgmod)
            u0 <- readIORef uniqref
            return $ closureConvertAndLift dataSigs u0 cfgmod

    maybeInterpretKNormalModule kmod = do
        flagVals <- gets ccFlagVals
        case getInterpretFlag flagVals of
            Nothing -> return ()
            Just tmpDir -> do
                _unused <- liftIO $ interpretKNormalMod kmod tmpDir
                return ()

showGeneratedMetaTypeVariables :: (Show ty) =>
                               IORef [MetaTyVar] -> Context ty -> Compiled ()
showGeneratedMetaTypeVariables varlist ctx_il =
  whenVerbose $ do
    metaTyVars <- readIORef varlist
    runOutput $ (outLn $ "generated " ++ (show $ length metaTyVars) ++ " meta type variables:")
    forM_ metaTyVars (\mtv@(Meta _ r _) -> do
        t <- readIORef r
        runOutput (outLn $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t))

    runOutput $ (outLn "vvvv contextBindings:====================")
    runOutput $ (outCSLn Yellow (joinWith "\n" $ map show (contextBindings ctx_il)))

type Compiled = StateT CompilerContext IO
data CompilerContext = CompilerContext {
        ccVerbose :: Bool
      , ccFlagVals :: ([Flag], [String])
      , ccUnique  :: IORef Uniq
}

whenVerbose :: IO () -> Compiled ()
whenVerbose action = do verbose <- gets ccVerbose ; liftIO $ when verbose action
