-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Main (main) where

import Text.ProtocolBuffers(messageGet)

import System.Environment(getArgs,getProgName)
import System.Console.ANSI(Color(..))

import qualified Data.ByteString.Lazy as L(readFile)
import qualified Data.Text as T
import qualified Data.Map as Map(fromList, toList)
import qualified Data.Set as Set(filter, toList, fromList, notMember)
import qualified Data.Graph as Graph(SCC, flattenSCC, stronglyConnComp)
import Data.Map(Map)
import Data.Set(Set)

import Data.IORef(IORef, newIORef, readIORef)
import Data.Traversable(mapM)
import Prelude hiding (mapM)
import Control.Monad.State(forM, when, forM_, StateT, runStateT, gets,
                           liftIO, liftM, liftM2)

import Foster.Base
import Foster.CFG
import Foster.Fepb.WholeProgram(WholeProgram)
import Foster.ProtobufFE(parseWholeProgram)
import Foster.ProtobufIL(dumpMonoModuleToProtobuf)
import Foster.ExprAST
import Foster.TypeAST
import Foster.ParsedType
import Foster.AnnExpr(AnnExpr, AnnExpr(E_AnnFn))
import Foster.AnnExprIL(AIExpr, fnOf)
import Foster.TypeIL(TypeIL, ilOf, extendTyCtx)
import Foster.ILExpr(closureConvertAndLift, showILProgramStructure)
import Foster.MonoExpr(MonoProgram, showMonoProgramStructure)
import Foster.KNExpr(kNormalizeModule)
import Foster.Typecheck
import Foster.Context
import Foster.Monomo
import Foster.KSmallstep
import Foster.Output
import Foster.MainCtorHelpers
import Foster.ConvertExprAST
import Foster.MainOpts

-----------------------------------------------------------------------
-- TODO shouldn't claim successful typechecks until we reach AnnExprIL.

pair2binding (nm, ty) = TermVarBinding nm (TypedId ty (GlobalSymbol nm))

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Bool -> Bool
               -> Graph.SCC (FnAST TypeAST)  ->   (Context TypeAST, TcEnv)
               -> IO ([OutputOr (AnnExpr Sigma)], (Context TypeAST, TcEnv))
typecheckFnSCC showASTs showAnnExprs scc (ctx, tcenv) = do
    let fns = Graph.flattenSCC scc

    -- Generate bindings (for functions without user-provided declarations)
    -- before doing any typechecking, so that if a function fails to typecheck,
    -- we'll have the best binding on hand to use for subsequent typechecking.
    -- TODO do we gain anything from using Nothing as the expected type for
    --      generated bindings?
    _bindings <- forM fns $ \fn ->
        case termVarLookup (fnAstName fn) (contextBindings ctx) of
          Nothing  -> do newBinding <- unTc tcenv $ bindingForFnAST fn
                         return (Nothing               , newBinding)
          Just tid -> do let binding = TermVarBinding (fnAstName fn) tid
                         return (Just (tidType tid), OK binding)
    let bindings = map (\(t, OK b) -> (t, b)) _bindings

    -- Note that all functions in an SCC are checked in the same environment!
    -- Also note that each function is typechecked with its own binding
    -- in scope (for typechecking recursive calls).
    -- TODO better error messages for type conflicts
    tcResults <- forM (zip fns bindings) $ \(fn, (expectedType, binding)) -> do
        let ast = (E_FnAST fn)
        let name = T.unpack $ fnAstName fn
        putStrLn $ "typechecking " ++ name
        annfn <- unTc tcenv $
             tcSigmaToplevel binding (prependContextBinding ctx binding) ast expectedType

        -- We can't convert AnnExpr to AIExpr here because
        -- the output context is threaded through further type checking.
        return (annfn, (ast, binding))

    -- Dump full ASTs if requested, otherwise just type-incorrect ASTs.
    mapM_ (uncurry inspect) tcResults

    -- The extra bindings of an SCC are the ones generated from successfully
    -- type checked symbols, plus the initial guesses (involving type variables)
    -- for those symbols which could not be checked. This ensures that we don't
    -- undefined-symbol errors when checking subsequent SCCs.
    let (goodexprs, errsAndASTs) = split tcResults
    let newctx = prependContextBindings ctx $ (map bindingOf errsAndASTs) ++
                                   [bindingForAnnFn f |(E_AnnFn f) <- goodexprs]

    if null errsAndASTs
     then return $ (,) (map OK goodexprs) (newctx, tcenv)
     else return $ (,) [Errors [out $ "not all functions type checked in SCC: "
                                  ++ show (map fnAstName fns)]
                        ]                 (newctx, tcenv)

   where
        bindingOf (_errs, (_ast, binding)) = binding

        split fnsAndASTs = (,) [expr        | (OK expr,     _ast) <- fnsAndASTs]
                               [(errs, ast) | (Errors errs,  ast) <- fnsAndASTs]

        inspect :: OutputOr (AnnExpr TypeAST) -> (ExprAST TypeAST, a) -> IO ()
        inspect typechecked (ast, _) =
            case typechecked of
                OK e -> do
                    when showASTs     $ (runOutput $ showStructure ast)
                    when showAnnExprs $ (runOutput $ showStructure e)
                Errors errs -> do
                    runOutput $ showStructure ast
                    runOutput $ (outCSLn Red "Typecheck error: ")
                    printOutputs errs
                    runOutput $ (outLn "")

        bindingForAnnFn :: Fn (AnnExpr TypeAST) TypeAST -> ContextBinding TypeAST
        bindingForAnnFn f = TermVarBinding (identPrefix $ fnIdent f) (fnVar f)

        -- Start with the most specific binding possible (i.e. sigma, not tau).
        -- Otherwise, if we blindly used a meta type variable, we'd be unable
        -- to type check a recursive & polymorphic function.
        bindingForFnAST :: (FnAST TypeAST) -> Tc (ContextBinding TypeAST)
        bindingForFnAST f = do t <- fnTypeTemplate f
                               return $ pair2binding (fnAstName f, t)

        typeTemplateSigma :: Maybe Sigma -> String -> Tc Sigma
        typeTemplateSigma Nothing    name = newTcUnificationVarSigma name
        typeTemplateSigma (Just ty) _name = return ty

        annVarTemplate :: TypedId Sigma -> Tc Sigma
        annVarTemplate v = typeTemplateSigma (Just $ tidType v) (show $ tidIdent v)

        fnTypeTemplate :: (FnAST TypeAST) -> Tc TypeAST
        fnTypeTemplate f = do
          retTy  <- newTcUnificationVarSigma ("ret type for " ++ (T.unpack $ fnAstName f))
          argTys <- mapM annVarTemplate (fnFormals f)
          let fnTy = mkFnType argTys [retTy]
          case fnTyFormals f of
            []        -> return $ fnTy
            tyformals -> return $ ForAllAST (map convertTyFormal tyformals) fnTy

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
    let dts = moduleASTprimTypes modast ++ moduleASTdataTypes modast
    let fns = moduleASTfunctions modast
    let primBindings = computeContextBindings primitiveDecls
    let declBindings = computeContextBindings (moduleASTdecls modast) ++
                       computeContextBindings (concatMap extractCtorTypes dts)
    case detectDuplicates (map fnAstName fns) of
      [] -> do
        let callGraphList = buildCallGraphList fns (Set.fromList $
                                     [nm | TermVarBinding nm _ <- declBindings])
        let sortedFns = Graph.stronglyConnComp callGraphList -- :: [SCC FnAST]
        when verboseMode $ do
                putStrLn $ "Function SCC list : " ++
                       show [(name, frees) | (_, name, frees) <- callGraphList]
        let ctx0 = mkContext declBindings primBindings dts
        let showASTs     = verboseMode
        let showAnnExprs = verboseMode
        (annFns, (ctx, tcenv)) <- mapFoldM sortedFns (ctx0, tcenv0)
                                       (typecheckFnSCC showASTs showAnnExprs)
        unTc tcenv (convertTypeILofAST modast ctx annFns)
      dups -> return (Errors [out $ "Unable to check module due to "
                                 ++ "duplicate bindings: " ++ show dups])
 where
   mkContext declBindings primBindings datatypes =
     Context declBindsMap primBindsMap verboseMode globalvars [] ctorinfo dtypes
       where globalvars   = declBindings ++ primBindings
             ctorinfo     = getCtorInfo  datatypes
             dtypes       = getDataTypes datatypes
             primBindsMap = Map.fromList $ map unbind primBindings
             declBindsMap = Map.fromList $ map unbind declBindings
             unbind (TermVarBinding s t) = (s, t)

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
     ForAllAST (map convertTyFormal tyformals)
      (FnTypeAST (TupleTypeAST ctorArgTypes) (typeOfDataType dt) FastCC FT_Proc)

   buildCallGraphList :: [FnAST TypeAST] -> Set T.Text
                      -> [(FnAST TypeAST, T.Text, [T.Text])]
   buildCallGraphList asts declBindings =
     map (\ast -> (ast, fnAstName ast, fnAstFreeVariables ast)) asts
       where
         fnAstFreeVariables f =
            let allCalledFns = Set.fromList $ freeVars (fnAstBody f) in
            -- Remove everything that isn't a top-level binding.
            let notTopLevel var = Set.notMember var declBindings in
            let nonPrimitives = Set.filter notTopLevel allCalledFns in
            -- remove recursive function name calls
            Set.toList $ Set.filter (\name -> fnAstName f /= name) nonPrimitives

   convertTypeILofAST :: ModuleAST FnAST TypeAST
                      -> Context TypeAST
                      -> [OutputOr (AnnExpr TypeAST)]
                      -> Tc (Context TypeIL, ModuleIL AIExpr TypeIL)
   convertTypeILofAST mAST ctx_ast oo_annfns = do
     ctx_il    <- liftContextM   (ilOf ctx_ast) ctx_ast
     decls     <- mapM (convertDecl (ilOf ctx_ast)) (externalModuleDecls mAST)
     primtypes <- mapM (convertDataTypeAST ctx_ast) (moduleASTprimTypes mAST)
     datatypes <- mapM (convertDataTypeAST ctx_ast) (moduleASTdataTypes mAST)
     aiFns     <- mapM (tcInject (fnOf ctx_ast))
                       (map (fmapOO unFunAnn) oo_annfns)
     let m = ModuleIL aiFns decls datatypes primtypes
                                                  (moduleASTsourceLines mAST)
     return (ctx_il, m)
       where
        -- Note that we discard internal declarations, which are only useful
        -- during type checking. External declarations, on the other hand,
        -- will eventually be needed during linking.
        externalModuleDecls mAST = filter has_no_defn (moduleASTdecls mAST)
          where
            funcnames = map fnAstName (moduleASTfunctions mAST)
            valuenames = Set.fromList funcnames
            has_no_defn (s, _) = Set.notMember (T.pack s) valuenames

        unFunAnn (E_AnnFn f) = f
        unFunAnn _           = error $ "Saw non-AnnFn in unFunAnn"

        fmapOO :: (a -> b) -> OutputOr a -> OutputOr b
        fmapOO  f (OK e)     = OK (f e)
        fmapOO _f (Errors o) = Errors o

        liftContextM :: (Monad m, Show t1, Show t2)
                     => (t1 -> m t2) -> Context t1 -> m (Context t2)
        liftContextM f (Context cb pb vb gb tybinds ctortypeast dtinfo) = do
          cb' <-mmapM (liftTID f) cb
          pb' <- mapM (liftTID f) pb
          gb' <- mapM (liftBinding f) gb
          return $ Context cb' pb' vb gb' tybinds ctortypeast dtinfo

        liftTID :: Monad m => (t1 -> m t2) -> TypedId t1 -> m (TypedId t2)
        liftTID f (TypedId t i) = do t2 <- f t ; return $ TypedId t2 i

        mmapM :: (Monad m, Ord k) => (a -> m b) -> Map k a -> m (Map k b)
        mmapM f ka = do
          kbl <- mapM (\(k, a) -> do b <- f a ; return (k, b)) (Map.toList ka)
          return $ Map.fromList kbl

        -- Wrinkle: need to extend the context used for checking ctors!
        convertDataTypeAST :: Context TypeAST ->
                              DataType TypeAST -> Tc (DataType TypeIL)
        convertDataTypeAST ctx (DataType dtName tyformals ctors) = do
          -- f :: TypeAST -> Tc TypeIL
          let f = ilOf (extendTyCtx ctx $ map convertTyFormal tyformals)
          cts <- mapM (convertDataCtor f) ctors
          return $ DataType dtName tyformals cts
            where
              convertDataCtor f (DataCtor dataCtorName n types) = do
                tys <- mapM f types
                return $ DataCtor dataCtorName n tys

printOutputs :: [Output] -> IO ()
printOutputs outs =
  forM_ outs $ \(output) ->
    do
       runOutput $ output
       runOutput $ (outLn "")

dieOnError :: OutputOr t -> Compiled t
dieOnError (OK     e) = return e
dieOnError (Errors errs) = liftIO $ do
    runOutput (outCSLn Red $ "Unable to type check input module:")
    printOutputs errs
    error "compilation failed"

isTau :: TypeAST -> Bool
isTau (ForAllAST {}) = False
isTau t = all isTau (childrenOf t)

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
    Right (pb_program, _) -> do
        uniqref <- newIORef 1
        varlist <- liftIO $ newIORef []
        let tcenv = TcEnv {       tcEnvUniqs = uniqref,
                           tcUnificationVars = varlist,
                                   tcParents = [] }
        (monoprog, _) <- runStateT (compile pb_program) $ CompilerContext {
                                ccVerbose  = getVerboseFlag flagVals
                              , ccFlagVals = flagVals
                              , ccTcEnv    = tcenv
                         }
        dumpMonoModuleToProtobuf monoprog outfile

compile :: WholeProgram -> Compiled MonoProgram
compile pb_program =
    (return $ parseWholeProgram pb_program)
     >>= mergeModules -- temporary hack
     >>= desugarParsedModule
     >>= typecheckSourceModule
     >>= (uncurry lowerModule)

mergeModules :: WholeProgramAST FnAST TypeP
              -> Compiled (ModuleAST FnAST TypeP)
mergeModules (WholeProgramAST modules) = return (foldr1 mergedModules modules)
  -- Modules are listed in reverse dependency order, conveniently.
  -- TODO track explicit module dependency graph, decompose to DAG, etc.
  where mergedModules m1 m2 = ModuleAST {
       moduleASThash        = moduleASThash        m1 -- meh
     , moduleASTfunctions   = moduleASTfunctions   m1 ++ moduleASTfunctions   m2
     , moduleASTdecls       = moduleASTdecls       m1 ++ moduleASTdecls       m2
     , moduleASTdataTypes   = moduleASTdataTypes   m1 ++ moduleASTdataTypes   m2
     , moduleASTsourceLines = moduleASTsourceLines m1 `appendSourceLines`
                                                         moduleASTsourceLines m2
     , moduleASTprimTypes   = moduleASTprimTypes   m1 -- should be the same
                                     }

astOfParsedType :: TypeP -> Tc TypeAST
astOfParsedType typep =
  let q = astOfParsedType in
  case typep of
        PrimIntP         size  -> return $ PrimIntAST         size
        TyConAppP "Int64"   [] -> return $ PrimIntAST         I64
        TyConAppP "Int32"   [] -> return $ PrimIntAST         I32
        TyConAppP "Int8"    [] -> return $ PrimIntAST         I8
        TyConAppP "Bool"    [] -> return $ PrimIntAST         I1
        TyConAppP "Float64" [] -> return $ PrimFloat64
        TyConAppP "Array"  [t] -> liftM  ArrayTypeAST            (q t)
        TyConAppP "Ref"    [t] -> liftM  RefTypeAST              (q t)
        TyConAppP    tc types  -> liftM (TyConAppAST tc) (mapM q types)
        TupleTypeP      types  -> liftM  TupleTypeAST    (mapM q types)
        RefTypeP       t       -> liftM  RefTypeAST              (q t)
        ArrayTypeP     t       -> liftM  ArrayTypeAST            (q t)
        CoroTypeP    s t       -> liftM2 CoroTypeAST       (q s) (q t)
        ForAllP    tvs t       -> liftM (ForAllAST $ map convertTyFormal tvs) (q t)
        TyVarP     tv          -> do return $ TyVarAST tv
        FnTypeP      s t cc cs -> do s' <- q s
                                     t' <- q t
                                     return $ FnTypeAST      s' t' cc cs
        MetaPlaceholder desc -> do newTcUnificationVarTau desc

desugarParsedModule :: ModuleAST FnAST TypeP ->
             Compiled (ModuleAST FnAST TypeAST)
desugarParsedModule m = do
  tcenv <- gets ccTcEnv
  (liftIO $ unTc tcenv (convertModule astOfParsedType m)) >>= dieOnError

typecheckSourceModule :: ModuleAST FnAST TypeAST
                      -> Compiled (ModuleIL AIExpr TypeIL, Context TypeIL)
typecheckSourceModule sm = do
    verboseMode <- gets ccVerbose
    tcenv       <- gets ccTcEnv
    (ctx_il, ai_mod) <- (liftIO $ typecheckModule verboseMode sm tcenv)
                      >>= dieOnError
    showGeneratedMetaTypeVariables (tcUnificationVars tcenv) ctx_il
    return (ai_mod, ctx_il)

lowerModule :: ModuleIL AIExpr TypeIL
            -> Context TypeIL
            -> Compiled MonoProgram
lowerModule ai_mod ctx_il = do
     let kmod = kNormalizeModule ai_mod ctx_il

     whenDumpIR "kn" $ do
        forM_ (moduleILfunctions kmod) (\fn -> do
           runOutput (outLn $ "vvvv k-normalized :====================")
           runOutput (outLn $ show (fnVar fn))
           runOutput (showStructure (fnBody fn)))

     cfgmod   <- cfgModule      kmod
     prog0    <- closureConvert cfgmod
     let monoprog = monomorphize prog0

     whenDumpIR "cfg" $ do
         runOutput $ (outLn "/// Closure-converted program =========")
         runOutput $ showILProgramStructure prog0
         runOutput $ (outLn "^^^ ===================================")

     whenDumpIR "mono" $ do
         runOutput $ (outLn "/// Monomorphized program =============")
         runOutput $ showMonoProgramStructure monoprog
         runOutput $ (outLn "^^^ ===================================")

     maybeInterpretKNormalModule kmod
     return monoprog

  where
    cfgModule kmod = do
        uniqref <- gets (tcEnvUniqs.ccTcEnv)
        liftIO $ do
            cfgFuncs <- mapM (computeCFGIO uniqref) (moduleILfunctions kmod)
            return $ kmod { moduleILfunctions = cfgFuncs }

    closureConvert cfgmod = do
        uniqref <- gets (tcEnvUniqs.ccTcEnv)
        liftIO $ do
            let datatypes = moduleILprimTypes cfgmod ++
                            moduleILdataTypes cfgmod
            let dataSigs = dataTypeSigs datatypes
            u0 <- readIORef uniqref
            return $ closureConvertAndLift dataSigs u0 cfgmod

    maybeInterpretKNormalModule kmod = do
        flagVals <- gets ccFlagVals
        case getInterpretFlag flagVals of
            Nothing -> return ()
            Just tmpDir -> do
                let cmdLineArgs = getProgArgs flagVals
                _unused <- liftIO $ interpretKNormalMod kmod tmpDir cmdLineArgs
                return ()

showGeneratedMetaTypeVariables :: (Show ty) =>
                               IORef [MetaTyVar] -> Context ty -> Compiled ()
showGeneratedMetaTypeVariables varlist ctx_il =
  ccWhen ccVerbose $ do
    metaTyVars <- readIORef varlist
    runOutput $ (outLn $ "generated " ++ (show $ length metaTyVars) ++ " meta type variables:")
    forM_ metaTyVars $ \mtv -> do
        t <- readIORef (mtvRef mtv)
        let wasTau = fmap isTau t /= Just False
        if mtvConstraint mtv == MTVTau && not wasTau
         then runOutput (outLn $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t) -- error $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t ++ " wasn't a tau!"
         else runOutput (outLn $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t)
    runOutput $ (outLn "vvvv contextBindings:====================")
    runOutput $ (outCSLn Yellow (joinWith "\n" $ map show (Map.toList $ contextBindings ctx_il)))

type Compiled = StateT CompilerContext IO
data CompilerContext = CompilerContext {
        ccVerbose   :: Bool
      , ccFlagVals  :: ([Flag], [String])
      , ccTcEnv     :: TcEnv
}

ccWhen :: (CompilerContext -> Bool) -> IO () -> Compiled ()
ccWhen getter action = do cond <- gets getter ; liftIO $ when cond action

whenDumpIR :: String -> IO () -> Compiled ()
whenDumpIR ir action = do flags <- gets ccFlagVals
                          let cond = getDumpIRFlag ir flags
                          liftIO $ when cond action
