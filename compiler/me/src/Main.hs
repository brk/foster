-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Main (main) where

import System.Environment(getArgs,getProgName)

import qualified Data.ByteString.Lazy as L(readFile)
import qualified Data.Text as T
import qualified Data.Map as Map(fromList, toList, empty)
import qualified Data.Set as Set(filter, toList, fromList, notMember, intersection)
import qualified Data.Graph as Graph(SCC, flattenSCC, stronglyConnComp, stronglyConnCompR)
import Data.Map(Map)
import Data.Set(Set)
import qualified Data.Sequence as Seq(length)

import qualified Data.Char as Char(isAlphaNum)
import Data.IORef(newIORef, readIORef, writeIORef)
import Data.Traversable(mapM)
import Prelude hiding (mapM, (<$>))
import Control.Monad.State(forM, when, forM_, evalStateT, gets,
                           liftIO, liftM, liftM2)
import Control.Monad.Trans.Except(runExceptT)
import System.Exit(exitFailure)

import Foster.Base
import Foster.Config
import Foster.CFG
import Foster.CFGOptimization
import Foster.ProtobufFE(cb_parseWholeProgram)
import Foster.ProtobufIL(dumpILProgramToProtobuf)
import Foster.TypeTC
import Foster.ExprAST
import Foster.TypeAST
import Foster.ParsedType
import Foster.PrettyExprAST()
import Foster.AnnExpr(AnnExpr, AnnExpr(E_AnnFn, E_AnnVar, AnnCall, AnnLetFuns))
import Foster.ILExpr(ILProgram, showILProgramStructure, prepForCodegen)
import Foster.KNExpr(KNExpr', kNormalizeModule, knLoopHeaders, knSinkBlocks,
                     knInline, knSize, renderKN,
                     handleCoercionsAndConstraints, collectIntConstraints)
import Foster.KNUtil(KNExpr, TypeIL)
import Foster.Typecheck
import Foster.Context
import Foster.CloConv(closureConvertAndLift, renderCC, CCBody(..))
import Foster.Monomo
import Foster.MonoType
import Foster.KNStaticChecks
import Foster.KSmallstep
import Foster.MainCtorHelpers
import Foster.ConvertExprAST
import Foster.MainOpts
import Foster.MKNExpr
import Foster.Kind(Kind(KindPointerSized))

import Data.Binary.Get
import Data.Binary.CBOR

import Text.Printf(printf)
import Foster.Output
import Text.PrettyPrint.ANSI.Leijen((<+>), (<>), (<$>), pretty, text, line, hsep,
                                     fill, parens, vcat, list, red, dullyellow)
import qualified Criterion.Measurement as Criterion(initializeTime, secs)

pair2binding (nm, ty, mcid) = TermVarBinding nm (TypedId ty (GlobalSymbol nm), mcid)

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Bool -> Bool -> Bool
               -> Graph.SCC (FnAST TypeAST)    ->   (Context TypeTC, TcEnv)
               -> IO ([OutputOr (AnnExpr SigmaTC)], (Context TypeTC, TcEnv))
typecheckFnSCC showASTs showAnnExprs pauseOnErrors scc (ctx, tcenv) = do
    let fns = Graph.flattenSCC scc

    -- Generate a binding (for functions without user-provided declarations)
    -- before doing any typechecking, so that SCC-recursive calls aren't left
    -- out in the cold.
    let genBinding :: FnAST TypeAST -> IO (ContextBinding TypeTC)
        genBinding fn = do
          oo_binding <-
              case termVarLookup (fnAstName fn) (contextBindings ctx) of
                  Nothing  -> do unTc tcenv $ bindingForFnAST ctx fn
                  Just cxb -> do return (OK $ TermVarBinding (fnAstName fn) cxb)
          case oo_binding of
            OK binding  -> return binding
            Errors errs -> error $ show (fnAstName fn) ++ " ;; " ++
                                   show (termVarLookup (fnAstName fn) (contextBindings ctx))
                                   ++ " \n " ++ show errs

    bindings <- mapM genBinding fns
    let extCtx = prependContextBindings ctx bindings

    -- Note that all functions in an SCC are checked in the same environment!
    -- Also note that each function is typechecked with its own binding
    -- in scope (for typechecking recursive calls).
    -- TODO better error messages for type conflicts
    tcResults <- forM (zip bindings fns) $ \(binding, fn) -> do
        let ast = (E_FnAST (fnAstAnnot fn) fn)
        let name = T.unpack $ fnAstName fn

        when False $ do
          putStrLn $ "typechecking " ++ name ++ " with binding " ++ show binding

        annfn <- unTc tcenv $ tcSigmaToplevel binding extCtx ast

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
                                  [bindingForAnnFn f | (E_AnnFn f) <- goodexprs]

    if null errsAndASTs
     then return $ (,) (map OK goodexprs) (newctx, tcenv)
     else return $ (,) [Errors [text $ "not all functions type checked in SCC: "
                                  ++ show (map fnAstName fns)]
                        ]                 (newctx, tcenv)

   where
        bindingOf (_errs, (_ast, binding)) = binding

        split fnsAndASTs = (,) [expr        | (OK expr,     _ast) <- fnsAndASTs]
                               [(errs, ast) | (Errors errs,  ast) <- fnsAndASTs]

        inspect :: OutputOr (AnnExpr TypeTC) -> (ExprAST TypeAST, a) -> IO ()
        inspect typechecked (ast, _) =
            case typechecked of
                OK e -> do
                    when showASTs     $ (putDocLn $ showStructure ast)
                    when showAnnExprs $ do
                        putStrLn $ "[[[[[["
                        putDocLn $ showStructure e
                        putStrLn $ "]]]]]]"
                Errors errs -> do
                    putDocLn $ showStructure ast
                    putDocLn $ red $ text "Typecheck error: "
                    forM_ errs putDocLn
                    putDocP line
                    when pauseOnErrors $ do
                        putStrLn "Press ENTER to continue..."
                        _ <- getLine
                        return ()

        bindingForAnnFn :: Fn () (AnnExpr ty) ty -> ContextBinding ty
        bindingForAnnFn f = TermVarBinding (identPrefix $ fnIdent f) (fnVar f, Nothing)

        -- Start with the most specific binding possible (i.e. sigma, not tau).
        -- Otherwise, if we blindly used a meta type variable, we'd be unable
        -- to type check a recursive & polymorphic function.
        bindingForFnAST :: Context TypeTC -> FnAST TypeAST -> Tc (ContextBinding TypeTC)
        bindingForFnAST ctx f = do
            t <- fnTypeShallow ctx f
            return $ pair2binding (fnAstName f, t, Nothing)

typecheckAndFoldContextBindings :: Context TypeTC ->
                                  [ContextBinding TypeAST] ->
                               Tc (Context TypeTC)
typecheckAndFoldContextBindings ctxTC0 bindings = do
  bindings' <- mapM (liftBinding (tcType ctxTC0)) bindings
  return $ prependContextBindings ctxTC0 bindings'

-- | Typechecking a module proceeds as follows:
-- |  #. Build separate binding lists for the globally-defined primitiveDecls
-- |     and the module's top-level (function) declarations.
-- |  #. Build a (conservative) dependency graph on the module's top-level
-- |     declarations, yielding a list of SCCs of declarations.
-- |  #. Typecheck the SCCs bottom-up, propagating results as we go along.
-- |  #. Make sure that all unification variables have been properly eliminated,
-- |     or else we consider type checking to have failed
-- |     (no implicit instantiation at the moment!)
typecheckModule :: Bool -> Bool -> Bool -> ([Flag], strings)
                -> ModuleAST FnAST TypeAST
                -> TcEnv
                -> Compiled (OutputOr TCRESULT)
typecheckModule verboseMode pauseOnErrors standalone flagvals modast tcenv0 = do
    liftIO $ when verboseMode $ do
        putDocLn $ text "module AST decls:" <$> pretty (moduleASTdecls modast)
    let dts = moduleASTprimTypes modast ++ moduleASTdataTypes modast
    let fns = moduleASTfunctions modast
    let filteredDecls = if standalone
                          then filter okForStandalone primitiveDecls
                          else primitiveDecls
        okForStandalone (nm, _) = nm `elem` ["foster__logf64"
                                            ,"prim_arrayLength"
                                            ,"coro_create"
                                            ,"coro_invoke"
                                            ,"coro_yield"
                                            ]

    let primBindings = computeContextBindings' (filteredDecls ++ primopDecls)
    let allCtorTypes = concatMap extractCtorTypes dts
    let (nullCtors, nonNullCtors) = splitCtorTypes allCtorTypes
    let declBindings = computeContextBindings' (moduleASTdecls modast) ++
                       computeContextBindings nonNullCtors
    let nullCtorBindings = computeContextBindings nullCtors

    liftIO $ when verboseMode $ do
        putDocLn $ (outLn "vvvv declBindings:====================")
        putDocLn $ (dullyellow (vcat $ map (text . show) declBindings))

    case detectDuplicates $ map fnAstName fns of
      [] -> do
        let declCG = buildCallGraphList' declBindings (Set.fromList $ map (\(TermVarBinding nm _) -> nm) declBindings)
        let globalids = map (\(TermVarBinding _ (tid, _)) -> tidIdent tid) $ declBindings ++ primBindings
        let declBindings' = topoSortBindingSCC $ Graph.stronglyConnCompR declCG -- :: [ [ContextBinding TypeAST] ]
        let primOpMap = Map.fromList [(T.pack nm, prim)
                            | (nm, (_, prim)) <- Map.toList gFosterPrimOpsTable]

        ctxErrsOrOK <- liftIO $ unTc tcenv0 $ do
                         let ctxAS1 = mkContext (computeContextBindings nonNullCtors)
                                         nullCtorBindings primBindings primOpMap globalids dts
                         let ctxTC0 = mkContext [] [] [] Map.empty [] []
                         ctxTC1 <- tcContext ctxTC0 ctxAS1
                         foldlM typecheckAndFoldContextBindings ctxTC1 declBindings'
        case ctxErrsOrOK of
          OK ctxTC -> do
            -- declBindings includes datatype constructors and some (?) functions.
            let callGraphList = buildCallGraphList fns (Set.fromList $ map fnAstName fns)
            let sortedFns = Graph.stronglyConnComp callGraphList -- :: [SCC FnAST]
            liftIO $ when verboseMode $ do
                    putStrLn $ "Function SCC list : " ++
                     (unlines $ map show [(name, frees) | (_, name, frees) <- callGraphList])
            let showASTs     = verboseMode || getDumpIRFlag "ast" flagvals
            let showAnnExprs = verboseMode || getDumpIRFlag "ann" flagvals
            (annFnSCCs, (ctx, tcenv)) <- liftIO $
                mapFoldM' sortedFns (ctxTC, tcenv0)
                            (typecheckFnSCC showASTs showAnnExprs pauseOnErrors)
            liftIO $ unTc tcenv (convertTypeILofAST modast ctx annFnSCCs)
          Errors os -> return (Errors os)
      dups -> return (Errors [text $ "Unable to check module due to "
                                  ++ "duplicate bindings: " ++ show dups])
 where
   mkContext :: [ContextBinding t] -> [ContextBinding t]
             -> [ContextBinding t] -> (Map T.Text (FosterPrim t)) -> [Ident] -> [DataType t] -> Context t
   mkContext declBindings nullCtorBnds primBindings primOpMap globalvars datatypes =
     Context declBindsMap nullCtorsMap primBindsMap primOpMap globalvars [] tyvarsMap [] ctorinfo dtypes
       where ctorinfo     = getCtorInfo  datatypes
             dtypes       = getDataTypes datatypes
             primBindsMap = Map.fromList $ map unbind primBindings
             nullCtorsMap = Map.fromList $ map unbind nullCtorBnds
             declBindsMap = Map.fromList $ map unbind declBindings
             tyvarsMap    = Map.fromList []
             unbind (TermVarBinding s t) = (s, t)

   computeContextBindings' :: [(String, TypeAST)] -> [ContextBinding TypeAST]
   computeContextBindings' decls = map (\(s,t) -> pair2binding (T.pack s, t, Nothing)) decls

   computeContextBindings :: [(String, TypeAST, CtorId)] -> [ContextBinding TypeAST]
   computeContextBindings decls = map (\(s,t,cid) -> pair2binding (T.pack s, t, Just cid)) decls

   -- Given a data type  T (A1::K1) ... (An::Kn)
   -- returns the type   T A1 .. An   (with A1..An free).
   typeOfDataType :: DataType TypeAST -> TypeAST
   typeOfDataType dt =
     let boundTyVarFor (TypeFormal name sr _kind) = TyVarAST $ BoundTyVar name sr in
     TyAppAST (TyConAST $ typeFormalName $ dataTypeName dt)
              (map boundTyVarFor $ dataTypeTyFormals dt)

   splitCtorTypes :: [(String, Either TypeAST TypeAST, CtorId)] ->
                    ([(String, TypeAST, CtorId)]
                    ,[(String, TypeAST, CtorId)])
   splitCtorTypes xs = go xs [] []
     where go [] rl rr = (reverse rl, reverse rr)
           go ((nm, Left  ty, cid):xs) rl rr = go xs ((nm, ty, cid):rl) rr
           go ((nm, Right ty, cid):xs) rl rr = go xs rl ((nm, ty, cid):rr)

   extractCtorTypes :: DataType TypeAST -> [(String, Either TypeAST TypeAST, CtorId)]
   extractCtorTypes dt = map nmCTy (dataTypeCtors dt)
     where nmCTy dc@(DataCtor name tyformals types _repr _range) =
                 (T.unpack name, ctorTypeAST tyformals dtType types, cid)
                         where dtType = typeOfDataType dt
                               cid    = ctorId (typeFormalName $ dataTypeName dt) dc

   nullFx = TupleTypeAST []

   -- Nullary constructors are constants; non-nullary ctors are functions.
   ctorTypeAST [] dtType [] = Left dtType
   ctorTypeAST [] dtType ctorArgTypes =
                            Right $ FnTypeAST ctorArgTypes dtType nullFx FastCC FT_Func

   ctorTypeAST tyformals dt ctorArgTypes =
     let f = ForAllAST (map convertTyFormal tyformals) in
     case ctorTypeAST [] dt ctorArgTypes of
       Left ty  -> Left $ f ty
       Right ty -> Right $ f ty

   buildCallGraphList' :: [ContextBinding TypeAST] -> Set T.Text
                      -> [(ContextBinding TypeAST, T.Text, [T.Text])]
   buildCallGraphList' bindings toplevels =
     map (\binding -> (binding, bindingName binding, freeVariables binding)) bindings
       where
         bindingName   (TermVarBinding nm _     ) = nm
         freeVariables (TermVarBinding nm (v, _)) =
            let allCalledFns = Set.fromList $ freeVars v in
            -- Remove everything that isn't a top-level binding.
            let nonPrimitives = Set.intersection allCalledFns toplevels in
            -- remove recursive function name calls
            Set.toList $ Set.filter (\name -> nm /= name) nonPrimitives

   buildCallGraphList :: [FnAST TypeAST] -> Set T.Text
                      -> [(FnAST TypeAST, T.Text, [T.Text])]
   buildCallGraphList asts toplevels =
     map (\ast -> (ast, fnAstName ast, fnAstFreeVariables ast)) asts
       where
         fnAstFreeVariables f =
            let allCalledFns = Set.fromList $ freeVars (fnAstBody f) in
            -- Remove everything that isn't a top-level binding.
            let nonPrimitives = Set.intersection allCalledFns toplevels in
            -- remove recursive function name calls
            Set.toList $ Set.filter (\name -> fnAstName f /= name) nonPrimitives

   -- The functions from the module have already been converted;
   -- now we just need to convert the rest of the module...
   convertTypeILofAST :: ModuleAST FnAST TypeAST
                      -> Context TypeTC
                      -> [[OutputOr (AnnExpr TypeTC)]]
                      -> Tc TCRESULT
   convertTypeILofAST mAST ctx_tc oo_unprocessed = do
     mapM_ (tcInject collectIntConstraints) (concat oo_unprocessed)
     tcApplyIntConstraints

     constraints <- tcGetConstraints
     processTcConstraints constraints

     -- oo_annfns :: [[OutputOr (AnnExpr TypeTC)]]
     oo_annfns <- mapM (mapM (tcInject handleCoercionsAndConstraints)) oo_unprocessed

     let unfuns fns -- :: [[AnnExpr t]] -> [[Fn () (AnnExpr t) t]]
                    = map (map unFunAnn) fns

     -- We've already typechecked the functions, so no need to re-process them...
     -- First, convert the non-function parts of our module from TypeAST to TypeTC.
     -- mTC :: ModuleAST FnAST TypeTC
     mTC <- convertModule (tcType ctx_tc) $ mAST { moduleASTfunctions = [] }

     let mTC' = ModuleIL (buildExprSCC' (unfuns oo_annfns))
                         (externalModuleDecls mTC)
                         (moduleASTdataTypes  mTC)
                         (moduleASTprimTypes  mTC)
                         (moduleASTsourceLines mAST)

     kmod <- kNormalizeModule  mTC' ctx_tc
     return (kmod, globalIdents ctx_tc)

       where
        buildExprSCC' :: [[Fn () (AnnExpr TypeTC) TypeTC]] -> (AnnExpr TypeTC)
        buildExprSCC' [] = error "Main.hs: Can't build SCC of no functions!"
        buildExprSCC' es = let call_of_main = AnnCall (annotForRange $ MissingSourceRange "buildExprSCC'main!") unitTypeTC
                                                (E_AnnVar (annotForRange $ MissingSourceRange "buildExprSCC'main")
                                                          (TypedId mainty (GlobalSymbol $ T.pack "main"), Nothing))
                                                []
                               mainty = FnTypeTC [unitTypeTC] unitTypeTC unitTypeTC (UniConst FastCC) (UniConst FT_Proc)
                          in foldr build call_of_main es
         where build es body = case es of
                    [] -> body
                    _  -> AnnLetFuns (annotForRange $ MissingSourceRange "buildExprSCC'")
                                     (map fnIdent es) es body
               unitTypeTC = TupleTypeTC (UniConst KindPointerSized) []

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

   processTcConstraints :: [(TcConstraint, SourceRange)] -> Tc ()
   processTcConstraints constraints = go constraints
      where go [] = return ()
            go _ = tcFails [text "Constraint processing not yet implemented"]

dieOnError :: OutputOr t -> Compiled t
dieOnError (OK     e) = return e
dieOnError (Errors errs) = liftIO $ do
    putDocLn (red $ text "Unable to type check input module:")
    forM_ errs putDocLn
    error "compilation failed"

topoSortBindingSCC :: [Graph.SCC (ContextBinding TypeAST, T.Text, [T.Text])]
                   -> [ [ContextBinding TypeAST] ]
topoSortBindingSCC allSCCs =
  -- First, pluck out all the SCCs which have no dependencies; they can all
  -- be processed in parallel.
  let go leafs nonleafs []         = (leafs, nonleafs)
      go leafs nonleafs (scc:sccs) =
         case Graph.flattenSCC scc of
           [(binding, _, [])] -> go (binding:leafs) nonleafs sccs
           [(_,      _,  _ )] -> go leafs (scc:nonleafs) sccs
           nodes -> error $ "Main.hs: cannot yet handle recursive nest of type refinements at toplevel: "
                            ++ show (map (\(_, nm, _) -> nm) nodes)
      (leafs, sccs) = go [] [] allSCCs
      flatten scc = map (\(binding, _, _) -> binding) (Graph.flattenSCC scc)
  in
    leafs : map flatten sccs


-----------------------------------------------------------------------

modulesSourceLines (WholeProgramAST mods) =
  let countLines (SourceLines seq) = Seq.length seq in
  map (countLines . moduleASTsourceLines) mods

readAndParseCbor infile = do
  cborbytes <- L.readFile infile
  return $ runGet getCBOR cborbytes

main = do
  Criterion.initializeTime
  args <- getArgs
  case args of
    (infile : outfile : rest) -> do
       flagVals <- parseOpts rest
       (ci_time, cb_program) <- ioTime $ readAndParseCbor infile
       let wholeprog = cb_parseWholeProgram cb_program (getStandaloneFlag flagVals)
       if getFmtOnlyFlag flagVals
         then do
           let WholeProgramAST modules = wholeprog
           liftIO $ putDocLn (pretty (head modules))
         else
           runCompiler ci_time wholeprog flagVals outfile

    rest -> do
      flagVals <- parseOpts rest
      if getDumpPrimitives flagVals
        then dumpAllPrimitives
        else do
           self <- getProgName
           return (error $ "Usage: " ++ self
                   ++ " path/to/infile.cbor path/to/outfile.pb")


runCompiler ci_time wholeprog flagVals outfile = do
   uniqref <- newIORef 2
   varlist <- newIORef []
   subcnst <- newIORef []
   icmap   <- newIORef Map.empty
   constraints <- newIORef []
   smtStatsRef <- newIORef (0, [])
   cfgSizesRef <- newIORef []

   let tcenv = TcEnv {       tcEnvUniqs = uniqref,
                      tcUnificationVars = varlist,
                              tcParents = [],
                   tcMetaIntConstraints = icmap,
                          tcConstraints = constraints,
               tcSubsumptionConstraints = subcnst,
                     tcCurrentFnEffect = Nothing,
                tcUseOptimizedCtorReprs = getCtorOpt flagVals,
                          tcVerboseMode = getVerboseFlag flagVals }
   (nc_time, mb_errs) <- ioTime $ runExceptT $ evalStateT (compile wholeprog tcenv)
                    CompilerContext {
                           ccVerbose  = getVerboseFlag flagVals
                         , ccFlagVals = flagVals
                         , ccDumpFns  = getDumpFns flagVals
                         , ccInline   = getInlining flagVals
                         , ccUniqRef  = uniqref
                         , ccSMTStats = smtStatsRef
                         , ccCFGSizes = cfgSizesRef
                    }

   case mb_errs of
     Left  errs -> do
       putStrLn $ "compilation time: " ++ Criterion.secs (nc_time)
       putDocLn $ red $ text "Compilation failed: "
       forM_ errs putDocLn
       putDocP line
       exitFailure

     Right (RWT in_time sr_time mn_time cg_time cp_time sc_time ilprog) -> do
       (pb_time, _) <- ioTime $ dumpILProgramToProtobuf ilprog outfile
       (nqueries, querytime) <- readIORef smtStatsRef
       reportFinalPerformanceNumbers ci_time nqueries querytime in_time sr_time
                                     mn_time cg_time cp_time sc_time nc_time pb_time
                                     (sum (modulesSourceLines wholeprog))

reportFinalPerformanceNumbers :: Double -> Int -> [ (Double, Double) ]
                              -> Double -> Double -> Double -> Double
                              -> Double -> Double -> Double -> Double
                              -> Int -> IO ()
reportFinalPerformanceNumbers ci_time nqueries querytime in_time sr_time
                              mn_time cg_time cp_time sc_time
                              nc_time pb_time wholeProgNumLines = do
       let ct_time = (nc_time - (in_time + mn_time + cg_time + cp_time + sc_time))
       let total_time = ci_time + pb_time + nc_time
       let pct f1 f2 = (100.0 * f1) / f2
       let fmt_pct time = let p = pct time nc_time
                              n = if p < 10.0 then 2 else if p < 100.0 then 1 else 0
                              padding = fill n (text "") in
                          padding <> parens (text (printf "%.1f" p) <> text "%")
       let fmt str time = text str <+> (fill 11 $ text $ Criterion.secs time) <+> fmt_pct time
       let pairwise f = \(x,y) -> (f x, f (x + y))
       putDocLn $ vcat $ [text "                                            (initial query time, overall query time)"
                         ,text "# SMT queries:" <+> pretty nqueries <+> text "taking" <+> pretty (map (pairwise Criterion.secs) querytime)
                         ,fmt "static-chk  time:" sc_time
                         ,fmt "inlining    time:" in_time
                         ,fmt "shrinking   time:" sr_time
                         ,fmt "monomorphiz time:" mn_time
                         ,fmt "cfg-ization time:" cg_time
                         ,fmt "codegenprep time:" cp_time
                         ,fmt "'other'     time:" ct_time
                         ,fmt "sum elapsed time:" nc_time
                         ,text ""
                         ,fmt "    CBOR-in time:" ci_time
                         ,fmt "protobufout time:" pb_time
                         ,text "overall wall-clock time:" <+> text (Criterion.secs $ total_time)
                         ,text "# source lines:" <+> pretty wholeProgNumLines
                         ,text "source lines/second:" <+> text (printf "%.1f" (fromIntegral wholeProgNumLines / total_time))
                         ]

data ResultWithTimings = RWT Double Double Double Double Double Double ILProgram

compile :: WholeProgramAST FnAST TypeP -> TcEnv -> Compiled ResultWithTimings
compile wholeprog tcenv = do
    (return wholeprog)
     >>= mergeModules -- temporary hack
     >>= desugarParsedModule tcenv
     >>= typecheckSourceModule tcenv
     >>= lowerModule

mergeModules :: WholeProgramAST FnAST ty
              -> Compiled (ModuleAST FnAST ty)
mergeModules (WholeProgramAST modules) = do
  return (foldr1 mergedModules modules)
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

desugarParsedModule :: TcEnv -> ModuleAST FnAST TypeP ->
                      Compiled (ModuleAST FnAST TypeAST)
desugarParsedModule tcenv m = do
  (liftIO $ unTc tcenv (convertModule astOfParsedType m)) >>= dieOnError
 where
  astOfParsedType :: TypeP -> Tc TypeAST
  astOfParsedType typep =
    let q = astOfParsedType in
    case typep of
          TyAppP (TyConP "Word"  )    [] -> return $ PrimIntAST         (IWord 0)
          TyAppP (TyConP "WordX2")    [] -> return $ PrimIntAST         (IWord 1)
          TyAppP (TyConP "Int64" )    [] -> return $ PrimIntAST         I64
          TyAppP (TyConP "Int32" )    [] -> return $ PrimIntAST         I32
          TyAppP (TyConP "Int8"  )    [] -> return $ PrimIntAST         I8
          TyAppP (TyConP "Bool"  )    [] -> return $ PrimIntAST         I1
          TyAppP (TyConP "Array" )   [t] -> liftM  ArrayTypeAST            (q t)
          TyAppP (TyConP "Ref"   )   [t] -> liftM  RefTypeAST              (q t)
          TyAppP (TyConP "Coro"  ) [o,i] -> liftM2 CoroTypeAST       (q o) (q i)
          TyAppP con types       -> liftM2 TyAppAST (q con) (mapM q types)
          TyConP nam             -> return $ TyConAST nam
          TupleTypeP      types  -> liftM  TupleTypeAST    (mapM q types)
          ForAllP    tvs t       -> liftM (ForAllAST $ map convertTyFormal tvs) (q t)
          TyVarP     tv          -> do return $ TyVarAST tv
          FnTypeP s t fx cc cs sr -> do s' <- mapM q s
                                        t' <- q t
                                        fx' <- case fx of
                                                 Nothing -> return $ MetaPlaceholderAST MTVTau   ("effectvar:" ++ showSourceRange sr)
                                                 Just xx -> q xx
                                        return $ FnTypeAST  s' t' fx' cc cs
          RefinedTypeP nm t e -> do t' <- q t
                                    e' <- convertExprAST q e
                                    return $ RefinedTypeAST nm t' e'
          MetaPlaceholder desc -> return $ MetaPlaceholderAST MTVTau desc

type TCRESULT = (ModuleIL KNExpr TypeIL, [Ident])

typecheckSourceModule :: TcEnv ->  ModuleAST FnAST TypeAST
                      -> Compiled (ModuleIL KNExpr TypeIL, [Ident])
typecheckSourceModule tcenv sm = do
    verboseMode <- gets ccVerbose
    flags <- gets ccFlagVals
    let standalone    = getStandaloneFlag  flags
    let pauseOnErrors = getInteractiveFlag flags
    --whenDumpIR "ast" $ do
    --   putDocLn (outLn $ "vvvv AST :====================")
    --   putDocLn (vsep $ map showFnStructure (moduleASTfunctions sm))
    --   putDocLn $ pretty sm
    --   return ()

    res0 <- typecheckModule verboseMode pauseOnErrors standalone flags sm tcenv
    dieOnError res0
    {-
    (ctx_il, ai_mod) <- dieOnError res0

    let dtypes = moduleILdataTypes ai_mod ++ moduleILprimTypes ai_mod
    let dtypeMap = Map.fromList [(typeFormalName (dataTypeName dt), dt) | dt <- dtypes]
    let knorm = kNormalize dtypeMap -- For normalizing expressions in types.
    kmod <- kNormalizeModule ai_mod ctx_il dtypeMap

    return (kmod, knorm, globalIdents ctx_il)
    -}

lowerModule :: (ModuleIL KNExpr TypeIL
               , [Ident] )
            -> Compiled ResultWithTimings
lowerModule (kmod, globals) = do
     inline   <- gets ccInline
     flags    <- gets ccFlagVals
     let donate = getInliningDonate flags
     let insize = getInliningSize   flags

     whenDumpIR "kn" $ do
         putDocLn (outLn $ "vvvv k-normalized :====================")
         putDocLn (showStructure (moduleILbody kmod))
         _ <- liftIO $ renderKN kmod True
         return ()

     (mn_time, monomod0) <- ioTime $ monomorphize   kmod

     whenDumpIR "mono" $ do
         putDocLn $ (outLn "/// Monomorphized program =============")
         putDocLn (showStructure (moduleILbody monomod0))
         putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod0)))
         _ <- liftIO $ renderKN monomod0 True
         putDocLn $ (outLn "^^^ ===================================")

     (sc_time, _) <- ioTime $ runStaticChecks monomod0
     monomod2 <- knLoopHeaders  monomod0

     liftIO $ putDocLn $ text $ "Performing shrinking: " ++ show (getShrinkFlag flags)

     (mkn_time, monomod3) <- ioTime $ do
       if getShrinkFlag flags
        then do
             assocBinders <- sequence [do r <- newOrdRef Nothing
                                          let id  = GlobalSymbol $ T.pack s
                                          let tid = TypedId ty id
                                          let b = MKBound tid r
                                          return (id, b) | (s, ty) <- moduleILdecls monomod2]
             let binders = Map.fromList assocBinders
             mk <- mkOfKN binders (moduleILbody monomod2)
             kn <- mknInline mk
             return $ monomod2 { moduleILbody = kn }
        else return $ monomod2

     (in_time, monomod4) <- ioTime $ (if inline then knInline insize donate else return) monomod3
     monomod  <- knSinkBlocks   monomod4

     whenDumpIR "mono" $ do
         putDocLn $ (outLn "/// Loop-headered program =============")
         putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod2)))
         _ <- liftIO $ renderKN monomod2 True
         putDocLn $ (outLn "^^^ ===================================")

         when (inline || getShrinkFlag flags) $ do
           putDocLn $ (outLn "/// Inlined       program =============")
           putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod4)))
           _ <- liftIO $ renderKN monomod4 True
           putDocLn $ (outLn "^^^ ===================================")

     whenDumpIR "mono-sunk" $ do
         putDocLn $ (outLn "/// Block-sunk program =============")
         _ <- liftIO $ renderKN monomod  True
         putDocLn $ (outLn "^^^ ===================================")

     (cg_time, cfgmod) <- ioTime $ cfgModule      monomod
     let constraints = collectMayGCConstraints (moduleILbody cfgmod)
     whenDumpIR "may-gc" $ do
         liftIO $ putStrLn "\n MAY GC CONSTRAINTS ======================="
         liftIO $ putDocLn $ list (map pretty $ (Map.toList constraints))
         liftIO $ putStrLn "\n/MAY GC CONSTRAINTS ======================="

     whenDumpIR "cfg" $ do
         putDocLn $ (outLn "/// CFG-ized program ==================")
         putDocP  $ pretty cfgmod
         putDocLn $ (outLn "^^^ ===================================")

     ccmod    <- closureConvert cfgmod globals
     whenDumpIR "cc" $ do
         putDocLn $ (outLn "/// Closure-converted program =========")
         _ <- liftIO $ renderCC ccmod True
         putDocLn $ (outLn "^^^ ===================================")

     (cp_time, (ilprog, prealloc)) <- ioTime $ prepForCodegen ccmod  constraints
     whenDumpIR "prealloc" $ do
         putDocLn $ (outLn "/// Pre-allocation ====================")
         _ <- liftIO (renderCC (ccmod { moduleILbody = let (CCB_Procs _ main) = moduleILbody ccmod in
                                                         CCB_Procs prealloc main }) True )
         putDocLn $ (outLn "^^^ ===================================")

     whenDumpIR "il" $ do
         putDocLn $ (outLn "/// ILProgram =========================")
         putDocLn (showILProgramStructure ilprog)
         putDocLn $ (outLn "^^^ ===================================")

     liftIO $ putDocLn $ (text $ "/// Mono    size: " ++ show (knSize (moduleILbody monomod0)))
     when (getShrinkFlag flags) $
       liftIO $ putDocLn $ (text $ "/// Shrunk  size: " ++ show (knSize (moduleILbody monomod3)))
     when (getInlining flags) $
       liftIO $ putDocLn $ (text $ "/// Inlined size: " ++ show (knSize (moduleILbody monomod4)))

     maybeInterpretKNormalModule kmod

     return (RWT in_time mkn_time mn_time cg_time cp_time sc_time ilprog)

  where
    cfgModule :: ModuleIL (KNExpr' RecStatus MonoType) MonoType -> Compiled (ModuleIL CFBody MonoType)
    cfgModule kmod = do
        cfgIdsRef <- liftIO $ newIORef []
        uniqref <- gets ccUniqRef
        cfgBody <- liftIO $ computeCFGs uniqref (moduleILbody kmod)
        cfgBody' <- optimizeCFGs cfgBody cfgIdsRef
        cfgIds <- liftIO $ readIORef cfgIdsRef
        let dups = detectDuplicates cfgIds
        if null dups
          then return $ kmod { moduleILbody = cfgBody' }
          else error $ "Main.hs: detected duplicate functions being CFGized: " ++ show dups

    closureConvert cfgmod globals = do
        uniqref <- gets ccUniqRef
        liftIO $ do
            let datatypes = moduleILprimTypes cfgmod ++
                            moduleILdataTypes cfgmod
            let dataSigs = dataTypeSigs datatypes
            u0 <- readIORef uniqref
            let (rv, u') = closureConvertAndLift dataSigs globals u0 cfgmod
            writeIORef uniqref u'
            return rv

    maybeInterpretKNormalModule kmod = do
        flagVals <- gets ccFlagVals
        case getInterpretFlag flagVals of
            Nothing -> return ()
            Just tmpDir -> do
                let cmdLineArgs = getProgArgs flagVals
                _unused <- liftIO $ interpretKNormalMod kmod tmpDir cmdLineArgs
                return ()

{-
showGeneratedMetaTypeVariables :: (Show ty) =>
                               IORef [MetaTyVar TypeTC] -> Context ty -> Compiled ()
showGeneratedMetaTypeVariables varlist ctx_il =
  ccWhen ccVerbose $ do
    metaTyVars <- readIORef varlist
    putDocLn $ (outLn $ "generated " ++ (show $ length metaTyVars) ++ " meta type variables:")
    forM_ metaTyVars $ \mtv -> do
        t <- readIORef (mtvRef mtv)
        let wasTau = fmap isTau t /= Just False
        if mtvConstraint mtv == MTVTau && not wasTau
         then putDocLn (text $ "\t" ++ show (MetaTyVarTC mtv) ++ " :: " ++ show t) -- error $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t ++ " wasn't a tau!"
         else putDocLn (text $ "\t" ++ show (MetaTyVarTC mtv) ++ " :: " ++ show t)
    putDocLn $ (outLn "vvvv contextBindings:====================")
    putDocLn $ (dullyellow $ vcat $ map (text . show) (Map.toList $ contextBindings ctx_il))
-}

dumpAllPrimitives = do
  mapM_ dumpPrimitive (Map.toList gFosterPrimOpsTable)
 where
    dumpPrimitive :: (String, (TypeAST, FosterPrim TypeAST)) -> IO ()
    dumpPrimitive (name, ((FnTypeAST args ret fx _ _), _primop)) = do
      let allNames = "abcdefghijklmnop"
      let namesArgs = [(text (name:[]) , arg) | (name, arg) <- zip allNames args]
      let textid str = if Char.isAlphaNum (head str)
                               then         text str
                               else parens (text str)
      putDocLn $ (fill 20 $ textid name)
                 <> text " = {"
                     <+> hsep [fill 12 (name <+> text ":" <+> pretty arg) <+> text "=>"
                              | (name, arg) <- namesArgs]
                     <+> fill 23 (text "prim" <+> text name <+> hsep (map fst namesArgs))
                 <+> text "}; // :: " <> pretty ret <+> text "; fx=" <> pretty fx

    dumpPrimitive (name, (_ty, _primop)) = error $ "Can't dump primitive " ++ name ++ " yet."

