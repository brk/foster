-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Main (main) where

import Text.ProtocolBuffers(messageGet)

import System.Environment(getArgs,getProgName)

import qualified Data.ByteString.Lazy as L(readFile)
import qualified Data.Text as T
import qualified Data.Map as Map(fromList, toList, empty)
import qualified Data.Set as Set(filter, toList, fromList, notMember, intersection)
import qualified Data.Graph as Graph(SCC, flattenSCC, stronglyConnComp, stronglyConnCompR)
import Data.Map(Map)
import Data.Set(Set)

import qualified Data.Char as Char(isAlphaNum)
import Data.IORef(IORef, newIORef, readIORef, writeIORef)
import Data.Traversable(mapM)
import Prelude hiding (mapM)
import Control.Monad.State(forM, when, forM_, evalStateT, gets,
                           liftIO, liftM, liftM2)
import Control.Monad.Error(runErrorT)
import System.Exit(exitFailure)

import Foster.Base
import Foster.Config
import Foster.CFG
import Foster.CFGOptimization
import Foster.ProtobufFE(parseWholeProgram)
import Foster.ProtobufIL(dumpILProgramToProtobuf)
import Foster.TypeTC
import Foster.ExprAST
import Foster.TypeAST
import Foster.ParsedType
import Foster.PrettyExprAST()
import Foster.AnnExpr(AnnExpr, AnnExpr(E_AnnFn))
import Foster.AnnExprIL(AIExpr(AILetFuns, AICall, E_AIVar), fnOf, ilOf,
                     collectIntConstraints, TypeIL(FnTypeIL),  unitTypeIL,
                     convertDataTypeTC)
import Foster.ILExpr(ILProgram, showILProgramStructure, prepForCodegen)
import Foster.KNExpr(KNExpr', kNormalizeModule, knLoopHeaders, knSinkBlocks,
                     knInline, kNormalize, knSize, renderKN)
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

import Text.Printf(printf)
import Foster.Output
import Text.PrettyPrint.ANSI.Leijen((<+>), (<>), (<$>), pretty, text, line, hsep,
                                    fill, parens, vcat, list, red, dullyellow)
import Criterion.Measurement(time, secs)

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
            t <- fnTypeTemplate ctx f
            return $ pair2binding (fnAstName f, t, Nothing)

        fnTypeTemplate :: Context TypeTC -> FnAST TypeAST -> Tc TypeTC
        fnTypeTemplate ctx f = tcType ctx fnTyAST
          where
           fnTyAST0 = FnTypeAST (map tidType $ fnFormals f)
                                (MetaPlaceholderAST MTVSigma ("ret type for " ++ (T.unpack $ fnAstName f)))
                                FastCC
                                (if fnWasToplevel f then FT_Proc else FT_Func)
           fnTyAST = case fnTyFormals f of
                         [] -> fnTyAST0
                         tyformals -> ForAllAST (map convertTyFormal tyformals) fnTyAST0

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
typecheckModule :: Bool -> Bool
                -> ModuleAST FnAST TypeAST
                -> TcEnv
                -> IO (OutputOr (Context TypeIL, ModuleIL AIExpr TypeIL))
typecheckModule verboseMode pauseOnErrors modast tcenv0 = do
    when verboseMode $ do
        putDocLn $ text "module AST decls:" <$> pretty (moduleASTdecls modast)
    let dts = moduleASTprimTypes modast ++ moduleASTdataTypes modast
    let fns = moduleASTfunctions modast
    let primBindings = computeContextBindings' primitiveDecls
    let allCtorTypes = concatMap extractCtorTypes dts
    let (nullCtors, nonNullCtors) = splitCtorTypes allCtorTypes
    let declBindings = computeContextBindings' (moduleASTdecls modast) ++
                       computeContextBindings nonNullCtors
    let nullCtorBindings = computeContextBindings nullCtors

    when verboseMode $ do
        putDocLn $ (outLn "vvvv declBindings:====================")
        putDocLn $ (dullyellow (vcat $ map (text . show) declBindings))

    case detectDuplicates $ map fnAstName fns of
      [] -> do
        let declCG = buildCallGraphList' declBindings (Set.fromList $ map (\(TermVarBinding nm _) -> nm) declBindings)
        let globalids = map (\(TermVarBinding _ (tid, _)) -> tidIdent tid) $ declBindings ++ primBindings
        let declBindings' = topoSortBindingSCC $ Graph.stronglyConnCompR declCG -- :: [ [ContextBinding TypeAST] ]
        let primOpMap = Map.fromList [(T.pack nm, prim)
                            | (nm, (_, prim)) <- Map.toList gFosterPrimOpsTable]

        ctxErrsOrOK <- unTc tcenv0 $ do
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
            when verboseMode $ do
                    putStrLn $ "Function SCC list : " ++
                     (unlines $ map show [(name, frees) | (_, name, frees) <- callGraphList])
            let showASTs     = verboseMode
            let showAnnExprs = verboseMode
            (annFnSCCs, (ctx, tcenv)) <- mapFoldM' sortedFns (ctxTC, tcenv0)
                                              (typecheckFnSCC showASTs showAnnExprs pauseOnErrors)
            unTc tcenv (convertTypeILofAST modast ctx annFnSCCs)
          Errors os -> return (Errors os)
      dups -> return (Errors [text $ "Unable to check module due to "
                                  ++ "duplicate bindings: " ++ show dups])
 where
   mkContext :: [ContextBinding t] -> [ContextBinding t]
             -> [ContextBinding t] -> (Map T.Text (FosterPrim t)) -> [Ident] -> [DataType t] -> Context t
   mkContext declBindings nullCtorBnds primBindings primOpMap globalvars datatypes =
     Context declBindsMap nullCtorsMap primBindsMap primOpMap globalvars tyvarsMap [] ctorinfo dtypes
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
   typeOfDataType :: DataType TypeAST -> CtorName -> TypeAST
   typeOfDataType dt _ctorName =
     let boundTyVarFor (TypeFormal name sr _kind) = TyVarAST $ BoundTyVar name sr in
     TyConAppAST (typeFormalName $ dataTypeName dt) (map boundTyVarFor $ dataTypeTyFormals dt)

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
                         where dtType = typeOfDataType dt name
                               cid    = ctorId (typeFormalName $ dataTypeName dt) dc

   -- Nullary constructors are constants; non-nullary ctors are functions.
   ctorTypeAST [] dtType [] = Left dtType
   ctorTypeAST [] dtType ctorArgTypes =
                            Right $ FnTypeAST ctorArgTypes dtType FastCC FT_Proc

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
                      -> Tc (Context TypeIL, ModuleIL AIExpr TypeIL)
   convertTypeILofAST mAST ctx_tc oo_annfns = do
     mapM_ (tcInject collectIntConstraints) (concat oo_annfns)
     tcApplyIntConstraints

     -- We've already typechecked the functions, so no need to re-process them...
     mTC <- convertModule (tcType ctx_tc) $ mAST { moduleASTfunctions = [] }
     ctx_il    <- liftContextM   (ilOf ctx_tc) ctx_tc
     decls     <- mapM (convertDecl (ilOf ctx_tc)) (externalModuleDecls mTC)
     primtypes <- mapM (convertDataTypeTC ctx_tc) (moduleASTprimTypes mTC)
     datatypes <- mapM (convertDataTypeTC ctx_tc) (moduleASTdataTypes mTC)
     let unfuns fns -- :: [[OutputOr (AnnExpr TypeAST)]] -> [[OutputOr (Fn (AnnExpr TypeAST) TypeAST)]]
                    = map (map (fmapOO unFunAnn)) fns
     -- Set fnIsRec flag on top-level functions.
     let tci oof -- :: OutputOr (Fn (AnnExpr TypeAST) TypeAST) -> Tc (Fn AIExpr TypeIL)
               = tcInject (fnOf ctx_tc) oof
     let tcis fns = mapM tci fns
     aiFns     <- mapM tcis (unfuns oo_annfns)
     let q = buildExprSCC aiFns
     let m = ModuleIL q decls datatypes primtypes (moduleASTsourceLines mAST)
     return (ctx_il, m)
       where
        buildExprSCC :: [[Fn () AIExpr TypeIL]] -> AIExpr
        buildExprSCC [] = error "Main.hs: Can't build SCC of no functions!"
        buildExprSCC es = let call_of_main = AICall unitTypeIL
                                              (E_AIVar (TypedId mainty (GlobalSymbol $ T.pack "main")))
                                              []
                              mainty = FnTypeIL [unitTypeIL] unitTypeIL FastCC FT_Proc
                          in foldr build call_of_main es
         where build :: [Fn () AIExpr TypeIL] -> AIExpr -> AIExpr
               build es body = case es of
                    [] -> body
                    _  -> AILetFuns (map fnIdent es) es body

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

readAndParseProtobuf infile = do
  protobuf <- L.readFile infile
  case messageGet protobuf of
    Left msg -> error $ "Failed to parse protocol buffer.\n" ++ msg
    Right (pb_program, _) -> return pb_program

main = do
  -- When we upgrade to criterion 1.0, we must call initializeTime here...
  args <- getArgs
  case args of
    (infile : outfile : rest) -> do
       flagVals <- parseOpts rest
       (pi_time, pb_program) <- ioTime $ readAndParseProtobuf infile
       let wholeprog = parseWholeProgram pb_program (getStandaloneFlag flagVals)
       if getFmtOnlyFlag flagVals
         then do
           let WholeProgramAST modules = wholeprog
           liftIO $ putDocLn (pretty (head modules))
         else
           runCompiler pi_time wholeprog flagVals outfile

    rest -> do
      flagVals <- parseOpts rest
      if getDumpPrimitives flagVals
        then dumpAllPrimitives
        else do
           self <- getProgName
           return (error $ "Usage: " ++ self
                   ++ " path/to/infile.pb path/to/outfile.pb")


runCompiler pi_time wholeprog flagVals outfile = do
   uniqref <- newIORef 2
   varlist <- newIORef []
   subcnst <- newIORef []
   icmap   <- newIORef Map.empty
   smtStatsRef <- newIORef (0, [])
   cfgSizesRef <- newIORef []

   let tcenv = TcEnv {       tcEnvUniqs = uniqref,
                      tcUnificationVars = varlist,
                              tcParents = [],
                   tcMetaIntConstraints = icmap,
               tcSubsumptionConstraints = subcnst,
                tcUseOptimizedCtorReprs = getCtorOpt flagVals,
                          tcVerboseMode = getVerboseFlag flagVals }
   (nc_time, mb_errs) <- time $ runErrorT $ evalStateT (compile wholeprog tcenv)
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
       putStrLn $ "compilation time: " ++ secs (nc_time)
       putDocLn $ red $ text "Compilation failed: "
       forM_ errs putDocLn
       putDocP line
       exitFailure

     Right (RWT in_time sr_time cp_time sc_time ilprog) -> do
       (pb_time, _) <- time $ dumpILProgramToProtobuf ilprog outfile
       (nqueries, querytime) <- readIORef smtStatsRef
       let ct_time = (nc_time - (cp_time + in_time + sc_time))
       let pct f1 f2 = (100.0 * f1) / f2
       let fmt_pct time = let p = pct time nc_time
                              n = if p < 10.0 then 2 else if p < 100.0 then 1 else 0
                              padding = fill n (text "") in
                          padding <> parens (text (printf "%.1f" p) <> text "%")
       let fmt str time = text str <+> (fill 11 $ text $ secs time) <+> fmt_pct time
       let pairwise f = \(x,y) -> (f x, f (x + y))
       putDocLn $ vcat $ [text "                                            (initial query time, overall query time)"
                         ,text "# SMT queries:" <+> pretty nqueries <+> text "taking" <+> pretty (map (pairwise secs) querytime)
                         ,fmt "static-chk  time:" sc_time
                         ,fmt "inlining    time:" in_time
                         ,fmt "shrinking   time:" sr_time
                         ,fmt "codegenprep time:" cp_time
                         ,fmt "'other'     time:" ct_time
                         ,fmt "sum elapsed time:" nc_time
                         ,text ""
                         ,fmt "protobuf-in time:" pi_time
                         ,fmt "protobufout time:" pb_time
                         ,text "overall wall-clock time:" <+> text (secs $ pi_time + pb_time + nc_time)
                         ]

data ResultWithTimings = RWT Double Double Double Double ILProgram

compile :: WholeProgramAST FnAST TypeP -> TcEnv -> Compiled ResultWithTimings
compile wholeprog tcenv = do
    (return wholeprog)
     >>= mergeModules -- temporary hack
     >>= desugarParsedModule tcenv
     >>= typecheckSourceModule tcenv
     >>= (uncurry lowerModule)

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
          PrimIntP         size  -> return $ PrimIntAST         size
          TyConAppP "Word"    [] -> return $ PrimIntAST         (IWord 0)
          TyConAppP "WordX2"  [] -> return $ PrimIntAST         (IWord 1)
          TyConAppP "Int64"   [] -> return $ PrimIntAST         I64
          TyConAppP "Int32"   [] -> return $ PrimIntAST         I32
          TyConAppP "Int8"    [] -> return $ PrimIntAST         I8
          TyConAppP "Bool"    [] -> return $ PrimIntAST         I1
          TyConAppP "Float64" [] -> return $ PrimFloat64AST
          TyConAppP "Array"  [t] -> liftM  ArrayTypeAST            (q t)
          TyConAppP "Ref"    [t] -> liftM  RefTypeAST              (q t)
          TyConAppP "Coro" [o,i] -> liftM2 CoroTypeAST       (q o) (q i)
          TyConAppP    tc types  -> liftM (TyConAppAST tc) (mapM q types)
          TupleTypeP      types  -> liftM  TupleTypeAST    (mapM q types)
          RefTypeP       t       -> liftM  RefTypeAST              (q t)
          ArrayTypeP     t       -> liftM  ArrayTypeAST            (q t)
          CoroTypeP    s t       -> liftM2 CoroTypeAST       (q s) (q t)
          ForAllP    tvs t       -> liftM (ForAllAST $ map convertTyFormal tvs) (q t)
          TyVarP     tv          -> do return $ TyVarAST tv
          FnTypeP      s t cc cs -> do s' <- mapM q s
                                       t' <- q t
                                       return $ FnTypeAST      s' t' cc cs
          RefinedTypeP nm t e -> do t' <- q t
                                    e' <- convertExprAST q e
                                    return $ RefinedTypeAST nm t' e'
          MetaPlaceholder desc -> return $ MetaPlaceholderAST MTVTau desc

typecheckSourceModule :: TcEnv ->  ModuleAST FnAST TypeAST
                      -> Compiled (ModuleIL AIExpr TypeIL, Context TypeIL)
typecheckSourceModule tcenv sm = do
    verboseMode <- gets ccVerbose
    flags <- gets ccFlagVals
    let pauseOnErrors = getInteractiveFlag flags
    (ctx_il, ai_mod) <- (liftIO $ typecheckModule verboseMode pauseOnErrors sm tcenv)
                      >>= dieOnError
    showGeneratedMetaTypeVariables (tcUnificationVars tcenv) ctx_il
    return (ai_mod, ctx_il)

lowerModule :: ModuleIL AIExpr TypeIL
            -> Context TypeIL
            -> Compiled ResultWithTimings
lowerModule ai_mod ctx_il = do
     inline   <- gets ccInline
     flags    <- gets ccFlagVals
     let donate = getInliningDonate flags
     let insize = getInliningSize   flags
     let dtypes = moduleILdataTypes ai_mod ++ moduleILprimTypes ai_mod
     let dtypeMap = Map.fromList [(typeFormalName (dataTypeName dt), dt) | dt <- dtypes]

     let knorm = kNormalize dtypeMap -- For normalizing expressions in types.

     kmod <- kNormalizeModule ai_mod ctx_il dtypeMap

     whenDumpIR "kn" $ do
         putDocLn (outLn $ "vvvv k-normalized :====================")
         putDocLn (showStructure (moduleILbody kmod))
         _ <- liftIO $ renderKN kmod True
         return ()

     monomod0 <- monomorphize   kmod knorm

     whenDumpIR "mono" $ do
         putDocLn $ (outLn "/// Monomorphized program =============")
         putDocLn (showStructure (moduleILbody monomod0))
         putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod0)))
         _ <- liftIO $ renderKN monomod0 True
         putDocLn $ (outLn "^^^ ===================================")

     (sc_time, _) <- ioTime $ runStaticChecks monomod0
     monomod2 <- knLoopHeaders  monomod0

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

         when inline $ do
           putDocLn $ (outLn "/// Inlined       program =============")
           putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod4)))
           _ <- liftIO $ renderKN monomod4 True
           putDocLn $ (outLn "^^^ ===================================")

     whenDumpIR "mono-sunk" $ do
         putDocLn $ (outLn "/// Block-sunk program =============")
         _ <- liftIO $ renderKN monomod  True
         putDocLn $ (outLn "^^^ ===================================")

     cfgmod   <- cfgModule      monomod
     let constraints = collectMayGCConstraints (moduleILbody cfgmod)
     whenDumpIR "may-gc" $ do
         liftIO $ putStrLn "\n MAY GC CONSTRAINTS ======================="
         liftIO $ putDocLn $ list (map pretty $ (Map.toList constraints))
         liftIO $ putStrLn "\n/MAY GC CONSTRAINTS ======================="

     whenDumpIR "cfg" $ do
         putDocLn $ (outLn "/// CFG-ized program ==================")
         putDocP  $ pretty cfgmod
         putDocLn $ (outLn "^^^ ===================================")

     ccmod    <- closureConvert cfgmod
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

     return (RWT in_time mkn_time cp_time sc_time ilprog)

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

    closureConvert cfgmod = do
        uniqref <- gets ccUniqRef
        liftIO $ do
            let datatypes = moduleILprimTypes cfgmod ++
                            moduleILdataTypes cfgmod
            let dataSigs = dataTypeSigs datatypes
            u0 <- readIORef uniqref
            let globals = globalIdents ctx_il
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


dumpAllPrimitives = do
  mapM_ dumpPrimitive (Map.toList gFosterPrimOpsTable)
 where
    dumpPrimitive :: (String, (TypeAST, FosterPrim TypeAST)) -> IO ()
    dumpPrimitive (name, ((FnTypeAST args ret _ _), _primop)) = do
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
                 <+> text "}; // :: " <> pretty ret

    dumpPrimitive (name, (_ty, _primop)) = error $ "Can't dump primitive " ++ name ++ " yet."

