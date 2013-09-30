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
import qualified Data.Graph as Graph(SCC, flattenSCC, stronglyConnComp)
import Data.Map(Map)
import Data.Set(Set)

import qualified Data.Char as Char(isAlphaNum)
import Data.IORef(IORef, newIORef, readIORef)
import Data.Traversable(mapM)
import Prelude hiding (mapM)
import Control.Monad.State(forM, when, forM_, evalStateT, gets,
                           liftIO, liftM, liftM2)

import Foster.Base
import Foster.Config
import Foster.CFG
import Foster.CFGOptimization
import Foster.Fepb.WholeProgram(WholeProgram)
import Foster.ProtobufFE(parseWholeProgram)
import Foster.ProtobufIL(dumpILProgramToProtobuf)
import Foster.ExprAST
import Foster.TypeAST
import Foster.ParsedType
import Foster.PrettyExprAST()
import Foster.AnnExpr(AnnExpr, AnnExpr(E_AnnFn))
import Foster.AnnExprIL(AIExpr(AILetFuns, AICall, E_AIVar), fnOf, collectIntConstraints)
import Foster.TypeIL(TypeIL(TupleTypeIL, FnTypeIL), ilOf)
import Foster.ILExpr(ILProgram, showILProgramStructure, prepForCodegen)
import Foster.KNExpr(KNExpr', kNormalizeModule, knLoopHeaders, knSinkBlocks, knInline, knSize, renderKN)
import Foster.Typecheck
import Foster.Context
import Foster.CloConv(closureConvertAndLift, renderCC, CCBody(..))
import Foster.Monomo
import Foster.MonoType
import Foster.KSmallstep
import Foster.MainCtorHelpers
import Foster.ConvertExprAST
import Foster.MainOpts

import Foster.Output
import Text.PrettyPrint.ANSI.Leijen
import Criterion.Measurement(time, secs)

-----------------------------------------------------------------------
-- TODO shouldn't claim successful typechecks until we reach AnnExprIL.

pair2binding (nm, ty, mcid) = TermVarBinding nm (TypedId ty (GlobalSymbol nm), mcid)

-- Every function in the SCC should typecheck against the input context,
-- and the resulting context should include the computed types of each
-- function in the SCC.
typecheckFnSCC :: Bool -> Bool
               -> Graph.SCC (FnAST TypeAST)  ->   (Context TypeAST, TcEnv)
               -> IO ([OutputOr (AnnExpr Sigma)], (Context TypeAST, TcEnv))
typecheckFnSCC showASTs showAnnExprs scc (ctx, tcenv) = do
    let fns = Graph.flattenSCC scc

    -- Generate a binding (for functions without user-provided declarations)
    -- before doing any typechecking, so that if a function fails to typecheck,
    -- we'll have the best binding on hand to use for subsequent typechecking.
    let genBinding fn = do
        OK binding <-
            case termVarLookup (fnAstName fn) (contextBindings ctx) of
                Nothing  -> do unTc tcenv $ bindingForFnAST fn
                Just cxb -> do return (OK $ TermVarBinding (fnAstName fn) cxb)
        return binding

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
                                   [bindingForAnnFn f |(E_AnnFn f) <- goodexprs]

    if null errsAndASTs
     then return $ (,) (map OK goodexprs) (newctx, tcenv)
     else return $ (,) [Errors [text $ "not all functions type checked in SCC: "
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
                    when showASTs     $ (putDocLn $ showStructure ast)
                    when showAnnExprs $ (putDocLn $ showStructure e)
                Errors errs -> do
                    putDocLn $ showStructure ast
                    putDocLn $ red $ text "Typecheck error: "
                    forM_ errs putDocLn
                    putDocP line

        bindingForAnnFn :: Fn () (AnnExpr TypeAST) TypeAST -> ContextBinding TypeAST
        bindingForAnnFn f = TermVarBinding (identPrefix $ fnIdent f) (fnVar f, Nothing)

        -- Start with the most specific binding possible (i.e. sigma, not tau).
        -- Otherwise, if we blindly used a meta type variable, we'd be unable
        -- to type check a recursive & polymorphic function.
        bindingForFnAST :: (FnAST TypeAST) -> Tc (ContextBinding TypeAST)
        bindingForFnAST f = do t <- fnTypeTemplate f
                               return $ pair2binding (fnAstName f, t, Nothing)

        typeTemplateSigma :: Maybe Sigma -> String -> Tc Sigma
        typeTemplateSigma Nothing    name = newTcUnificationVarSigma name
        typeTemplateSigma (Just ty) _name = return ty

        annVarTemplate :: TypedId Sigma -> Tc Sigma
        annVarTemplate v = typeTemplateSigma (Just $ tidType v) (show $ tidIdent v)

        fnTypeTemplate :: (FnAST TypeAST) -> Tc TypeAST
        fnTypeTemplate f = do
          retTy  <- newTcUnificationVarSigma ("ret type for " ++ (T.unpack $ fnAstName f))
          argTys <- mapM annVarTemplate (fnFormals f)
          let procOrFunc = if fnWasToplevel f then FT_Proc else FT_Func
          let fnTy = FnTypeAST argTys retTy FastCC procOrFunc
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
    let primBindings = computeContextBindings' primitiveDecls
    let (nullCtors, nonNullCtors) = splitCtorTypes (concatMap extractCtorTypes dts)
    let declBindings = computeContextBindings' (moduleASTdecls modast) ++
                       computeContextBindings nonNullCtors
    let nullCtorBindings = computeContextBindings nullCtors
    putDocLn $ (outLn "vvvv declBindings:====================")
    putDocLn $ (dullyellow (vcat $ map (text . show) declBindings))

    let ctx0 = mkContext declBindings nullCtorBindings primBindings dts
    ctxErrsOrOK <- unTc tcenv0 (tcContext ctx0)

    case (detectDuplicates (map fnAstName fns), ctxErrsOrOK) of
      ([], OK _) -> do
        -- declBindings includes datatype constructors and some (?) functions.
        let callGraphList = buildCallGraphList fns (Set.fromList $ map fnAstName fns)
        let sortedFns = Graph.stronglyConnComp callGraphList -- :: [SCC FnAST]
        when verboseMode $ do
                putStrLn $ "Function SCC list : " ++
                 (unlines $ map show [(name, frees) | (_, name, frees) <- callGraphList])
        let showASTs     = verboseMode
        let showAnnExprs = verboseMode
        (annFnSCCs, (ctx, tcenv)) <- mapFoldM' sortedFns (ctx0, tcenv0)
                                          (typecheckFnSCC showASTs showAnnExprs)
        unTc tcenv (convertTypeILofAST modast ctx annFnSCCs)
      ([], Errors os) -> return (Errors os)
      (dups, _) -> return (Errors [text $ "Unable to check module due to "
                                        ++ "duplicate bindings: " ++ show dups])
 where
   mkContext declBindings nullCtorBnds primBindings datatypes =
     Context declBindsMap nullCtorsMap primBindsMap verboseMode globalvars tyvarsMap [] ctorinfo dtypes
       where globalvars   = declBindings ++ primBindings
             ctorinfo     = getCtorInfo  datatypes
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
     let boundTyVarFor (TypeFormalAST name _kind) = TyVarAST $ BoundTyVar name in
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
     where nmCTy dc@(DataCtor name tyformals types _range) =
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

   convertTypeILofAST :: ModuleAST FnAST TypeAST
                      -> Context TypeAST
                      -> [[OutputOr (AnnExpr TypeAST)]]
                      -> Tc (Context TypeIL, ModuleIL AIExpr TypeIL)
   convertTypeILofAST mAST ctx_ast oo_annfns = do
     mapM_ (tcInject collectIntConstraints) (concat oo_annfns)
     tcApplyIntConstraints

     ctx_il    <- liftContextM   (ilOf ctx_ast) ctx_ast
     decls     <- mapM (convertDecl (ilOf ctx_ast)) (externalModuleDecls mAST)
     primtypes <- mapM (convertDataTypeAST ctx_ast) (moduleASTprimTypes mAST)
     datatypes <- mapM (convertDataTypeAST ctx_ast) (moduleASTdataTypes mAST)
     let unfuns fns -- :: [[OutputOr (AnnExpr TypeAST)]] -> [[OutputOr (Fn (AnnExpr TypeAST) TypeAST)]]
                    = map (map (fmapOO unFunAnn)) fns
     -- Set fnIsRec flag on top-level functions.
     let tci oof -- :: OutputOr (Fn (AnnExpr TypeAST) TypeAST) -> Tc (Fn AIExpr TypeIL)
               = tcInject (fnOf ctx_ast) oof
     let tcis fns = mapM tci fns
     aiFns     <- mapM tcis (unfuns oo_annfns)
     let q = buildExprSCC aiFns
     let m = ModuleIL q decls datatypes primtypes
                                                  (moduleASTsourceLines mAST)
     return (ctx_il, m)
       where
        buildExprSCC :: [[Fn () AIExpr TypeIL]] -> AIExpr
        buildExprSCC [] = error "Main.hs: Can't build SCC of no functions!"
        buildExprSCC es = let call_of_main = AICall unit
                                              (E_AIVar (TypedId mainty (GlobalSymbol $ T.pack "main")))
                                              []
                              unit   = TupleTypeIL []
                              mainty = FnTypeIL [unit] unit FastCC FT_Proc
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

        liftContextM :: (Monad m, Show t1, Show t2)
                     => (t1 -> m t2) -> Context t1 -> m (Context t2)
        liftContextM f (Context cb nb pb vb gb tyvars tybinds ctortypeast dtinfo) = do
          cb' <-mmapM (liftCXB f) cb
          nb' <- mapM (liftCXB f) nb
          pb' <- mapM (liftCXB f) pb
          gb' <- mapM (liftBinding f) gb
          tyvars' <- mmapM f tyvars
          return $ Context cb' nb' pb' vb gb' tyvars' tybinds ctortypeast dtinfo

        liftTID :: Monad m => (t1 -> m t2) -> TypedId t1 -> m (TypedId t2)
        liftTID f (TypedId t i) = do t2 <- f t ; return $ TypedId t2 i

        liftCXB :: Monad m => (t1 -> m t2) -> CtxBound t1 -> m (CtxBound t2)
        liftCXB f (tid, mb_ci) = do tid' <- liftTID f tid; return (tid' , mb_ci)

        mmapM :: (Monad m, Ord k) => (a -> m b) -> Map k a -> m (Map k b)
        mmapM f ka = do
          kbl <- mapM (\(k, a) -> do b <- f a ; return (k, b)) (Map.toList ka)
          return $ Map.fromList kbl

        -- Wrinkle: need to extend the context used for checking ctors!
        convertDataTypeAST :: Context TypeAST ->
                              DataType TypeAST -> Tc (DataType TypeIL)
        convertDataTypeAST ctx (DataType dtName tyformals ctors range) = do
          -- f :: TypeAST -> Tc TypeIL
          let f = ilOf (extendTyCtx ctx $ map convertTyFormal tyformals)
          cts <- mapM (convertDataCtor f) ctors
          return $ DataType dtName tyformals cts range
            where
              convertDataCtor f (DataCtor dataCtorName tyformals types range) = do
                tys <- mapM f types
                return $ DataCtor dataCtorName tyformals tys range

dieOnError :: OutputOr t -> Compiled t
dieOnError (OK     e) = return e
dieOnError (Errors errs) = liftIO $ do
    putDocLn (red $ text "Unable to type check input module:")
    forM_ errs putDocLn
    error "compilation failed"

isTau :: TypeAST -> Bool
isTau (ForAllAST {}) = False
isTau t = all isTau (childrenOf t)

-----------------------------------------------------------------------

main = do
  args <- getArgs
  case args of
    (infile : outfile : rest) -> do
       protobuf <- L.readFile infile
       flagVals <- parseOpts rest
       case messageGet protobuf of
        Left msg -> error $ "Failed to parse protocol buffer.\n" ++ msg
        Right (pb_program, _) ->
          runCompiler pb_program flagVals outfile

    rest -> do
      flagVals <- parseOpts rest
      if getDumpPrimitives flagVals
        then do
           mapM_ dumpPrimitive (Map.toList gFosterPrimOpsTable)
        else do
           self <- getProgName
           return (error $ "Usage: " ++ self
                   ++ " path/to/infile.pb path/to/outfile.pb")


runCompiler pb_program flagVals outfile = do
   uniqref <- newIORef 1
   varlist <- newIORef []
   icmap   <- newIORef Map.empty
   let tcenv = TcEnv {       tcEnvUniqs = uniqref,
                      tcUnificationVars = varlist,
                              tcParents = [],
                   tcMetaIntConstraints = icmap }
   (il_time, ilprog) <- time $ evalStateT (compile pb_program tcenv)
                    CompilerContext {
                           ccVerbose  = getVerboseFlag flagVals
                         , ccFlagVals = flagVals
                         , ccDumpFns  = getDumpFns flagVals
                         , ccInline   = getInlining flagVals
                         , ccUniqRef  = uniqref
                    }
   (pb_time, _) <- time $ dumpILProgramToProtobuf ilprog outfile
   putStrLn $ "compilation time: " ++ secs il_time
   putStrLn $ "protobufout time: " ++ secs pb_time

compile :: WholeProgram -> TcEnv -> Compiled ILProgram
compile pb_program tcenv =
    (return $ parseWholeProgram pb_program)
     >>= mergeModules -- temporary hack
     >>= desugarParsedModule tcenv
     >>= typecheckSourceModule tcenv
     >>= (uncurry lowerModule)

mergeModules :: WholeProgramAST FnAST TypeP
              -> Compiled (ModuleAST FnAST TypeP)
mergeModules (WholeProgramAST modules) = do
  liftIO $ putDocLn (pretty (head modules))
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
          MetaPlaceholder desc -> do newTcUnificationVarTau desc

typecheckSourceModule :: TcEnv ->  ModuleAST FnAST TypeAST
                      -> Compiled (ModuleIL AIExpr TypeIL, Context TypeIL)
typecheckSourceModule tcenv sm = do
    verboseMode <- gets ccVerbose
    liftIO $ putStrLn $ "Verbose mode: " ++ show verboseMode
    (ctx_il, ai_mod) <- (liftIO $ typecheckModule verboseMode sm tcenv)
                      >>= dieOnError
    showGeneratedMetaTypeVariables (tcUnificationVars tcenv) ctx_il
    return (ai_mod, ctx_il)

lowerModule :: ModuleIL AIExpr TypeIL
            -> Context TypeIL
            -> Compiled ILProgram
lowerModule ai_mod ctx_il = do
     inline   <- gets ccInline
     flags    <- gets ccFlagVals
     let donate = getInliningDonate flags
     let insize = getInliningSize   flags
     let ctoropt = getCtorOpt       flags

     kmod <- kNormalizeModule ai_mod ctx_il ctoropt
     monomod0 <- monomorphize   kmod
     monomod2 <- knLoopHeaders  monomod0
     monomod4 <- (if inline then knInline insize donate else return) monomod2
     monomod  <- knSinkBlocks   monomod4

     whenDumpIR "kn" $ do
         putDocLn (outLn $ "vvvv k-normalized :====================")
         putDocLn (showStructure (moduleILbody kmod))
         _ <- liftIO $ renderKN kmod True
         return ()

     whenDumpIR "mono" $ do
         putDocLn $ (outLn "/// Monomorphized program =============")
         putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod0)))
         _ <- liftIO $ renderKN monomod0 True
         putDocLn $ (outLn "^^^ ===================================")

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

     (ilprog, prealloc) <- prepForCodegen ccmod  constraints
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
     liftIO $ putDocLn $ (text $ "/// Inlined size: " ++ show (knSize (moduleILbody monomod4)))

     maybeInterpretKNormalModule kmod

     return ilprog

  where
    cfgModule :: ModuleIL (KNExpr' RecStatus MonoType) MonoType -> Compiled (ModuleIL CFBody MonoType)
    cfgModule kmod = do
        uniqref <- gets ccUniqRef
        cfgBody <- liftIO $ computeCFGs uniqref (moduleILbody kmod)
        cfgBody' <- optimizeCFGs cfgBody
        return $ kmod { moduleILbody = cfgBody' }

    closureConvert cfgmod = do
        uniqref <- gets ccUniqRef
        liftIO $ do
            let datatypes = moduleILprimTypes cfgmod ++
                            moduleILdataTypes cfgmod
            let dataSigs = dataTypeSigs datatypes
            u0 <- readIORef uniqref
            let tmBindingId (TermVarBinding _ (tid, _)) = tidIdent tid
                globals = map tmBindingId (globalBindings ctx_il)
            return $ closureConvertAndLift dataSigs globals u0 cfgmod

    maybeInterpretKNormalModule kmod = do
        flagVals <- gets ccFlagVals
        case getInterpretFlag flagVals of
            Nothing -> return ()
            Just tmpDir -> do
                let cmdLineArgs = getProgArgs flagVals
                _unused <- liftIO $ interpretKNormalMod kmod tmpDir cmdLineArgs
                return ()

showGeneratedMetaTypeVariables :: (Show ty) =>
                               IORef [MetaTyVar TypeAST] -> Context ty -> Compiled ()
showGeneratedMetaTypeVariables varlist ctx_il =
  ccWhen ccVerbose $ do
    metaTyVars <- readIORef varlist
    putDocLn $ (outLn $ "generated " ++ (show $ length metaTyVars) ++ " meta type variables:")
    forM_ metaTyVars $ \mtv -> do
        t <- readIORef (mtvRef mtv)
        let wasTau = fmap isTau t /= Just False
        if mtvConstraint mtv == MTVTau && not wasTau
         then putDocLn (text $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t) -- error $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t ++ " wasn't a tau!"
         else putDocLn (text $ "\t" ++ show (MetaTyVar mtv) ++ " :: " ++ show t)
    putDocLn $ (outLn "vvvv contextBindings:====================")
    putDocLn $ (dullyellow $ vcat $ map (text . show) (Map.toList $ contextBindings ctx_il))

dumpPrimitive (name, ((FnTypeAST args ret _ _), _primop)) = do
  let allNames = "abcdefghijklmnop"
  let namesArgs = [(text (name:[]) , arg) | (name, arg) <- zip allNames args]
  let textid str = if Char.isAlphaNum (head str)
                           then         text str
                           else parens (text str)
  putDocLn $ (fill 20 $ textid name)
             <> text " = {"
                 <+> hsep [fill 10 (name <+> text ":" <+> pretty arg) <+> text "=>"
                          | (name, arg) <- namesArgs]
                 <+> text "prim" <+> text name <+> hsep (map fst namesArgs)
             <+> text "}; // :: " <> pretty ret

dumpPrimitive (name, (_ty, _primop)) = error $ "Can't dump primitive " ++ name ++ " yet."

whenDumpIR :: String -> IO () -> Compiled ()
whenDumpIR ir action = do flags <- gets ccFlagVals
                          let cond = getDumpIRFlag ir flags
                          liftIO $ when cond action
