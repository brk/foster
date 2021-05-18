{-# LANGUAGE Strict #-}
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
import Data.Sequence(Seq)
import qualified Data.Sequence as Seq(empty, (><), fromList)
import Data.Either(partitionEithers)
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
import Foster.ProtobufFE(cb_parseWholeProgram)
import Foster.CapnpIL(dumpILProgramToCapnp)
import Foster.HashCache
import Foster.TypeTC
import Foster.ExprAST
import Foster.PrettyExprAST(IsQuietPlaceholder(..))
import Foster.TypeAST
import Foster.ParsedType
import Foster.AnnExpr(AnnExpr, AnnExpr(E_AnnFn, E_AnnVar, AnnCall, AnnLetFuns,
                      AnnLetVar))
import Foster.ILExpr(showILProgramStructure, prepForCodegen)
import Foster.KNExpr(kNormalizeModule, knLoopHeaders, knSinkBlocks,
                     knSize, renderKN,
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
import Foster.Infer(unify)
import Foster.SourceRange(SourceRange(..), SourceLines(SourceLines), rangeOf,
          showSourceRangeStr, appendSourceLines, highlightFirstLineDoc,
          prettyWithLineNumbers)

import Codec.CBOR.Term
import Codec.CBOR.Read (deserialiseFromBytes)

import Text.Printf(printf) -- for toFixed
import Foster.Output
import Prettyprinter((<+>), pretty, line, hsep, fill, parens, vcat, Doc)

import qualified Criterion.Measurement as Criterion(initializeTime, secs)

{-
import qualified Criterion.Measurement as Criterion(getGCStats)
import GHC.Stats
import System.Mem
-}

pair2binding (nm, ty, mcid) = TermVarBinding nm (TypedId ty (GlobalSymbol nm NoRename), mcid)

data FnsOrExpr = AllFns   [FnAST TypeAST]
               | NonFn    T.Text (ExprAST TypeAST)

type Binding thing = (T.Text, thing)

typecheckSCC :: Bool -> Bool -> Bool -> TcEnv
             -> Graph.SCC (Binding (ExprAST TypeAST)) -> Context TypeTC
             -> IO ([OutputOr (Binding (AnnExpr SigmaTC))], Context TypeTC)
typecheckSCC showASTs showAnnExprs pauseOnErrors tcenv    scc ctx = do
     let exprs = Graph.flattenSCC scc
     case classify exprs of
       AllFns fns -> do
         typecheckFnSCC fns

       NonFn name expr -> do
         oo_bindann <- unTc tcenv $ typecheckNonFn name expr
         case oo_bindann of
           OK (binding, ann) ->
             return ( [OK (name, ann)] , prependContextBinding ctx binding )
           Errors os ->
             -- If typechecking fails, we don't bother extending the context.
             return ( [Errors os], ctx )


  where
    classify :: [(T.Text, ExprAST TypeAST)] -> FnsOrExpr
    classify things =
      let eith (nm, exp) =
            case exp of
              E_FnAST _ fn -> Left fn
              _            -> Right (nm, exp)
      in
      case partitionEithers (map eith things) of
        ([], [(nm, exp)]) -> NonFn nm exp
        (fns, [])         -> AllFns fns
        _ -> error $ "Main.hs: classify saw mixed fns/non fns in " ++ show things

    typecheckNonFn :: T.Text -> ExprAST TypeAST -> Tc (ContextBinding SigmaTC, AnnExpr SigmaTC)
    typecheckNonFn name expr = do
      ann <- case termVarLookup name (contextBindings ctx) of
                Just cxb -> do tcSigmaToplevel (TermVarBinding name cxb) ctx expr
                Nothing  -> do tcSigmaToplevelNonFn ctx expr
      return (TermVarBinding name (TypedId (typeOf ann) (GlobalSymbol name NoRename), Nothing), ann)

    -- Every function in the SCC should typecheck against the input context,
    -- and the resulting context should include the computed types of each
    -- function in the SCC.
    typecheckFnSCC :: [FnAST TypeAST]
                   -> IO ([OutputOr (Binding (AnnExpr SigmaTC))], Context TypeTC)
    typecheckFnSCC fns = do

        -- Generate a binding (for definitions without user-provided declarations)
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
            let name = fnAstName fn

            when False $ do
              putStrLn $ "typechecking " ++ T.unpack name ++ " with binding " ++ show binding

            varbind <- unTc tcenv $ do
                          ann <- tcSigmaToplevel binding extCtx ast
                          return (name, ann)

            -- We can't convert AnnExpr to AIExpr here because
            -- the output context is threaded through further type checking.
            return (varbind, (ast, binding))

        -- Dump full ASTs if requested, otherwise just type-incorrect ASTs.
        mapM_ (uncurry inspect) tcResults

        -- The extra bindings of an SCC are the ones generated from successfully
        -- type checked symbols, plus the initial guesses (involving type variables)
        -- for those symbols which could not be checked. This ensures that we don't
        -- undefined-symbol errors when checking subsequent SCCs.
        let (goodexprs, errsAndASTs) = split tcResults
        let newctx = prependContextBindings ctx $ (map bindingOf errsAndASTs) ++
                                      [bindingForAnnFn f | (_, E_AnnFn f) <- goodexprs]

        if null errsAndASTs
         then return (map OK goodexprs, newctx)
         else return ([Errors [string $ "not all functions type checked in SCC: "
                                      ++ show (map fnAstName fns)]], newctx)

       where
            bindingOf (_errs, (_ast, binding)) = binding

            split fnsAndASTs = (,) [thing       | (OK thing,    _ast) <- fnsAndASTs]
                                   [(errs, ast) | (Errors errs,  ast) <- fnsAndASTs]

            inspect :: OutputOr (Binding (AnnExpr TypeTC)) -> (ExprAST TypeAST, a) -> IO ()
            inspect typechecked (ast, _) =
                case typechecked of
                    OK (_, e) -> do
                        when showASTs     $ (putDocLn $ showStructure ast)
                        when showAnnExprs $ do
                            putStrLn $ "[[[[[["
                            putDocLn $ showStructure e
                            putStrLn $ "]]]]]]"
                    Errors errs -> do
                        --putDocLn $ showStructure ast
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

instance IsQuietPlaceholder TypeAST where
  isQuietPlaceholder _ = False
instance IsQuietPlaceholder TypeTC where
  isQuietPlaceholder _ = False

typecheckAndFoldContextBindings :: Context TypeTC ->
                                  [ContextBinding TypeAST] ->
                               Tc (Context TypeTC)
typecheckAndFoldContextBindings ctxTC0 bindings = do
  bindings' <- mapM (liftBinding (tcType ctxTC0)) bindings
  return $ prependContextBindings ctxTC0 bindings'

-- | Typechecking a module proceeds as follows:
-- |  #. Build separate binding lists for the globally-defined primitiveDecls
-- |     and the module's top-level (function) declarations.
-- |  #. Typecheck non-function definitions, in a minimal environment.
-- |  #. Build a (conservative) dependency graph on the module's top-level
-- |     declarations, yielding a list of SCCs of declarations.
-- |  #. Initialize the "real" environment with data and effect ctor functions.
-- |  #. Typecheck the SCCs bottom-up, propagating results as we go along.
-- |  #. Make sure that all unification variables have been properly eliminated,
-- |     or else we consider type checking to have failed
-- |     (no implicit instantiation at the moment!)
typecheckModule :: Bool -> Bool -> ([Flag], strings)
                -> ModuleExpr TypeAST
                -> TcEnv
                -> Compiled (OutputOr TCRESULT)
typecheckModule verboseMode pauseOnErrors flagvals modast tcenv0 = do
    liftIO $ when verboseMode $ do
        putDocLn $ text "module AST decls:" <$> prettyT (moduleASTdecls modast)
    let dts = moduleASTprimTypes modast ++ moduleASTdataTypes modast
    --let fns = moduleASTfunctions modast
    --let nonfns = moduleASTnonfndefs modast
    let defns = [(nm, e) | ToplevelDefn (nm, e) <- moduleASTitems modast]

    let primBindings = computeContextBindings' (primitiveDecls ++ primopDecls)
    let allCtorTypes = concatMap extractCtorTypes dts
    let (nullCtors, nonNullCtors) = splitCtorTypes allCtorTypes
    let declBindings = computeContextBindings' (moduleASTdecls modast) ++
                       computeContextBindings nonNullCtors ++
                       concatMap effectContextBindings (moduleASTeffects modast)
    let nullCtorBindings = computeContextBindings nullCtors

{-
    liftIO $ when verboseMode $ do
        putDocLn $ (outLn "vvvv declBindings:====================")
        putDocLn $ (dullyellow (vcat $ map prettyT declBindings))
-}

    rv <- case collectDuplicatesBy fst defns of
      [] -> do
        let declCG = buildCallGraphList' declBindings (Set.fromList $ map (\(TermVarBinding nm _) -> nm) declBindings)
        let globalids = map (\(TermVarBinding _ (tid, _)) -> tidIdent tid) $ declBindings ++ primBindings
        let declBindings' = topoSortBindingSCC $ Graph.stronglyConnCompR declCG -- :: [ [ContextBinding TypeAST] ]
        let primOpMap = Map.fromList [(nm, prim)
                            | (nm, (_, prim)) <- Map.toList gFosterPrimOpsTable]

        ctxErrsOrOK <- liftIO $ unTc tcenv0 $ do
                         let ctxAS1 = mkContext (computeContextBindings nonNullCtors)
                                         nullCtorBindings primBindings primOpMap
                                         (Seq.fromList globalids)
                                         (Seq.fromList dts)
                                         (Seq.fromList $ moduleASTeffects modast)
                         let ctxTC0 = mkContext [] [] [] Map.empty Seq.empty Seq.empty Seq.empty
                         ctxTC1 <- tcContext ctxTC0 ctxAS1
                         foldlM typecheckAndFoldContextBindings ctxTC1 declBindings'
        case ctxErrsOrOK of
          OK ctxTC -> do
              -- declBindings includes datatype constructors and some (?) functions.
              let callGraphList = buildCallGraphList defns (Set.fromList $ map fst defns)
              let sortedBindings = Graph.stronglyConnComp callGraphList -- :: [SCC (T.Text, ExprAST TypeAST)]
              liftIO $ when verboseMode $ do
                    putStrLn $ "Top-level SCC list : " ++
                      (unlines $ map show [(name, frees) | (_, name, frees) <- callGraphList])
              let showASTs     = verboseMode || getDumpIRFlag "ast" flagvals
              let showAnnExprs = verboseMode || getDumpIRFlag "ann" flagvals
              (annSCCs, ctx) <- liftIO $
                  mapFoldM' sortedBindings ctxTC
                              (typecheckSCC showASTs showAnnExprs pauseOnErrors tcenv0)
              liftIO $ unTc tcenv0 (convertTypeILofAST modast ctx annSCCs)
          Errors os -> do
              when verboseMode $ do liftIO $ putStrLn "~~~ Typechecking the module's context failed"
              return (Errors os)
      dups -> return (Errors $ [text "Unable to check module due to duplicate bindings: "
                               ] ++ (map (prettyWithLineNumbers . rangeOf . snd) (concat dups)))
    return rv
 where
   mkContext :: [ContextBinding t] -> [ContextBinding t]
             -> [ContextBinding t] -> (Map T.Text (FosterPrim t))
             -> Seq Ident -> Seq (DataType t) -> Seq (EffectDecl t) -> Context t
   mkContext declBindings nullCtorBnds primBindings primOpMap globalvars datatypes effdecls =
     Context declBindsMap nullCtorsMap primBindsMap primOpMap globalvars Seq.empty tyvarsMap effctors Seq.empty ctorinfo dtypes
       where effctors     = getCtorInfo' effdecls
             ctorinfo     = getCtorInfo  datatypes
             dtypes       = getDataTypes (datatypes Seq.>< fmap dataTypeOfEffectDecl effdecls)
             primBindsMap = Map.fromList $ map unbind primBindings
             nullCtorsMap = Map.fromList $ map unbind nullCtorBnds
             declBindsMap = Map.fromList $ map unbind declBindings
             tyvarsMap    = Map.fromList []
             unbind (TermVarBinding s t) = (s, t)

   mkBinding' (bn, ty, isForeign) =
     case isForeign of
       NotForeign   -> pair2binding (bn, ty, Nothing)
       IsForeign nm -> TermVarBinding bn
                         (TypedId ty (GlobalSymbol bn (RenameTo nm)), Nothing)

   computeContextBindings' :: [(T.Text, TypeAST, IsForeignDecl)] -> [ContextBinding TypeAST]
   computeContextBindings' decls = map mkBinding' decls

   computeContextBindings :: [(T.Text, TypeAST, CtorId)] -> [ContextBinding TypeAST]
   computeContextBindings decls = map (\(s,t,cid) -> pair2binding (s, t, Just cid)) decls

   effectContextBindings :: EffectDecl TypeAST -> [ContextBinding TypeAST]
   effectContextBindings ed = map (\(EffectCtor dctor outty) -> 
        -- For an effect operation    Op args => out   for effect E,
        -- add a binding do_Op :: { args => out @E }
        let nm = T.concat [T.pack "do_", dataCtorName dctor]
            ty0 = FnTypeAST (dataCtorTypes dctor) outty
                            (effectSingle (typeFormalName $ effectDeclName ed)
                                          [TyVarAST tv | (tv, _k) <- map convertTyFormal (dataCtorDTTyF dctor)])
                            FastCC FT_Func
            ty = case dataCtorDTTyF dctor of
                  [] -> ty0
                  formals -> ForAllAST (map convertTyFormal formals) ty0 in
        TermVarBinding nm (TypedId ty (GlobalSymbol nm NoRename), Nothing)
      ) (effectDeclCtors ed)

   dataTypeOfEffectDecl :: EffectDecl t -> DataType t
   dataTypeOfEffectDecl (EffectDecl nm tyformals effctors rng) =
                         DataType   nm tyformals ctors False rng
      where ctors = map effectCtorAsData effctors

   -- Given a data type  T (A1::K1) ... (An::Kn)
   -- returns the type   T A1 .. An   (with A1..An free).
   typeOfDataType :: DataType TypeAST -> TypeAST
   typeOfDataType dt =
     let boundTyVarFor (TypeFormal name sr _kind) = TyVarAST $ BoundTyVar name sr in
     TyAppAST (TyConAST $ typeFormalName $ dataTypeName dt)
              (map boundTyVarFor $ dataTypeTyFormals dt)

   splitCtorTypes :: [(T.Text, Either TypeAST TypeAST, CtorId)] ->
                    ([(T.Text, TypeAST, CtorId)]
                    ,[(T.Text, TypeAST, CtorId)])
   splitCtorTypes xs = go xs [] []
     where go [] rl rr = (reverse rl, reverse rr)
           go ((nm, Left  ty, cid):xs) rl rr = go xs ((nm, ty, cid):rl) rr
           go ((nm, Right ty, cid):xs) rl rr = go xs rl ((nm, ty, cid):rr)

   extractCtorTypes :: DataType TypeAST -> [(T.Text, Either TypeAST TypeAST, CtorId)]
   extractCtorTypes dt = map nmCTy (dataTypeCtors dt)
     where nmCTy dc@(DataCtor name tyformals types _repr _lone _range) =
                 (name, ctorTypeAST tyformals dtType types, cid)
                         where dtType = typeOfDataType dt
                               cid    = ctorId (typeFormalName $ dataTypeName dt) dc

   -- Nullary constructors are constants; non-nullary ctors are functions.
   ctorTypeAST [] dtType [] = Left dtType
   ctorTypeAST [] dtType ctorArgTypes =
                            Right $ FnTypeAST ctorArgTypes dtType nullFx FastCC FT_Func

   ctorTypeAST tyformals dt ctorArgTypes =
     let f = ForAllAST (map convertTyFormal tyformals) in
     case ctorTypeAST [] dt ctorArgTypes of
       Left ty  -> Left $ f ty
       Right ty -> Right $ f ty

   freeVarsOf :: Expr b => Set T.Text -> b -> T.Text -> [T.Text]
   freeVarsOf toplevels body nm =
     let allCalledFns = Set.fromList $ freeVars body in
     -- Remove everything that isn't a top-level binding.
     let nonPrimitives = Set.intersection allCalledFns toplevels in
     -- remove recursive function name calls
     Set.toList $ Set.filter (\name -> nm /= name) nonPrimitives

   buildCallGraphList' :: [ContextBinding TypeAST] -> Set T.Text
                      -> [(ContextBinding TypeAST, T.Text, [T.Text])]
   buildCallGraphList' bindings toplevels =
     map mkDep bindings
      where
       mkDep = \binding@(TermVarBinding nm (v, _)) ->
                    (binding, nm, freeVarsOf toplevels v nm)

   buildCallGraphList :: [ (T.Text, ExprAST TypeAST) ] -> Set T.Text
                      -> [((T.Text, ExprAST TypeAST), T.Text, [T.Text])]
   buildCallGraphList defns toplevels =
     map mkDep defns
      where
       mkDep = \(nm, expr) -> ((nm, expr), nm, freeVarsOf toplevels expr nm)

   liftSnd :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
   liftSnd f (c, a) = do b <- f a ; return (c, b)

   -- The functions from the module have already been converted;
   -- now we just need to convert the rest of the module...
   convertTypeILofAST :: ModuleExpr TypeAST
                      -> Context TypeTC
                      -> [[OutputOr (Binding (AnnExpr TypeTC))]]
                      -> Tc TCRESULT
   convertTypeILofAST mAST ctx_tc oo_unprocessed = do
     mapM_ (tcInject (collectIntConstraints . snd)) (concat oo_unprocessed)
     tcApplyIntConstraints

     constraints <- tcGetConstraints
     processTcConstraints constraints

     -- annexprs :: [[Binding (AnnExpr TypeTC)]]
     annexprs <- mapM (mapM (tcInject (liftSnd handleCoercionsAndConstraints))) oo_unprocessed

     -- We've already typechecked the definitions, so no need to re-process them...
     -- First, convert the non-defn parts of our module from TypeAST to TypeTC.
     -- mTC :: ModuleExpr TypeTC
     mTC <- let nonDefn (ToplevelDefn _) = False
                nonDefn _                = True
            in convertModule (tcType ctx_tc) $ mAST { moduleASTitems =
                                      filter nonDefn (moduleASTitems mAST) }

     -- TODO get the non-fns from mTC items, wrap around buildExprSCC' ...
    
     call_of_main <- do
        levels <- mkLevels
        let mainty = FnTypeTC [unitTypeTC] unitTypeTC emptyEffectTC (UniConst FastCC) (UniConst FT_Proc) levels
        return $ AnnCall (annotForRange $ MissingSourceRange "buildExprSCC'main!") unitTypeTC
                                                (E_AnnVar (annotForRange $ MissingSourceRange "buildExprSCC'main")
                                                          (TypedId mainty (GlobalSymbol (T.pack "main") NoRename), Nothing))
                                                [] CA_None

     let mTC' = ModuleIL (buildExprSCC' annexprs call_of_main)
                         (externalModuleDecls mTC)
                         (moduleASTdataTypes  mTC)
                         (moduleASTprimTypes  mTC)
                         (moduleASTeffects    mTC)
                         (moduleASTsourceLines mAST)

     kNormalizeModule  mTC' ctx_tc

       where
        buildExprSCC' :: [[Binding (AnnExpr TypeTC)]] -> AnnExpr TypeTC -> (AnnExpr TypeTC)
        buildExprSCC' [] _ = error "Main.hs: Can't build SCC of no functions!"
        buildExprSCC' es call_of_main = foldr build call_of_main es
         where isFn (E_AnnFn {}) = True
               isFn _ = False

               build binds body = case binds of
                [] -> body
                [(nm, expr)] | not (isFn expr) ->
                    AnnLetVar emptyAnnot (GlobalSymbol nm NoRename) expr body
                fnbinds ->
                    let fnes = map snd fnbinds in
                    if all isFn fnes
                      then let fns = [f | E_AnnFn f <- fnes] in
                           AnnLetFuns emptyAnnot (map fnIdent fns) fns body
                      else error $ "Main.hs: unable to build expr from mixed fns/non-fns"

               emptyAnnot = annotForRange $ MissingSourceRange "buildExprSCC'"

        -- Note that we discard internal declarations, which are only useful
        -- during type checking. External declarations, on the other hand,
        -- will eventually be needed during linking.
        externalModuleDecls mAST = filter has_no_defn (moduleASTdecls mAST)
          where
            funcnames = map fnAstName (moduleASTfunctions mAST)
            valuenames = Set.fromList funcnames
            has_no_defn (nm, _, _) = Set.notMember nm valuenames

   processTcConstraints :: [(TcConstraint, SourceRange)] -> Tc ()
   processTcConstraints constraints = mapM_ processConstraint constraints
      where
        processConstraint ((TcC_IsFloat mtv), range) = do
          zt <- repr (MetaTyVarTC mtv)
          case zt of
            TyAppTC (TyConTC "Float32") [] -> return ()
            TyAppTC (TyConTC "Float64") [] -> return ()
            m@(MetaTyVarTC _) -> unify m (TyAppTC (TyConTC "Float64") []) []
            _ -> tcFails [text "Unable to give the type" <+> prettyT zt <+>
                          text "to the numeric constant",
                          highlightFirstLineDoc range]

        processConstraint ((TcC_SeqUnit mtv), _range) = do
            zt <- repr (MetaTyVarTC mtv)
            case zt of
              TupleTypeTC {} -> return ()
              PrimIntTC   {} -> return ()
              m@(MetaTyVarTC _) -> unify m unitTypeTC [text "seq-unit"]
              _ -> error $ "Main.hs:processConstraint"

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
  case deserialiseFromBytes decodeTerm cborbytes of
    Left failure -> error $ show failure
    Right (_bs, term) -> return term

main = do
  Criterion.initializeTime
  args <- getArgs
  case args of
    (infile : outfile : rest) -> do
        flagVals <- parseOpts rest

        --liftIO $ performGC
        --Just stats1 <- liftIO $ Criterion.getGCStats

        (ci_time, cb_program) <- ioTime $ readAndParseCbor infile
        let wholeprog = cb_parseWholeProgram cb_program

        --liftIO $ performGC
        --Just stats2 <- liftIO $ Criterion.getGCStats
        --liftIO $ putStrLn $ "delta in gc stats during protobuf parsing: " ++ show (stats2 `minusGCStats` stats1)

        if getFmtOnlyFlag flagVals
          then do
            let WholeProgramAST modules = wholeprog
            liftIO $ putDocLn (prettyT (head modules))
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
   plaref      <- newIORef []
   hc <- getHashCache "fosterc-z3-cache.cbor"


   let tcenv = TcEnv {       tcEnvUniqs = uniqref,
                      tcUnificationVars = varlist,
                              tcParents = [],
                   tcMetaIntConstraints = icmap,
                          tcConstraints = constraints,
               tcSubsumptionConstraints = subcnst,
                     tcCurrentFnEffect = Nothing,
                        tcCurrentLevel = 0,
              tcPendingLevelAdjustments = plaref,
                tcUseOptimizedCtorReprs = getCtorOpt flagVals,
                          tcVerboseMode = getVerboseFlag flagVals,
                     tcNoQuantification = getNoQuant flagVals }
   (nc_time, mb_errs) <- ioTime $ runExceptT $ evalStateT (compile wholeprog tcenv outfile)
                    CompilerContext {
                           ccVerbose  = getVerboseFlag flagVals
                         , ccFlagVals = flagVals
                         , ccDumpFns  = getDumpFns flagVals
                         , ccUniqRef  = uniqref
                         , ccHashCache = hc
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

     Right (Timings tc_time sr_time mn_time cp_time sc_time pb_time) -> do

       (nqueries, querytime) <- readIORef smtStatsRef
       reportFinalPerformanceNumbers ci_time nqueries querytime tc_time sr_time
                                     mn_time cp_time sc_time nc_time pb_time
                                     (sum (modulesSourceLines wholeprog))

toFixed :: Double -> Doc any
toFixed f = text $ T.pack $ printf "%.1f" f

{-
minusGCStats (GCStats a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2 n2 o2 p2 q2 r2)
             (GCStats a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1 r1)
  = GCStats (a2 - a1) (b2 - b1) (c2 - c1) (d2 - d1) (e2 - e1) (f2 - f1) (g2 - g1) (h2 - h1) (i2 - i1) (j2 - j1) (k2 - k1) (l2 - l1) (m2 - m1) (n2 - n1) (o2 - o1) (p2 - p1) (q2 - q1) (r2 - r1)
-}

reportFinalPerformanceNumbers :: Double -> Int -> [ (Double, Double) ]
                              -> Double -> Double -> Double -> Double
                              -> Double -> Double -> Double
                              -> Int -> IO ()
reportFinalPerformanceNumbers ci_time nqueries querytime tc_time sr_time
                              mn_time cp_time sc_time
                              nc_time pb_time wholeProgNumLines = do
       let ct_time = (nc_time - (tc_time + mn_time + cp_time + sc_time))
       let total_time = ci_time + pb_time + nc_time
       let pct f1 f2 = (100.0 * f1) / f2
       let fmt_pct time = let p = pct time nc_time
                              n = if p < 10.0 then 2 else if p < 100.0 then 1 else 0
                              padding = fill n (text "") in
                          padding <> parens (toFixed p <> text "%")
       let fmt str time = text str <+> (fill 11 $ text $ T.pack $ Criterion.secs time) <+> fmt_pct time
       
       if nqueries > 0
         then do
           let pairwise f = \(x,y) -> (f x, f (x + y))
           putDocLn $ vcat $
                         [text "                                            (initial query time, overall query time)"
                         ,text "# SMT queries (uncached):" <+> pretty nqueries <+> text "taking" <+> pretty (map (pairwise Criterion.secs) querytime)]
         else return ()
                         
       putDocLn $ vcat $ [fmt "typecheck   time:" tc_time
                         ,fmt "inlining    time:" sr_time
                         ,fmt "monomorphiz time:" mn_time
                         ,fmt "static-chk  time:" sc_time
                         ,fmt "codegenprep time:" cp_time
                         ,fmt "'other'     time:" ct_time
                         ,fmt "sum elapsed time:" nc_time
                         ,text ""
                         ,fmt "CBOR-in     time:" ci_time
                         ,fmt "  capnp-out time:" pb_time
                         ,text "overall wall-clock time:" <+> text (T.pack $ Criterion.secs $ total_time)
                         ,text "# source lines:" <+> pretty wholeProgNumLines
                         ,text "source lines/second:" <+> toFixed (fromIntegral wholeProgNumLines / total_time)
                         ]

data CompilerTimings = Timings Double Double Double Double Double Double

compile :: WholeProgramAST (ExprSkel ExprAnnot) TypeP -> TcEnv -> String -> Compiled CompilerTimings
compile wholeprog tcenv outfile = do
    (return wholeprog)
     >>= mergeModules -- temporary hack
     >>= desugarParsedModule tcenv
     >>= typecheckSourceModule tcenv
     >>= lowerModule outfile

mergeModules :: WholeProgramAST (ExprSkel ExprAnnot) ty
              -> Compiled (ModuleExpr ty)
mergeModules (WholeProgramAST modules) = do
  return (foldr1 mergedModules modules)
  -- Modules are listed in reverse dependency order, conveniently.
  -- TODO track explicit module dependency graph, decompose to DAG, etc.
  where mergedModules m1 m2 = ModuleAST {
       moduleASThash        = moduleASThash        m1 -- meh
     , moduleASTitems       = moduleASTitems       m1 ++ moduleASTitems m2
     , moduleASTsourceLines = moduleASTsourceLines m1 `appendSourceLines`
                                                         moduleASTsourceLines m2
     , moduleASTprimTypes   = moduleASTprimTypes   m1 -- should be the same
     , moduleASTincludes    = moduleASTincludes   m1 ++ moduleASTincludes m2
                                     }

desugarParsedModule :: TcEnv -> ModuleExpr TypeP ->
                      Compiled (ModuleExpr TypeAST)
desugarParsedModule tcenv m = do
  (liftIO $ unTc tcenv (convertModule astOfParsedType m)) >>= dieOnError
 where
  astOfParsedType :: TypeP -> Tc TypeAST
  astOfParsedType typep =
    let q = astOfParsedType in
    case typep of
          TyAppP (TyConP "Word"  )    [] -> return $ PrimIntAST         IWd
          TyAppP (TyConP "WordX2")    [] -> return $ PrimIntAST         IDw
          TyAppP (TyConP "Int64" )    [] -> return $ PrimIntAST         I64
          TyAppP (TyConP "Int32" )    [] -> return $ PrimIntAST         I32
          TyAppP (TyConP "Int16" )    [] -> return $ PrimIntAST         I16
          TyAppP (TyConP "Int8"  )    [] -> return $ PrimIntAST         I8
          TyAppP (TyConP "Bool"  )    [] -> return $ PrimIntAST         I1
          TyAppP (TyConP "Array" )   [t] -> liftM  ArrayTypeAST            (q t)
          TyAppP (TyConP "Ref"   )   [t] -> liftM  RefTypeAST              (q t)
          TyAppP con types       -> liftM2   TyAppAST (q con) (mapM q types)
          TyConP nam             -> return $ TyConAST nam
          RecordTypeP labels types -> liftM (RecordTypeAST labels) (mapM q types)
          TupleTypeP k   types   -> liftM (TupleTypeAST k)    (mapM q types)
          ForAllP    tvs t       -> liftM (ForAllAST $ map convertTyFormal tvs) (q t)
          TyVarP     tv          -> do return $ TyVarAST tv
          FnTypeP s t fx cc cs sr -> do s' <- mapM q s
                                        t' <- q t
                                        fx' <- case fx of
                                                 Nothing -> return $ MetaPlaceholderAST MTVEffect   ("effectvar:" ++ showSourceRangeStr sr)
                                                 Just xx -> q xx
                                        return $ FnTypeAST  s' t' fx' cc cs
          RefinedTypeP nm t e -> do t' <- q t
                                    e' <- convertExprAST q e
                                    return $ RefinedTypeAST (T.unpack nm) t' e'
          MetaPlaceholder desc -> return $ MetaPlaceholderAST MTVTau desc

type TCRESULT = ModuleIL KNExpr TypeIL

typecheckSourceModule :: TcEnv ->          ModuleExpr TypeAST
                      -> Compiled (Double, TCRESULT)
typecheckSourceModule tcenv sm = do
    verboseMode <- gets ccVerbose
    flags <- gets ccFlagVals
    let pauseOnErrors = getInteractiveFlag flags
    --whenDumpIR "ast" $ do
    --   putDocLn (outLn $ "vvvv AST :====================")
    --   putDocLn (vsep $ map showFnStructure (moduleASTfunctions sm))
    --   putDocLn $ pretty sm
    --   return ()

    --liftIO $ performGC
    --Just stats1 <- liftIO $ Criterion.getGCStats

    (tc_time, res0) <- ioTime $ typecheckModule verboseMode pauseOnErrors flags sm tcenv

    --liftIO $ performGC
    --Just stats2 <- liftIO $ Criterion.getGCStats
    --liftIO $ putStrLn $ "delta in gc stats during typechecking: " ++ show (stats2 `minusGCStats` stats1)

    res <- dieOnError res0
    return (tc_time, res)

lowerModule :: FilePath -> (Double, (ModuleIL KNExpr TypeIL))
            -> Compiled CompilerTimings
lowerModule outfile (tc_time, kmod) = do
     flags    <- gets ccFlagVals

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
     hc <- gets ccHashCache
     liftIO $ hashCachePersist hc

     maybeInterpretKNormalModule kmod

     (mkn_time, cp_time, pb_time) <- if getTypecheckOnly flags
                                       then return (0.0, 0.0, 0.0)
                                       else lowerModulePhase2 monomod0 flags outfile
     return (Timings tc_time mkn_time mn_time cp_time sc_time pb_time)

  where

    maybeInterpretKNormalModule kmod = do
        flagVals <- gets ccFlagVals
        case getInterpretFlag flagVals of
            Nothing -> return ()
            Just tmpDir -> do
                let cmdLineArgs = getProgArgs flagVals
                _unused <- liftIO $ interpretKNormalMod kmod tmpDir cmdLineArgs
                return ()



lowerModulePhase2 monomod0 flags outfile = do
     monomod2 <- knLoopHeaders  monomod0

     whenDumpIR "mono-loop" $ do
      putDocLn $ (outLn "/// Loop-headered program =============")
      putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod2)))
      _ <- liftIO $ renderKN monomod2 True
      putDocLn $ (outLn "^^^ ===================================")

     monomod2a  <- knSinkBlocks   monomod2

     whenDumpIR "mono-sunk" $ do
      putDocLn $ (outLn "/// Block-sunk program =============")
      _ <- liftIO $ renderKN monomod2a  True
      putDocLn $ (outLn "^^^ ===================================")

     (mkn_time, pccmod) <- ioTime $ do
          assocBinders <- sequence [do r <- newOrdRef Nothing
                                       let renam = case isForeign of
                                                    NotForeign -> NoRename
                                                    IsForeign nm -> RenameTo nm
                                       let xid = GlobalSymbol s renam
                                       let tid = TypedId ty xid
                                       let b = MKBound tid r
                                       return (xid, b)
                                   | (s, ty, isForeign) <-
                                            ("main", FnType [] (TupleType []) CCC FT_Proc, NotForeign)
                                            : moduleILdecls monomod2a]

          let mainBinder = head assocBinders
          let binders = Map.fromList assocBinders
          mk <- evalStateT 
                  (mkOfKNMod (moduleILbody monomod2a) (snd mainBinder))
                  binders
          mknInline mk (snd mainBinder) (getInliningGas flags)
          uref <- gets ccUniqRef
          pcc@(PreCloConv (cffns,_topbinds)) <- pccOfTopTerm uref mk

          whenDumpIR "cfg" $ do
              putDocLn $ (outLn "/// pre//CFG program ==================")
              putDocP  $ vcat $ map prettyCFFn cffns
              putDocLn $ (outLn "^^^ ===================================")

          return $ monomod2a { moduleILbody = pcc }

     whenDumpIR "mono" $ do
         putDocLn $ (outLn "/// Loop-headered program =============")
         putDocLn $ (outLn $ "///               size: " ++ show (knSize (moduleILbody monomod2)))
         _ <- liftIO $ renderKN monomod2 True
         putDocLn $ (outLn "^^^ ===================================")

     whenDumpIR "mono-sunk" $ do
         putDocLn $ (outLn "/// Block-sunk program =============")
         _ <- liftIO $ renderKN monomod2a  True
         putDocLn $ (outLn "^^^ ===================================")

     ccmod    <- closureConvert pccmod
     whenDumpIR "cc" $ do
         putDocLn $ (outLn "/// Closure-converted program =========")
         _ <- liftIO $ renderCC ccmod True
         putDocLn $ (outLn "^^^ ===================================")

     (cp_time, (ilprog, prealloc)) <- ioTime $ prepForCodegen ccmod
     whenDumpIR "prealloc" $ do
         putDocLn $ (outLn "/// Pre-allocation ====================")
         _ <- liftIO (renderCC (ccmod { moduleILbody = let (CCBody _ vals) = moduleILbody ccmod in
                                                         CCBody prealloc vals }) True )
         putDocLn $ (outLn "^^^ ===================================")

     whenDumpIR "il" $ do
         putDocLn $ (outLn "/// ILProgram =========================")
         putDocLn (showILProgramStructure ilprog)
         putDocLn $ (outLn "^^^ ===================================")

     liftIO $ putDocLn $ (string $ "/// Mono    size: " ++ show (knSize (moduleILbody monomod0)))

     (pb_time , _) <- ioTime $ ccWhen (not . getTypecheckOnly . ccFlagVals) $
                                   (liftIO $ dumpILProgramToCapnp ilprog (outfile ++ ".cb"))

     return (mkn_time, cp_time, pb_time)

  where

    closureConvert pccmod = do
        uniqref <- gets ccUniqRef
        liftIO $ do
            let datatypes = moduleILprimTypes pccmod ++
                            moduleILdataTypes pccmod
            let dataSigs = dataTypeSigs datatypes
            u0 <- readIORef uniqref
            let (rv, u') = closureConvertAndLift dataSigs (u0 + 1) pccmod
            writeIORef uniqref u'
            return rv

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
    prettySrc (BoundTyVar name _) = text name
    prettySrc (SkolemTyVar name uniq _kind) = text "$" <> text name <> text ":" <> pretty uniq

    forallPart tvs = hsep $ [text "forall"] ++ map (\(tv, k) -> parens (prettySrc tv <+> text ":" <+> pretty k)) tvs

    textid txt = if Char.isAlphaNum (T.head txt)
                    then         text txt
                    else parens (text txt)

    allNames = "abcdefghijklmnop"

    dumpPrimitive :: (T.Text, (TypeAST, FosterPrim TypeAST)) -> IO ()
    dumpPrimitive (name, ((FnTypeAST args ret _fx _ _), _primop)) = do
      
      let namesArgs = [(text (T.singleton nameChar) , arg) | (nameChar, arg) <- zip allNames args]
      putDocLn $ (fill 20 $ textid name)
                 <> text " = {"
                     <+> hsep [fill 12 (name <+> text ":" <+> prettyT arg) <+> text "=>"
                              | (name, arg) <- namesArgs]
                     <+> fill 23 (text "prim" <+> text name <+> hsep (map fst namesArgs))
                 <+> text "}; // :: " <> prettyT ret -- <+> text "; fx=" <> prettyT fx
    
    dumpPrimitive (name, ((ForAllAST tvs (FnTypeAST args ret _fx _ _)), _primop)) = do
      let argNames = [text (T.singleton nameChar) | (nameChar, _arg) <- zip allNames args]
      putDocLn $ (fill 20 $ textid name) <+> text "::" <+> forallPart tvs
                                         <+> text "{" <+>
                                            hsep (map (\a -> prettyT a <+> text "=>") args) <+> prettyT ret
                                         <+> text "}"
                                         <> text ";"
      putDocLn $ (fill 20 $ textid name)
                 <> text " = {"
                     <+> hsep [fill 12 name <+> text "=>"
                              | name <- argNames]
                     <+> fill 23 (text "prim" <+> text name <+> hsep argNames)
                 <+> text "}; // :: " <> prettyT ret -- <+> text "; fx=" <> prettyT fx

    dumpPrimitive (name, (_ty, _primop)) = error $ "Can't dump primitive " ++ T.unpack name ++ " yet."
