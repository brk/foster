{-# LANGUAGE StandaloneDeriving, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2014 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNStaticChecks (runStaticChecks) where

import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.List(foldl')
import Data.Maybe(fromMaybe)
import Data.IORef(writeIORef)

import Foster.MonoType
import Foster.Base
import Foster.KNUtil
import Foster.Config

import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.HughesPJ as HughesPJ(Doc)
import qualified Data.Text as T

import Control.Monad.Error(throwError, catchError, runErrorT, ErrorT)
import Control.Monad.State(gets, liftIO, evalStateT, execStateT, StateT,
                           execState, State, forM, forM_, runStateT,
                           liftM, liftM2, get, put, lift)

import qualified SMTLib2 as SMT
import           SMTLib2(app, Script(..), Command(..), Option(..), Type(..))
import qualified SMTLib2.Core as SMT
import           SMTLib2.Core(tBool, (===), (=/=))
import SMTLib2.BitVector

import Foster.RunZ3 (runZ3)

data SymDecl = SymDecl SMT.Name [SMT.Type] SMT.Type

instance Ord SymDecl where compare (SymDecl n1 _ _) (SymDecl n2 _ _) = compare n1 n2
instance Eq  SymDecl where (==)    (SymDecl n1 _ _) (SymDecl n2 _ _) = (==)    n1 n2

data SMTExpr = SMTExpr SMT.Expr (Set SymDecl) [(Ident, SMT.Expr)]

instance Pretty SMT.Expr where pretty e = string (show $ SMT.pp e)

mergeSMTExpr f (SMTExpr e1 s1 m1) (SMTExpr e2 s2 m2) =
    SMTExpr (f e1 e2) (Set.union s1 s2) (m1 ++ m2)

mergeSMTExprAsPathFact (SMTExpr e s m) (Facts preconds identfacts pathfacts decls) =
  Facts preconds (m ++ identfacts) (e:pathfacts) (Set.union s decls)

smtExprAddPathFacts (SMTExpr e s m) ps = SMTExpr e s (ps ++ m)

smtExprLift  f (SMTExpr e s m) = SMTExpr (f e) s m
smtExprLiftM f (SMTExpr e s m) = liftM (\e' -> SMTExpr e' s m) (f e)

data Facts = Facts { fnPreconds :: Map Ident [[MoVar] -> SC SMTExpr]
                   , identFacts :: [(Ident, SMT.Expr)]
                   , pathFacts  :: [SMT.Expr]
                   , symbolicDecls :: Set SymDecl
                   }
------
{-
mergeFactsForCompilation (Facts _ _ pfs1 decls1) (Facts _ _ pfs2 decls2) =
  Facts Map.empty Map.empty (pfs1 ++ pfs2) (mergeDecls decls1 decls2 [] Set.empty)
    where mergeDecls []   [] merged _    = merged
          mergeDecls [] rest merged seen = mergeDecls rest [] merged seen
          mergeDecls (t@(nm, _, _):rest) others merged seen =
            if Set.member nm seen
              then mergeDecls rest others   merged  seen
              else mergeDecls rest others (t:merged) (Set.insert nm seen)
              -}
------
nm id = SMT.N (show id)

ident :: Ident -> SMT.Ident
ident id = SMT.I (nm id) []

smtId  id  = app (ident id) []
smtVar tid = smtId (tidIdent tid)

smtVars tids = map smtVar tids

smtNameI :: SMT.Ident -> SMT.Name
smtNameI (SMT.I nm _) = nm

addIdentFact facts id (SMTExpr expr _ _) ty =
  addSymbolicVar facts' (TypedId ty id)
    where facts' = facts { identFacts = (id, expr):(identFacts facts) }

addIdentFact'' facts id expr ty =
  addSymbolicVar facts' (TypedId ty id)
    where facts' = facts { identFacts = (id, expr):(identFacts facts) }

addIdentFact' id (SMTExpr expr decls idfacts) ty =
 addSymbolicVar' (SMTExpr expr decls idfacts' ) (TypedId ty id)
    where idfacts' = (id, expr):idfacts

addIdentFact''' facts id expr =
    facts { identFacts = (id, expr):(identFacts facts) }

addIdentFacts''' facts idfacts =
    facts { identFacts = idfacts ++ identFacts facts }

mkSymbolicVar :: TypedId MonoType -> SymDecl
mkSymbolicVar v = d
  where id = tidIdent v
        d  = case tidType v of
                FnType dom rng _ _ ->
                      SymDecl (nm id) (map smtType dom) (smtType rng)
                ty -> SymDecl (nm id) []                (smtType ty)

addSymbolicVar facts v = facts { symbolicDecls = Set.insert (mkSymbolicVar v) (symbolicDecls facts) }
addSymbolicDecls facts decls = facts { symbolicDecls = Set.union decls (symbolicDecls facts) }

addSymbolicVar' :: SMTExpr -> TypedId MonoType -> SMTExpr
addSymbolicVar' (SMTExpr e decls idfacts) v = SMTExpr e (Set.insert (mkSymbolicVar v) decls) idfacts

addSymbolicVar'' :: (Maybe (Ident -> SC SMTExpr)) -> TypedId MonoType -> (Maybe (Ident -> SC SMTExpr))
addSymbolicVar'' Nothing _ = Nothing
addSymbolicVar'' (Just f) v = Just (\id -> do e <- f id ; return $ addSymbolicVar' e v)

smtType :: MonoType -> SMT.Type
smtType (PrimInt I1) = tBool
smtType (PrimInt sz) = tBitVec (fromIntegral $ intSizeOf sz)
smtType (ArrayType _) = smtArray
smtType (TupleType tys) = TApp (smtI ("FosterTuple" ++ show (length tys))) (map smtType tys)
smtType (RefinedType v _ _) = smtType (tidType v)
smtType (TyConApp nm tys) = TApp (smtI nm) (map smtType tys)
smtType ty = error $ "smtType can't yet handle " ++ show ty

smtArray = TApp (smtI "FosterArray") []

smtTruncToSize i v = extract (fromIntegral i - 1) 0 v

litOfSize num sz = bv num (fromIntegral $ intSizeOf sz)

scriptImplyingBy' :: SMT.Expr -> Facts -> Script
scriptImplyingBy' pred facts = scriptImplyingBy (bareSMTExpr pred) facts

scriptImplyingBy :: SMTExpr -> Facts -> Script
scriptImplyingBy (SMTExpr pred declset idfacts) facts =
  let preconds = map snd $ idfacts ++ (identFacts facts) in
  let alldecls = Set.toList $ Set.union declset (symbolicDecls facts) in
  let tydecls  = [CmdDeclareType nm arity | (nm, arity) <-
                    uniquesWithoutPrims
                     [(smtNameI id, fromIntegral $ length tys)
                     | SymDecl _ [] (TApp id tys) <- alldecls]] in
  Script $ [CmdSetOption (OptProduceModels True)
           ,CmdSetLogic (SMT.N "QF_AUFBV")
           ,CmdDeclareType (SMT.N "FosterArray") 0
           ,CmdDeclareFun (SMT.N "foster$arraySizeOf") [smtArray] (tBitVec 64)
           ]
        ++ tydecls
        ++ map (\(SymDecl nm tys ty) -> CmdDeclareFun nm tys ty) alldecls
        ++ map CmdAssert (pathFacts facts ++ preconds)
        ++ [CmdPush 1]
        ++ [CmdAssert $ SMT.not pred]

-- As we traverse the input expression, we build up a collection of path facts
-- and id-associated facts (which are, morally, path facts), which we can
-- collectively term F. When it comes time to check an individual precondition,
-- p, we want to make sure that the following formula holds for all possible
-- assignments of values to free variables: [[ F => p ]].
-- The S in SMT stands for "satisfiability", which is to say finding one such
-- assignment (called a "model"), whereas we want "validity" -- which is to say,
-- intuitively, we want to be told that there is no un-satisfying assignment.
--
-- To bridge this gap, we do a small trick:
-- We ask the SMT solver about [[ not (F => p) ]]; if it finds a satisfying
-- assignment, then we know that the same assignment would invalidate our
-- original formula. But if the SMT solver reports that no such assignment
-- exists, then we know that [[ F => p ]] is valid.
--
-- Since the context F may be large, we also have a second trick up our sleeve:
-- we use material implication and de Bruijn laws to turn
-- [[ not (F => p) ]] into [[ not (not F or p) ]] into [[ F and (not p) ]].
--
-- A more compact way of showing this chain of reasoning:
--      forall models, F => p                    =>
--      not (not (forall models, F => p))        =>
--      not (exists model , not (F => p))        =>
--      not (exists model , not (not F or p))    =>
--      not (exists model , F && not p)
--
-- We can also look at just the context, F. If the SMT solver reports that
-- F by itself is unsatisfiable, then any choice of (negated) predicate will
-- appear to be valid. Intuitively this corresponds to dead code paths, as the
-- "B" branch of ``if true then A else B`` will have a path fact of
-- ``true = false`` which is obviously inconsistent.

uniquesWithoutPrims pairs =
    pairs `butnot` [(SMT.N "Bool", 0), (SMT.N "BitVec", 0),
                    (SMT.N "FosterArray", 0)]
------

type SC = StateT SCState Compiled
data SCState = SCState {
  scExtraFacts :: Map Ident (Ident -> SMT.Expr)
}

scAddFact id k = do
  sc <- get
  put $ sc { scExtraFacts = Map.insert id k (scExtraFacts sc) }

scGetFact id = do
  sc <- get
  return $ Map.lookup id (scExtraFacts sc)

-- Errors will be propagated, while unsat (success) results are trivial...
scRunZ3 :: KNMono -> HughesPJ.Doc -> SC ()
scRunZ3 expr doc = lift $ do
  res <- liftIO $ runZ3 (show doc) (Just "(pop 1)\n(check-sat)")
  case res of
    Left x -> throwError [text x, pretty expr, string (show doc)]
    Right ("unsat":"sat":_) -> return ()
    Right ["unsat","unsat"] -> do
        liftIO $ putStrLn $ "WARNING: scRunZ3 returning OK due to inconsistent context..."
        liftIO $ putStrLn $ "   This is either dead code or a buggy implementation of our SMT query generation."
        return ()
    Right strs -> throwError ([text "Unable to verify precondition associated with expression",
                               pretty expr,
                               string (show doc)] ++ map text strs)
  return ()

putZ3Result (Left x) = putStrLn x
putZ3Result (Right strs) = mapM_ (putStrLn . ("\t"++)) strs

runStaticChecks :: ModuleIL KNMono MonoType -> Compiled ()
runStaticChecks m = do
  checkModuleExprs (moduleILbody m) (Facts Map.empty [] [] Set.empty)

checkModuleExprs :: KNMono -> Facts -> Compiled ()
checkModuleExprs expr facts =
  case expr of
    KNLetFuns     ids fns b -> do
        facts' <- foldlM (\facts (id, fn) -> recordIfHasFnPrecondition facts id (fnType fn))
                           facts (zip ids fns)
        mapM_ (\fn -> checkFn fn facts') fns
        checkModuleExprs b facts'
    KNCall {} ->
      return ()
    _ -> error $ "Unexpected expression in checkModuleExprs: " ++ show expr

checkFn fn facts = do
  evalStateT (checkFn' fn facts) (SCState Map.empty)

checkFn' fn facts0 = do
  -- Assert any refinements associated with the function's args
  -- within the scope of the function body.

  -- Example of a fnVar:  state : (% rstate : Int32 : rstate < 10)
  -- So we convert the refinement type into a predicate, and pass the variable
  -- as the argument, thus producing the path fact (state < 10).
  -- To handle dependent refinements, each predicate takes all the fnvars...
  let (relevantFormals, relevantActuals) =
        unzip $ Prelude.concat [case tidType v of RefinedType v' _ _ -> [(v', v)]
                                                  _                  -> []
                               | v <- fnVars fn]
      mbFnOfRefinement rt@(RefinedType {}) = [fnOfRefinement rt]
      mbFnOfRefinement _                   = []

      fnOfRefinement (RefinedType _ body _) =
          Fn (fnVar fn) relevantFormals body NotRec (ExprAnnot [] (MissingSourceRange "fnOfRefinement") [])

      refinements = concatMap mbFnOfRefinement (map tidType $ fnVars fn)
      foldPathFact facts f = do liftIO $ putStrLn $ "checkFn' calling smtEvalApp... {"
                                e <- smtEvalApp facts f relevantActuals
                                liftIO $ putStrLn $ "checkFn' called  smtEvalApp... }"
                                return $ mergeSMTExprAsPathFact e facts
  liftIO $ putStrLn $ "%%%%%%%%%%%%%%%%%%%%%%%%%%%"
  liftIO $ putStrLn $ show $ map pretty refinements
  liftIO $ putStrLn $ show $ fnVars fn
  liftIO $ putStrLn $ show relevantFormals
  liftIO $ putStrLn $ show relevantActuals


  facts <- foldlM foldPathFact facts0 refinements

  -- Before processing the body, add declarations for the function formals,
  -- and record the preconditions associated with any function-typed formals.
  let facts' = foldl' addSymbolicVar facts (fnVars fn)
  facts''  <- foldlM recordIfTidHasFnPrecondition facts' (fnVars fn)

  liftIO $ putStrLn $ "checking body " ++ (show (pretty (fnBody fn)))
  smtexpr <- checkBody (fnBody fn) facts''
  liftIO $ putStrLn $ "... checked body"
  -- We need to add declarations for the function variables to both the facts
  -- environment (for use in checks within the function) and the result
  -- (for use in checks outside the function definition).
  return $ foldl' addSymbolicVar'' smtexpr (fnVars fn)

smtEvalApp facts fn args = do
  -- skolems <- mapM genSkolem (map tidType args)
  smt_f <- (mkPrecondGen facts fn) args
  return $ smt_f

recordIfTidHasFnPrecondition facts tid =
   recordIfHasFnPrecondition facts (tidIdent tid) (tidType tid)

withPathFact facts pathfact = facts { pathFacts = pathfact : pathFacts facts }

lift2 f [x, y] = f x y

inRangeCO x (a, b) = bvsge x a `SMT.and` bvslt x b
inRangeCC x (a, b) = bvsge x a `SMT.and` bvsle x b

smtI s = SMT.I (SMT.N s) []

smtArraySizeOf x = app (smtI "foster$arraySizeOf") [x]

fnMap = Map.fromList    [("==", (===))
                        ,("!=", (=/=))
                        ,("+", bvadd)
                        ,("-", bvsub)
                        ,("bitand", bvand)
                        ,("bitxor", bvxor)
                        ,("bitor", bvor)
                        ,("<u",  bvult) ,("<s",  bvslt)
                        ,(">u",  bvugt) ,(">s",  bvsgt)
                        ,("<=u", bvule) ,("<=s", bvsle)
                        ,(">=u", bvuge) ,(">=s", bvsge)
                        ]

smtAll [expr] = expr
smtAll exprs = SMT.app (smtI "and") exprs

staticArrayValueBounds [] = Nothing
staticArrayValueBounds ((Right _):_) = Nothing
staticArrayValueBounds (Left (LitInt li):entries) = go entries (Just (litIntValue li, litIntValue li))
  where go [] mnmx = mnmx
        go _ Nothing = Nothing
        go ((Right _):_) _ = Nothing
        go (Left (LitInt li):xs) (Just (mn, mx)) = let x = litIntValue li in
                                                   go xs (Just (min x mn, max x mx))

withDecls :: Facts -> (Ident -> SC SMT.Expr) -> Maybe (Ident -> SC SMTExpr)
withDecls facts f = Just $
    \x -> do e <- f x
             return $ SMTExpr e (symbolicDecls facts) (identFacts facts)

withBindings :: TypedId MonoType -> [TypedId MonoType] -> Facts -> SC Facts
withBindings fnv vs facts0 = do
  -- For example, given f = { x : (% z : Int32 : ...) => y : Int32 => x + y }
  -- the relevant formals are [z] and the relevant actuals are [x].
  -- The computed refinements would be [ { z => ... } ]
  -- TODO pick better names for the relevants...
  let (relevantFormals, relevantActuals) =
        unzip $ Prelude.concat [case tidType v of RefinedType v' _ _ -> [(v', v)]
                                                  _                  -> []
                               | v <- vs]
      mbFnOfRefinement rt@(RefinedType {}) = [fnOfRefinement rt]
      mbFnOfRefinement _                   = []

      fnOfRefinement (RefinedType _ body _) =
          Fn fnv relevantFormals body NotRec (ExprAnnot [] (MissingSourceRange "fnOfRefinement") [])

      refinements = concatMap mbFnOfRefinement (map tidType vs)
      foldPathFact facts f = do liftIO $ putStrLn $ "withBindings calling smtEvalApp... { "
                                e <- smtEvalApp facts f relevantActuals
                                liftIO $ putStrLn $ "withBindings called  smtEvalApp... } "
                                return $ mergeSMTExprAsPathFact e facts
  facts <- foldlM foldPathFact facts0 refinements

  -- Before processing the body, add declarations for the function formals,
  -- and record the preconditions associated with any function-typed formals.
  let facts' = foldl' addSymbolicVar facts vs
  --facts''  <- foldlM recordIfTidHasFnPrecondition facts' (fnVars fn)
  return facts'

-- Given a variable with function type { t1 => ... => tn }
-- returns a list of functions, one per refined type in the signature;
-- each function corresponds to one refined parameter.
-- For example, for the type { Int32 => % b : Int32 : p(b) => Int32 }
-- we would return [ { _ => b => p(b) } ]
--
-- These functions are used to generate a precond with
-- mkPrecondGen/compilePreconditionFn, then stored in the fnPreconds map.
-- TODO handle return type refinements...?
computeRefinements :: TypedId MonoType -> [FnMono]
computeRefinements fnv =
  let
      ts   = monoFnTypeDomain (tidType fnv)
      frsh = Ident (T.pack "_") 0 -- Well, fresh enough...?

      mbFnOfRefinement (RefinedType v e _) = [fnOfRefinement v e]
      mbFnOfRefinement _                   = []

      fnOfRefinement _ body =
          Fn fnv (map refinedVarOrFresh ts) body NotRec
                (ExprAnnot [] (MissingSourceRange "fnOfRefinement") [])

      refinedVarOrFresh t = case t of RefinedType rv _ _ -> rv
                                      _                  -> TypedId t frsh
      refinements = concatMap mbFnOfRefinement ts
  in
  refinements

genSkolem ty = liftM (TypedId ty) (lift $ ccFreshId $ T.pack ".skolem")

primName tid = T.unpack (identPrefix (tidIdent tid))

-- Returns an SMT expression summarizing the given expression.
checkBody :: KNMono -> Facts -> SC (Maybe (Ident -> SC SMTExpr))
checkBody expr facts =
  -- Calling scRunZ3 corresponds to checking/validating a precondition/assertion.
  --
  -- The ``facts`` variable holds assertions tied to control flow rather than
  -- value bindings. For example, ``if v then e1 else e2 end``
  -- checks ``e2`` after extending ``facts`` with the assertion ``not v``.
  --
  -- Returning something of the form
  --    ``withDecls facts $ \x -> return (foo x)``
  -- means that the given expression (if bound to x) satisifes the property (foo x).
  -- For example:
  --   * The literal 10 satisfies (x == 10).
  --   * A read from an array in which all values are bounded by y satisfies (x <= y).
  --   * A literal of length y satisfies (arrayLength x == y)
  --
  -- Checking of ``x = e1; e2`` proceeds as follows:
  --    * If checking ``e1`` reveals that it satisfies property foo
  --
  --    * Otherwise, ``e2`` is checked with a declaration for ``x``.
  case expr of
    KNLiteral ty (LitInt i) -> do
        return $ withDecls facts $ \x -> return $ smtId x === litOfSize (fromInteger $ litIntValue i) (intSizeBitsOf ty)
    KNLiteral _ (LitBool b) ->
        return $ withDecls facts $ \x -> return $ smtId x === (if b then SMT.true else SMT.false)
    KNLiteral     {} -> do liftIO $ putStrLn $ "no constraint for literal " ++ show expr
                           return Nothing
    KNVar         {} -> return Nothing
    KNKillProcess {} -> return Nothing
    KNTyApp       {} -> return Nothing
    KNTuple       {} -> return Nothing
    KNAllocArray  {} -> return Nothing

    KNArrayRead ty (ArrayIndex a i _ SG_Static) -> do
        --let precond = (sign_extend 32 (smtVar i)) `inRangeCO` (litOfSize 0 I64, smtArraySizeOf (smtVar a))
        let precond = bvult (zero_extend 32 (smtVar i)) (smtArraySizeOf (smtVar a))
        let thm = scriptImplyingBy' precond facts
        scRunZ3 expr (SMT.pp thm)
        -- If the array has an annotation, use it.
        mb_f <- scGetFact (tidIdent a)
        case mb_f of
          Nothing -> do liftIO $ putStrLn $ "no constraint on output of array read"
                        return Nothing
          Just f -> do liftIO $ putStrLn $ "have a constraint on output of array read: " ++ show (f (tidIdent a))
                       return $ withDecls facts $ \x -> return $ f x

    KNArrayRead ty (ArrayIndex a i _ SG_Dynamic) -> do
        -- If the array has an annotation, use it.
        mb_f <- scGetFact (tidIdent a)
        case mb_f of
          Nothing -> do liftIO $ putStrLn $ "no constraint on output of array read"
                        return Nothing
          Just f -> do liftIO $ putStrLn $ "have a constraint on output of array read: " ++ show (f (tidIdent a))
                       return $ withDecls facts $ \x -> return $ f x


    KNArrayPoke ty (ArrayIndex a i _ _) v -> return Nothing

    KNArrayLit (ArrayType (PrimInt sz)) _v entries -> do
        {- TODO: attach this condition to the array itself, so that
                 the condition is asserted on the results of any reads from the array,
                 without needing to use a universal quantifier... -}
        let arrayReadResultConstraint id =
                case staticArrayValueBounds entries of
                      Just (mn, mx) -> (smtId id) `inRangeCC` (litOfSize mn sz, litOfSize mx sz)
                      Nothing -> SMT.true
        return $ withDecls facts $ \x -> do
                    scAddFact x arrayReadResultConstraint
                    return $ (smtArraySizeOf (smtId x) === litOfSize (fromIntegral $ length entries) I64)

    KNArrayLit {} -> return Nothing

    KNAlloc       {} -> return Nothing
    KNStore       {} -> return Nothing
    KNDeref       {} -> return Nothing

    KNCallPrim _ (NamedPrim tid) _  | primName tid `elem` ["print_i32", "expect_i32"] -> do
        return $ Nothing

    KNCallPrim _ (NamedPrim tid) vs | primName tid `elem` ["assert-invariants"] -> do
        let precond = smtAll (map smtVar vs)
        let thm = scriptImplyingBy' precond facts
        scRunZ3 expr (SMT.pp thm)
        return $ Nothing

    KNCallPrim _ (NamedPrim tid) [v] | primName tid `elem` ["prim_arrayLength"] -> do
        return $ withDecls facts $ \x -> return $ smtId x === smtArraySizeOf (smtVar v)

    KNCallPrim (PrimInt szr) (PrimOp ('s':'e':'x':'t':'_':_) (PrimInt szi)) [v] -> do
        return $ withDecls facts $ \x -> return $ smtId x === sign_extend (fromIntegral $ intSizeOf szr - intSizeOf szi) (smtVar v)

    KNCallPrim (PrimInt szr) (PrimOp ('z':'e':'x':'t':'_':_) (PrimInt szi)) [v] -> do
        return $ withDecls facts $ \x -> return $ smtId x === zero_extend (fromIntegral $ intSizeOf szr - intSizeOf szi) (smtVar v)

    KNCallPrim _ (PrimOp opname (PrimInt _)) vs | Just op <- Map.lookup opname fnMap -> do
        return $ withDecls facts $ \x -> return $ smtId x === lift2 op (smtVars vs)

    KNCallPrim _ (PrimOp "bitshl" (PrimInt _)) vs -> do
        -- TODO check 2nd var <= sz
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvshl (smtVars vs)

    KNCallPrim _ (PrimOp "bitlshr" (PrimInt _)) vs -> do
        -- TODO check 2nd var <= sz
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvlshr (smtVars vs)

    KNCallPrim _ (PrimOp "bitashr" (PrimInt _)) vs -> do
        -- TODO check 2nd var <= sz
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvashr (smtVars vs)

    KNCallPrim _ (PrimIntTrunc _ tosz) [v] -> do
        return $ withDecls facts $ \x -> return $ smtId x === smtTruncToSize (intSizeOf tosz) (smtVar v)

    KNCallPrim (PrimInt _) (PrimOp "sdiv-unsafe" (PrimInt sz)) vs -> do
        let precond [s1, s2] = s2 =/= (litOfSize 0 sz)
        let thm = scriptImplyingBy' (precond (smtVars vs)) facts
        scRunZ3 expr (SMT.pp thm)
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvsdiv (smtVars vs)

    KNCallPrim _ty prim vs -> do
        liftIO $ putStrLn $ "TODO: checkBody attributes for call prim " ++ show prim ++ " $ " ++ show vs
        return Nothing

    KNAppCtor     {} -> return Nothing
    KNInlined _t0 _to _tn _old new -> checkBody new facts
    KNCase        ty v arms     -> do
        -- TODO: better path conditions for individual arms
        _ <- forM arms $ \arm -> do
            case caseArmGuard arm of
                Nothing -> do facts' <- withBindings v (caseArmBindings arm) facts
                              checkBody (caseArmBody arm) facts'
                Just g -> error $ "can't yet support case arms with guards in KNStaticChecks"
        return Nothing
        --error $ "checkBody cannot yet support KNCase" -- KNCase ty v (map (fmapCaseArm id (q tailq) id) arms)
    KNIf          ty v e1 e2    -> do
        _ <- checkBody e1 (facts `withPathFact` (        (smtVar v)))
        _ <- checkBody e2 (facts `withPathFact` (SMT.not (smtVar v)))
        return Nothing

    KNCall ty v vs -> do
        -- Do any of the called function's args have preconditions?
        case tidType v of
          FnType formals _ _ _ -> do
            forM_ (zip formals vs) $ \(formalTy, arg) -> do
              case formalTy of
                FnType {} ->
                  liftIO $ putStrLn "check precondition implication (TODO!)"
                  {-
                  case (monoFnPrecondition formalTy, monoFnPrecondition (tidType arg)) of
                    (HavePrecondition pf, HavePrecondition pa) -> do
                      skolems <- mapM genSkolem (monoFnTypeDomain formalTy)
                      smt_f <- (mkPrecondGen facts $ unLetFn pf) skolems
                      smt_a <- (mkPrecondGen facts $ unLetFn pa) skolems
                      let smte = mergeSMTExpr (\ef ea -> ef SMT.==> ea) smt_f smt_a
                      let thm  = scriptImplyingBy smte facts
                      liftIO $ do res <- ccRunZ3 (SMT.pp thm)
                                  putStrLn $ "precondition implication " ++ show (SMT.pp thm) ++ ": "
                                  putZ3Result res
                    _ -> return ()
                  -}
                _ -> return ()
          _ -> return ()

        liftIO $ putStrLn $ "KNCall " ++ show (pretty expr)
        -- Does the called function have a precondition?
        -- See also mkPrecondGen / compilePreconditionFn
        case fromMaybe [] $ getMbFnPreconditions facts (tidIdent v) of
          [] -> do
            liftIO $ putStrLn $ "TODO: call of function with result type " ++ show ty ++ " ; " ++ show (v)
            liftIO $ putStrLn $ "           (no precond)"
            return Nothing
          fps -> do
            liftIO $ putStrLn $ "TODO: call of function with result type " ++ show ty ++ " ; " ++ show (tidIdent v)
            liftIO $ putStrLn $ "           (have precond)"
            let checkPrecond fp = do
                SMTExpr e decls idfacts <- fp vs
                liftIO $ putStrLn $ "checkPrecond[ " ++ show vs ++ " ] " ++ show (SMT.pp e) ++ ";;;;;" ++ show idfacts
                --let thm = scriptImplyingBy expr (mergeFactsForCompilation facts efacts)
                let thm = scriptImplyingBy (SMTExpr e decls idfacts)  facts
                liftIO $ putStrLn $ "fn precond checking this script:"
                liftIO $ putStrLn $ show (SMT.pp thm)
                scRunZ3 expr (SMT.pp thm)
            mapM_ checkPrecond fps
            return Nothing

    KNLetVal      id   e1 e2    -> do
        liftIO $ putStrLn $ "letval checking bound expr for " ++ show id
        liftIO $ putStrLn $ "    " ++ show e1

        facts0 <-
         case typeKN e1 of
          RefinedType v e args -> do
              liftIO $ putStrLn $ "*#*#*#*#*#*#**#*#*#* bound a refined var, adding a fact? " ++ show args
              liftIO $ putStrLn $ show id
              liftIO $ putStrLn $ show v
              liftIO $ putStrLn $ show e
              -- Conjure up a name for the overall value of the refinement expr.

              resid <- lift $ ccFreshId $ T.pack ".true"
              -- Compute an SMT expression representing ``expr'',
              -- in an environment unaffected by ``blah``.

              liftIO $ putStrLn $ "KNLetVal -> RefinedType -> pre check"
              mb_f2 <- checkBody e facts
              liftIO $ putStrLn $ "KNLetVal -> RefinedType -> mid check"
              (SMTExpr body decls idfacts) <- (trueOr mb_f2) resid

              liftIO $ putStrLn $ "KNLetVal -> RefinedType -> post check"
              liftIO $ putStrLn $ show (id, tidIdent v)
              liftIO $ putStrLn $ show $ text "     body:    " <> pretty body
              liftIO $ putStrLn $ show $ text "     idfacts: " <> pretty idfacts

              let idfacts' = extendIdFacts resid body [(id, tidIdent v)] idfacts

              let facts'0 = addSymbolicVar facts v
              let facts'1 = addSymbolicVar facts'0 (TypedId (PrimInt I1) resid)
              let facts'2 = addIdentFacts''' facts'1 idfacts'
              let facts'3 = addSymbolicDecls facts'2 decls
              return $ facts'3 `withPathFact` (smtId resid)

              --return $ (addSymbolicVar ( ) v) `withPathFact` (smtId resid)
              {-return $ (flip addSymbolicVar v $
                         addIdentFact'''
                          (addIdentFact'' facts resid body (PrimInt I1))
                          id (idsEq (id, tidIdent v))) `withPathFact` (smtId resid)-}
{-
              -- Assert the truthiness of the refinement expr,
              -- given that id and v are the same.
              let idfacts' = extendIdFacts resid body [(id, tidIdent v)] idfacts
              let smtexpr = SMTExpr (smtId resid) decls idfacts'
              -- Note this starts from facts', not facts.
              -- The latter *is* affected by ``blah``.
              let facts''  = foldl' addSymbolicVar facts'  [v, TypedId (PrimInt I1) resid]
              let thm = scriptImplyingBy smtexpr facts''
              scRunZ3 expr (SMT.pp thm)
              -}
          _ -> return facts

        mb_f <- checkBody e1 facts
        case mb_f of
          Nothing -> do liftIO $ putStrLn $ "  no fact for id binding " ++ show id
                        liftIO $ putStrLn $ "       with type " ++ show (pretty (typeKN e1))
                        checkBody e2 (addSymbolicVar facts0 (TypedId (typeKN e1) id))
          Just f  -> do liftIO $ putStrLn $ "have fact for id binding " ++ show id
                        newfact@(SMTExpr _body _decls _idfacts) <- f id
                        liftIO $ putStrLn $ "        body: " ++ show (pretty _body)
                        liftIO $ putStrLn $ "        idfacts: " ++ show (pretty _idfacts)
                        let facts' = addIdentFact facts0 id newfact (typeKN e1)
                        whenRefined (typeKN e1) $ \_v _e ->
                            liftIO $ putStrLn $ "letval validating refinement: " ++ show (pretty (typeKN e1)) ++ show (pretty (_v, _e))
                        whenRefined (typeKN e1) $ validateRefinement facts facts' id
                        liftIO $ putStrLn $ "letval checking letval body after binding " ++ show id
                        checkBody e2 facts'

    KNLetFuns     [id] [fn] b | identPrefix id == T.pack "assert-invariants-thunk" -> do
        checkFn'  fn facts
        checkBody b  facts
        return Nothing

    KNLetRec      ids es  b     ->
        error $ "KNStaticChecks.hs: checkBody can't yet support recursive non-function bindings."

    KNLetFuns     ids fns b     -> do
        facts' <- foldlM (\facts (id, fn) -> recordIfHasFnPrecondition facts id (fnType fn))
                           facts (zip ids fns)
        mapM_ (\fn -> checkFn' fn facts') fns
        checkBody b facts'

    KNCompiles (KNCompilesResult resvar) _t e -> do
        res <- scIntrospect (checkBody e facts)
        case res of
          Left  {} -> do liftIO $ writeIORef resvar False
                         return $ Nothing
          Right {} -> do return $ Nothing

runCompiled :: Compiled x -> CompilerContext -> IO (Either CompilerFailures x)
runCompiled action state = runErrorT $ evalStateT action state

compiledIntrospect :: Compiled x -> Compiled (Either CompilerFailures x)
compiledIntrospect action = do state <- get
                               liftIO $ runCompiled action state

scIntrospect :: SC x -> SC (Either CompilerFailures x)
scIntrospect action = do state <- get
                         lift $ compiledIntrospect (evalStateT action state)

whenRefined ty f =
  case ty of
    RefinedType v e _ -> f v e
    _                 -> return ()

-- For a binding id : (% v : expr) = blah,
-- we must ensure that the value computed by blah
-- will satisfy the refinement expr.
validateRefinement facts facts' id v expr = do
  -- Conjure up a name for the overall value of the refinement expr.
  resid <- lift $ ccFreshId $ T.pack "letres"
  -- Compute an SMT expression representing ``expr'',
  -- in an environment unaffected by ``blah``.
  mb_f2 <- checkBody expr facts
  (SMTExpr body decls idfacts) <- (trueOr mb_f2) resid
  -- Assert the truthiness of the refinement expr,
  -- given that id and v are the same.
  let idfacts' = extendIdFacts resid body [(id, tidIdent v)] idfacts
  let smtexpr = SMTExpr (smtId resid) decls idfacts'
  -- Note this starts from facts', not facts.
  -- The latter *is* affected by ``blah``.
  let facts''  = foldl' addSymbolicVar facts'  [v, TypedId (PrimInt I1) resid]
  let thm = scriptImplyingBy smtexpr facts''
  scRunZ3 expr (SMT.pp thm)

recordIfHasFnPrecondition facts id ty =
  case ty of
    FnType {} -> do
      liftIO $ putStrLn $ "computeRefinements for " ++ show (TypedId ty id) ++ " was " ++ show (computeRefinements (TypedId ty id))
      case computeRefinements (TypedId ty id) of
        [] -> return $ facts
        preconds -> return $ facts { fnPreconds = Map.insert id (map (mkPrecondGen facts) preconds) (fnPreconds facts) }
    _ -> return $ facts

mkPrecondGen :: Facts -> (Fn RecStatus KNMono MonoType) -> ([MoVar] -> SC SMTExpr)
mkPrecondGen facts fn = \argVars -> do
  uref <- lift $ gets ccUniqRef
  fn' <- liftIO $ alphaRename' fn uref
  lift $ evalStateT (compilePreconditionFn fn' facts argVars) (SCState Map.empty)

-- Implicit precondition: fn is alpha-renamed.
compilePreconditionFn fn facts argVars = do
  liftIO $ putStrLn $ "compilePreconditionFn<" ++ show (length argVars) ++ " vs " ++ show (length (fnVars fn)) ++ " # " ++ show argVars ++ "> ;; " ++ show fn
  resid <- lift $ ccFreshId $ identPrefix $ fmapIdent (T.append (T.pack "res$")) $ tidIdent (fnVar fn)
  let facts' = foldl' addSymbolicVar facts ((TypedId (PrimInt I1) resid):(argVars ++ fnVars fn))
  facts'' <- foldlM recordIfTidHasFnPrecondition facts' (fnVars fn)
  bodyf <- checkBody (fnBody fn) facts''
  (SMTExpr body decls idfacts) <- (trueOr bodyf) resid
  let idfacts' = extendIdFacts resid body (zip (map tidIdent argVars)
                                               (map tidIdent $ fnVars fn)) idfacts
  return $ SMTExpr (smtId resid) decls idfacts'

-- Adds ``body`` as an associated fact of ``resid``,
-- and adds pairwise equality facts assoc w/ ``map fst equalIds``.
extendIdFacts resid body equalIds idfacts =
    foldl' (\idfacts (av,fv) -> (av, idsEq (av,fv)) : idfacts)
           ((resid, body):idfacts)
           equalIds

trueOr Nothing  = \id -> return $ bareSMTExpr (smtId id === SMT.true)
trueOr (Just f) = f

bareSMTExpr e = SMTExpr e Set.empty []

idsEq  (v1, v2) = smtId  v1 === smtId  v2

getMbFnPreconditions facts id = Map.lookup id (fnPreconds facts)