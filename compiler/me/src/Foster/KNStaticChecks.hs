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
import Foster.Output(putDocLn)

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T

import Control.Monad.Error(throwError, runErrorT, ErrorT)
import Control.Monad.State(gets, liftIO, evalStateT, StateT,
                           forM, forM_, get, put, lift)

import qualified SMTLib2 as SMT
import           SMTLib2(app, Script(..), Command(..), Option(..), Type(..))
import qualified SMTLib2.Core as SMT
import           SMTLib2.Core(tBool, (===), (=/=))
import SMTLib2.BitVector

import Foster.RunZ3 (runZ3)

--------------------------------------------------------------------

newtype CommentedScript = CommentedScript [CommentOrCommand]
data CommentOrCommand = Cmnt String | Cmds [Command]

data SymDecl = SymDecl SMT.Name [SMT.Type] SMT.Type

data SMTExpr = SMTExpr SMT.Expr (Set SymDecl) [(Ident, SMT.Expr)]

mergeSMTExprAsPathFact (SMTExpr e s m) (Facts preconds identfacts pathfacts decls) =
  Facts preconds (m ++ identfacts) (e:pathfacts) (Set.union s decls)

data Facts = Facts { fnPreconds :: Map Ident [[MoVar] -> SC SMTExpr]
                   , identFacts :: [(Ident, SMT.Expr)]
                   , pathFacts  :: [SMT.Expr]
                   , symbolicDecls :: Set SymDecl
                   }
------

-- {{{ Utility functions for SMT names and types
nm id = SMT.N (map cleanChar $ show id)
  where cleanChar c = case c of
                         '.' -> '_'
                         '/' -> '_'
                         '!' -> '_'
                         ':' -> '_'
                         _ -> c

ident :: Ident -> SMT.Ident
ident id = SMT.I (nm id) []

smtId  id  = app (ident id) []
smtVar tid = smtId (tidIdent tid)

smtVars tids = map smtVar tids

smtNameI :: SMT.Ident -> SMT.Name
smtNameI (SMT.I nm _) = nm

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

-- Oddly, Z3 equates type Bool with type (_ BitVec 1),
-- but doesn't equate the literals for the two types!
litOfSize num I1 = if num == 0 then SMT.false else SMT.true
litOfSize num sz = bv num (fromIntegral $ intSizeOf sz)

-- inRangeCO x (a, b) = bvsge x a `SMT.and` bvslt x b
inRangeCC x (a, b) = bvsge x a `SMT.and` bvsle x b

smtI s = SMT.I (SMT.N s) []

smtArraySizeOf x = app (smtI "foster$arraySizeOf") [x]
-- }}}

-- {{{ Adding ident facts etc
insertIdentFact id expr idfacts =
  -- trace (show (text "insertIdentFact" <+> indent 4 (vsep [pretty (id,expr), pretty idfacts]))) $
  (id, expr):idfacts

addIdentFact facts id (SMTExpr expr _ _) ty =
  addSymbolicVar (addIdentFact''' facts id expr) (TypedId ty id)

addIdentFact''' facts id expr =
    facts { identFacts = insertIdentFact id expr (identFacts facts) }

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

withPathFact :: Facts -> SMT.Expr -> Facts
withPathFact  facts pathfact  = withPathFacts facts [pathfact]
withPathFacts facts pathfacts = facts { pathFacts = pathfacts ++ pathFacts facts }
-- }}}

scriptImplyingBy' :: SMT.Expr -> Facts -> CommentedScript
scriptImplyingBy' pred facts = scriptImplyingBy (bareSMTExpr pred) facts

scriptImplyingBy :: SMTExpr -> Facts -> CommentedScript
scriptImplyingBy (SMTExpr pred declset idfacts) facts =
  let uniquesWithoutPrims pairs =
        pairs `butnot` [(SMT.N "Bool", 0), (SMT.N "BitVec", 0),
                        (SMT.N "FosterArray", 0)]
      alldecls = Set.toList $ Set.union declset (symbolicDecls facts)
      alldecltys = concatMap (\(SymDecl _nm targs tret) -> tret:targs) alldecls
      tydecls  = [CmdDeclareType nm arity | (nm, arity) <-
                    uniquesWithoutPrims
                     [(smtNameI id, fromIntegral $ length tys)
                     | (TApp id tys) <- alldecltys]] in
  CommentedScript $ [Cmds $
           [CmdSetOption (OptProduceModels True)
           ,CmdSetLogic (SMT.N "QF_AUFBV")
           ,CmdDeclareType (SMT.N "FosterArray") 0
           ,CmdDeclareFun (SMT.N "foster$arraySizeOf") [smtArray] (tBitVec 64)
           ]
        ++ tydecls
        ++ map (\(SymDecl nm tys ty) -> CmdDeclareFun nm tys ty) alldecls
      ] ++ [Cmnt "path facts"]
        ++ [Cmds $ map CmdAssert (pathFacts facts)]
        ++ [Cmnt "facts preconds"]
        ++ [Cmds $ map CmdAssert (map snd $ identFacts facts)]
        ++ [Cmnt "expr preconds"]
        ++ [Cmds $ map CmdAssert (map snd $ idfacts)]
        ++ [Cmds $ [CmdPush 1]
                ++ [CmdAssert $ SMT.not pred]]

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

------

-- Errors will be propagated, while unsat (success) results are trivial...
scRunZ3 :: KNMono -> CommentedScript -> SC ()
scRunZ3 expr script = lift $ do
  let doc = prettyCommentedScript script
  res <- liftIO $ runZ3 (show doc) (Just "(pop 1)\n(check-sat)")
  case res of
    Left x -> throwError [text x, pretty expr, string (show doc)]
    Right ("unsat":"sat":_) -> return ()
    Right ["unsat","unsat"] -> do
        liftIO $ putStrLn $ "WARNING: scRunZ3 returning OK due to inconsistent context..."
        liftIO $ putStrLn $ "   This is either dead code or a buggy implementation of our SMT query generation."
        return ()
    Right strs -> throwError ([text "Unable to verify precondition associated with expression",
                               case maybeSourceRangeOf expr of
                                   Just sr -> prettyWithLineNumbers sr
                                   Nothing -> pretty expr,
                               string (show doc)] ++ map text strs)
  return ()

maybeSourceRangeOf (KNCallPrim sr _ _ _) = Just sr
maybeSourceRangeOf (KNTuple _ _ sr) = Just sr
maybeSourceRangeOf _ = Nothing

runStaticChecks :: ModuleIL KNMono MonoType -> Compiled ()
runStaticChecks m = do
  checkModuleExprs (moduleILbody m) (Facts Map.empty [] [] Set.empty)

checkModuleExprs :: KNMono -> Facts -> Compiled ()
checkModuleExprs expr facts =
  case expr of
    KNLetFuns     ids fns b -> do
        facts' <- foldlM (\facts (id, fn) -> recordIfHasFnPrecondition facts (TypedId (fnType fn) id))
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

      mbFnOfRefinement (RefinedType _ body _) =
          [Fn (fnVar fn) relevantFormals body NotRec
           (annotForRange (MissingSourceRange "fnOfRefinement"))]
      mbFnOfRefinement _                   = []

      refinements = concatMap mbFnOfRefinement (map tidType $ fnVars fn)
      foldPathFact facts f = do liftIO $ putStrLn $ "checkFn' calling smtEvalApp... {"
                                e <- smtEvalApp facts f relevantActuals
                                liftIO $ putStrLn $ "checkFn' called  smtEvalApp... }"
                                liftIO $ putDocLn $ pretty e
                                return $ mergeSMTExprAsPathFact e facts
  liftIO $ putStrLn $ "%%%%%%%%%%%%%%%%%%%%%%%%%%%"
  liftIO $ putStrLn $ "refinements: " ++ show (map pretty refinements)
  liftIO $ putStrLn $ "fnVars fn:   " ++ show (fnVars fn)
  liftIO $ putStrLn $ "relevantFormals: " ++ show relevantFormals
  liftIO $ putStrLn $ "relevantActuals: " ++ show relevantActuals

  -- Generates equalities between the refinements and the actuals
  -- (freshly-generated versions thereof for each refinement predicate).
  facts <- foldlM foldPathFact facts0 refinements

  -- Before processing the body, add declarations for the function formals,
  -- and record the preconditions associated with any function-typed formals.
  let facts' = foldl' addSymbolicVar facts (relevantFormals ++ fnVars fn)
  facts''  <- foldlM recordIfHasFnPrecondition facts' (fnVars fn)

  liftIO $ putDoc $ text "checking body " <$> indent 2 (pretty (fnBody fn)) <> line
  smtexpr <- checkBody (fnBody fn) facts''
  liftIO $ putStrLn $ "... checked body"
  -- We need to add declarations for the function variables to both the facts
  -- environment (for use in checks within the function) and the result
  -- (for use in checks outside the function definition).
  return $ foldl' addSymbolicVar'' smtexpr (fnVars fn)

smtEvalApp facts fn args = do
  (mkPrecondGen facts fn) args

lift2 f [x, y] = f x y
lift2 _ _ = error "KNStaticChecks.hs: lift2 passed a non-binary list of arguments"

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
        go _ _ =           error "KNStaticChecks.hs: staticArrayValueBounds expects literal int entries."
staticArrayValueBounds _ = error "KNStaticChecks.hs: staticArrayValueBounds expects literal int entries."

-- Wraps the SMT.Expr produced by ``f`` with the current facts to make an SMTExpr.
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

      mbFnOfRefinement (RefinedType _ body _) =
        [Fn fnv relevantFormals body NotRec (annotForRange (MissingSourceRange "fnOfRefinement"))]
      mbFnOfRefinement _                   = []

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
      frsh idx = Ident (T.pack $ "_" ++ show idx) 0 -- Well, fresh enough...?

      mbFnOfRefinement (RefinedType v e _) = [fnOfRefinement v e]
      mbFnOfRefinement _                   = []

      fnOfRefinement _ body =
          Fn fnv (map refinedVarOrFresh (zip ts [0..])) body NotRec
                (annotForRange (MissingSourceRange "fnOfRefinement"))

      refinedVarOrFresh (t,idx) = case t of RefinedType rv _ _ -> rv
                                            _                  -> TypedId t (frsh idx)
      refinements = concatMap mbFnOfRefinement ts
  in
  refinements

--genSkolem ty = liftM (TypedId ty) (lift $ ccFreshId $ T.pack ".skolem")

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
    KNVar v -> return $ withDecls facts $ \x -> return $ smtId x === smtVar v

    KNArrayRead _ty (ArrayIndex a i _ SG_Static) -> do
        --let precond = (sign_extend 32 (smtVar i)) `inRangeCO` (litOfSize 0 I64, smtArraySizeOf (smtVar a))
        let precond = bvult (zero_extend 32 (smtVar i)) (smtArraySizeOf (smtVar a))
        scRunZ3 expr $ scriptImplyingBy' precond facts
        -- If the array has an annotation, use it.
        mb_f <- scGetFact (tidIdent a)
        case mb_f of
          Nothing -> do liftIO $ putStrLn $ "no constraint on output of array read"
                        return Nothing
          Just f -> do liftIO $ putStrLn $ "have a constraint on output of array read: " ++ show (f (tidIdent a))
                       return $ withDecls facts $ \x -> return $ f x

    KNArrayRead _ty (ArrayIndex a _i _ _sg) -> do
        -- If the array has an annotation, use it.
        mb_f <- scGetFact (tidIdent a)
        case mb_f of
          Nothing -> do liftIO $ putStrLn $ "no constraint on output of array read"
                        return Nothing
          Just f -> do liftIO $ putStrLn $ "have a constraint on output of array read: " ++ show (f (tidIdent a))
                       return $ withDecls facts $ \x -> return $ f x


    KNArrayPoke _ty (ArrayIndex _a _i _ _) _v -> return Nothing

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

    KNArrayLit (ArrayType (RefinedType v e _ids)) _v entries -> do
        let resid = Ident (T.pack ".xyz") 0
            go entry = do
              liftIO $ putDocLn $ text "obeysRefinement"
              liftIO $ putDocLn $ text "         v:" <+> indent 2 (pretty v    )
              liftIO $ putDocLn $ text "         e:" <+> indent 2 (pretty e    )
              liftIO $ putDocLn $ text "     entry:" <+> indent 2 (pretty entry)

              mb_f2 <- checkBody e facts
              SMTExpr body decls idfacts <- (trueOr mb_f2) resid

              let smtRepr (Right v) = smtVar v
                  smtRepr (Left (LitInt li)) =
                            litOfSize (fromInteger $ litIntValue li) (intSizeBitsOf (tidType v))

              let idfacts' = extendIdFacts resid body [] idfacts
                  facts'1 = foldl' addSymbolicVar facts [v, TypedId (PrimInt I1) resid]
                  facts'2 = if null lostFacts then facts'1 { identFacts = idfacts' }
                                              else error $ "xdont wanna lose these facts! : " ++ (show (pretty lostFacts))
                  facts'3 = addSymbolicDecls facts'2 decls
                  facts'4 = facts'3 `withPathFact` (smtVar v === smtRepr entry)
                  lostFacts = (identFacts facts'1) `butnot` idfacts'

              let thm = scriptImplyingBy' (smtId resid) facts'4
              liftIO $ putStrLn "mach-array-lit w/ refinement type checking the following script:"
              liftIO $ putDocLn $ indent 4 (prettyCommentedScript thm)
              scRunZ3 expr thm
{-
              uref <- lift $ gets ccUniqRef
              (Fn v [] e _ _) <- liftIO $ alphaRename' (Fn v0 [] e0 undefined undefined) uref
              mb_f2 <- checkBody e facts
              resid <- lift $ ccFreshId $ T.pack ".true"
              (SMTExpr body decls idfacts) <- (trueOr mb_f2) resid
              let idfacts' = extendIdFacts resid body [(id, tidIdent v)] idfacts
              let facts'1 = foldl' addSymbolicVar facts [v, TypedId (PrimInt I1) resid]
              let lostFacts = (identFacts facts'1) `butnot` idfacts'
              let facts'2 = if null lostFacts then facts'1 { identFacts = idfacts' }
                                              else error $ "dont wanna lose these facts! : " ++ (show lostFacts)
              let facts'3 = addSymbolicDecls facts'2 decls
              return $ facts'3 `withPathFact` (smtId resid)

              let thm = scriptImplyingBy' SMT.true facts''
              liftIO $ putStrLn "mach-array-lit w/ refinement type checking the following script:"
              liftIO $ putStrLn $ show (prettyCommentedScript thm)

              -}
              return ()
        mapM_ go entries
        return $ Nothing

    KNArrayLit {} -> return Nothing

    KNCallPrim _ _ (NamedPrim tid) _  | primName tid `elem` ["print_i32", "expect_i32"] -> do
        return $ Nothing

    KNCallPrim _ _ (NamedPrim tid) vs | primName tid `elem` ["assert-invariants"] -> do
        let precond = smtAll (map smtVar vs)
        let thm = scriptImplyingBy' precond facts
        liftIO $ putStrLn "assert-invariants checking the following script:"
        liftIO $ putStrLn $ show (prettyCommentedScript thm)
        scRunZ3 expr thm
        return $ Nothing

    KNCallPrim _ _ (NamedPrim tid) [v] | primName tid `elem` ["prim_arrayLength"] -> do
        return $ withDecls facts $ \x -> return $ smtId x === smtArraySizeOf (smtVar v)

    KNCallPrim _ (PrimInt szr) (PrimOp ('s':'e':'x':'t':'_':_) (PrimInt szi)) [v] -> do
        return $ withDecls facts $ \x -> return $ smtId x === sign_extend (fromIntegral $ intSizeOf szr - intSizeOf szi) (smtVar v)

    KNCallPrim _ (PrimInt szr) (PrimOp ('z':'e':'x':'t':'_':_) (PrimInt szi)) [v] -> do
        return $ withDecls facts $ \x -> return $ smtId x === zero_extend (fromIntegral $ intSizeOf szr - intSizeOf szi) (smtVar v)

    KNCallPrim _ _ (PrimOp opname (PrimInt _)) vs | Just op <- Map.lookup opname fnMap -> do
        return $ withDecls facts $ \x -> return $ smtId x === lift2 op (smtVars vs)

    -- No need to check the shift width because the backend will apply a mask.
    KNCallPrim _ _ (PrimOp "bitshl" (PrimInt _)) vs -> do
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvshl (smtVars vs)

    KNCallPrim _ _ (PrimOp "bitlshr" (PrimInt _)) vs -> do
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvlshr (smtVars vs)

    KNCallPrim _ _ (PrimOp "bitashr" (PrimInt _)) vs -> do
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvashr (smtVars vs)

    KNCallPrim _ _ (PrimIntTrunc _ tosz) [v] -> do
        return $ withDecls facts $ \x -> return $ smtId x === smtTruncToSize (intSizeOf tosz) (smtVar v)

    KNCallPrim _ (PrimInt _) (PrimOp "sdiv-unsafe" (PrimInt sz)) vs -> do
        let precond [s1, s2] = s2 =/= (litOfSize 0 sz)
        scRunZ3 expr $ scriptImplyingBy' (precond (smtVars vs)) facts
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvsdiv (smtVars vs)

    KNCallPrim _ _ty prim vs -> do
        liftIO $ putStrLn $ "TODO: checkBody attributes for call prim " ++ show prim ++ " $ " ++ show vs
        return Nothing

    KNAppCtor     {} -> return Nothing
    KNInlined _t0 _to _tn _old new -> checkBody new facts
    KNCase       _ty v arms     -> do
        -- TODO: better path conditions for individual arms
        _ <- forM arms $ \arm -> do
            case caseArmGuard arm of
                Nothing -> do facts' <- withBindings v (caseArmBindings arm) facts
                              checkBody (caseArmBody arm) facts'
                Just _g -> error $ "can't yet support case arms with guards in KNStaticChecks"
        return Nothing

    KNIf        _ty v e1 e2    -> do
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
                liftIO $ putStrLn $ show (prettyCommentedScript thm)
                scRunZ3 expr thm
            mapM_ checkPrecond fps
            return Nothing

    KNLetVal      id   e1 e2    -> do
        liftIO $ putStrLn $ "letval checking bound expr for " ++ show id
        liftIO $ putStrLn $ "    " ++ show e1

        facts0 <- case typeKN e1 of
                      RefinedType v e _ -> do
                           compileRefinementBoundTo id v e facts
                      _ -> return facts

        -- Note: we intentionally use facts and not facts0 here...
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

    KNLetRec      _ids _es _b     ->
        error $ "KNStaticChecks.hs: checkBody can't yet support recursive non-function bindings."

    KNLetFuns     ids fns b     -> do
        facts' <- foldlM (\facts (id, fn) -> recordIfHasFnPrecondition facts (TypedId (fnType fn) id))
                           facts (zip ids fns)
        mapM_ (\fn -> checkFn' fn facts') fns
        checkBody b facts'

    KNCompiles (KNCompilesResult resvar) _t e -> do
        res <- scIntrospect (checkBody e facts)
        case res of
          Left  {} -> do liftIO $ writeIORef resvar False
                         return $ Nothing
          Right {} -> do return $ Nothing

    KNAlloc       {} -> return Nothing
    KNStore       {} -> return Nothing
    KNDeref       {} -> return Nothing

    KNKillProcess {} -> return Nothing
    KNTyApp       {} -> return Nothing
    KNTuple       {} -> return Nothing
    KNAllocArray  {} -> return Nothing

scIntrospect :: SC x -> SC (Either CompilerFailures x)
scIntrospect action = do state <- get
                         lift $ compiledIntrospect (evalStateT action state)
  where
    compiledIntrospect :: Compiled x -> Compiled (Either CompilerFailures x)
    compiledIntrospect action = do state <- get
                                   liftIO $ runCompiled action state

    runCompiled :: Compiled x -> CompilerContext -> IO (Either CompilerFailures x)
    runCompiled action state = runErrorT $ evalStateT action state


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
  -- Unlike facts, facts' *is* affected by ``blah``.
  let facts''  = foldl' addSymbolicVar facts'  [v, TypedId (PrimInt I1) resid]
  scRunZ3 expr $ scriptImplyingBy smtexpr facts''

recordIfHasFnPrecondition facts v@(TypedId ty id) =
  case ty of
    FnType {} -> do
      liftIO $ putDocLn $ text $ "computeRefinements for " ++ show v ++ " was "
      liftIO $ putDocLn $ indent 4 $ pretty (computeRefinements v)
      case computeRefinements v of
        [] -> return $ facts
        preconds -> return $ facts { fnPreconds = Map.insert id (map (mkPrecondGen facts) preconds) (fnPreconds facts) }
    _ -> return $ facts

mkPrecondGen :: Facts -> (Fn RecStatus KNMono MonoType) -> ([MoVar] -> SC SMTExpr)
mkPrecondGen facts fn = \argVars -> do
  uref <- lift $ gets ccUniqRef
  fn' <- liftIO $ alphaRename' fn uref
  lift $ evalStateT (compilePreconditionFn fn' facts argVars) (SCState Map.empty)

-- Implicit precondition: fn is alpha-renamed.
compilePreconditionFn :: Fn RecStatus KNMono MonoType -> Facts
                      -> [TypedId MonoType] -> SC SMTExpr
compilePreconditionFn fn facts argVars = do
  liftIO $ putStrLn $ "compilePreconditionFn<" ++ show (length argVars) ++ " vs " ++ show (length (fnVars fn)) ++ " # " ++ show argVars ++ "> ;; " ++ show fn
  resid <- lift $ ccFreshId $ identPrefix $ fmapIdent (T.append (T.pack "res$")) $ tidIdent (fnVar fn)
  let facts' = foldl' addSymbolicVar facts ((TypedId (PrimInt I1) resid):(argVars ++ fnVars fn))
  facts'' <- foldlM recordIfHasFnPrecondition facts' (fnVars fn)
  bodyf <- checkBody (fnBody fn) facts''
  (SMTExpr body decls idfacts) <- (trueOr bodyf) resid
  let idfacts' = extendIdFacts resid body (zip (map tidIdent argVars)
                                               (map tidIdent $ fnVars fn)) idfacts
  return $ SMTExpr (smtId resid) decls idfacts'

compileRefinementBoundTo id v0 e0 facts = do
  uref <- lift $ gets ccUniqRef
  (Fn v [] e _ _) <- liftIO $ alphaRename' (Fn v0 [] e0 undefined undefined) uref
  mb_f2 <- checkBody e facts
  resid <- lift $ ccFreshId $ T.pack ".true"
  (SMTExpr body decls idfacts) <- (trueOr mb_f2) resid
  let idfacts' = extendIdFacts resid body [(id, tidIdent v)] idfacts
  let facts'1 = foldl' addSymbolicVar facts [v, TypedId (PrimInt I1) resid]
  let lostFacts = (identFacts facts'1) `butnot` idfacts'
  let facts'2 = if null lostFacts then facts'1 { identFacts = idfacts' }
                                  else error $ "dont wanna lose these facts! : " ++ (show lostFacts)
  let facts'3 = addSymbolicDecls facts'2 decls
  return $ facts'3 `withPathFact` (smtId resid)

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

-- {{{ Pretty-printing and other instances
instance Ord SymDecl where compare (SymDecl n1 _ _) (SymDecl n2 _ _) = compare n1 n2
instance Eq  SymDecl where (==)    (SymDecl n1 _ _) (SymDecl n2 _ _) = (==)    n1 n2

instance Pretty SMT.Expr where pretty e = string (show $ SMT.pp e)
instance Pretty SMTExpr where
    pretty (SMTExpr e decls idfacts) =
          parens (text "SMTExpr" <+> pretty e <$>
                    indent 2 (vsep
                         [hang 4 $ text "decls =" <$> pretty (Set.toList decls)
                         ,hang 4 $ text "idfacts =" <$> pretty idfacts]))
instance Pretty SMT.Name where pretty x = string (show x)
instance Pretty SMT.Type where pretty x = string (show x)
instance Pretty SymDecl where
    pretty (SymDecl nm tys ty) =
          parens (text "SymDecl" <+> pretty nm <+> pretty tys <+> pretty ty)

instance Pretty CommentOrCommand where
  pretty (Cmds cmds) = string (show $ SMT.pp $ Script cmds)
  pretty (Cmnt str) = vcat [text ";" <+> text line | line <- lines str]

instance Pretty (Either Literal (TypedId MonoType))
  where pretty (Left lit) = pretty lit
        pretty (Right v) = pretty v


prettyCommentedScript :: CommentedScript -> Doc
prettyCommentedScript (CommentedScript items) =
  vsep $ map pretty items
-- }}}
