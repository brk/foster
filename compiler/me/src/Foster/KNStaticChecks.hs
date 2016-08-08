{-# LANGUAGE StandaloneDeriving, BangPatterns, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2014 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNStaticChecks (runStaticChecks) where

import Prelude hiding ((<$>))

import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Data.List(foldl')
import Data.Maybe(fromMaybe)
import Data.IORef(writeIORef, modifyIORef, IORef)

import Foster.MonoType
import Foster.Base
import Foster.KNUtil
import Foster.Config
import Foster.Output(putDocLn)

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T
import qualified Data.ByteString as BS

import Control.Monad.Trans.Except(runExceptT)
import Control.Monad.State(gets, liftIO, evalStateT, StateT,
                           forM, forM_, get, put, lift)

import qualified SMTLib2 as SMT
import           SMTLib2(app, Script(..), Command(..), Option(..), Type(..))
import qualified SMTLib2.Core as SMT
import           SMTLib2.Core(tBool, (===), (=/=))
import SMTLib2.BitVector

import Foster.RunZ3 (runZ3)

--------------------------------------------------------------------

data CommentedScript = CommentedScript [CommentOrCommand] SMT.Expr
data CommentOrCommand = Cmnt String | Cmds [Command]

data SymDecl = SymDecl SMT.Name [SMT.Type] SMT.Type

data SMTExpr = SMTExpr SMT.Expr (Set SymDecl) [(Ident, SMT.Expr)]

mergeSMTExprAsPathFact (SMTExpr e s m) (Facts preconds identfacts pathfacts decls) =
  Facts preconds (m ++ identfacts) (e:pathfacts) (Set.union s decls)

liftSMTExpr (SMTExpr e s m) f = SMTExpr (f e) s m

data Facts = Facts { fnPreconds :: Map Ident [[MoVar] -> SC SMTExpr]
                   , identFacts :: [(Ident, SMT.Expr)]
                   , pathFacts  :: [SMT.Expr]
                   , symbolicDecls :: Set SymDecl
                   }
------

-- {{{ Utility functions for SMT names and types
nm :: Ident -> SMT.Name
nm id = smtN (show id)

smtN :: String -> SMT.Name
smtN s = SMT.N (noLeadingDot $ map cleanChar s)
  where noLeadingDot ('.':xs) = '_':xs
        noLeadingDot other    = other
        cleanChar c = if c `elem` "\"/:[]() " then '_' else c

smtI s = SMT.I (smtN s) []

-- Precondition: s must be a valid SMT identifier.
smtI_ s = SMT.I (SMT.N s) []

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
smtType (TupleType  tys) = TApp (smtI ("FosterTuple" ++ show (length tys))) (map smtType tys)
smtType (StructType tys) = TApp (smtI ("FosterTuple" ++ show (length tys))) (map smtType tys)
smtType (RefinedType v _ _) = smtType (tidType v)
smtType (TyApp (TyCon "Float64") []) = TApp (smtI_ "$Float64") []
smtType (TyApp (TyCon nm) tys) = TApp (smtI nm) (map smtType tys)
smtType (PtrType t) = TApp (smtI_ "$Ptr") [smtType t]
smtType (FnType ds rt _cc _pf) = TApp (smtI $ "$Fn_" ++ show (pretty rt)) (map smtType ds)
smtType (PtrTypeUnknown) = TApp (smtI_ "$Ptr_") []
smtType (CoroType a b) = TApp (smtI_ "$Coro") [smtType a, smtType b]
smtType other = error $ "smtType unable to handle " ++ show other

smtArray = TApp (smtI_ "FosterArray") []

smtTruncToSize i v = extract (fromIntegral i - 1) 0 v

-- Oddly, Z3 equates type Bool with type (_ BitVec 1),
-- but doesn't equate the literals for the two types!
litOfSize num I1 = if num == 0 then SMT.false else SMT.true
litOfSize num sz = bv num (fromIntegral $ intSizeOf sz)

-- inRangeCO x (a, b) = bvsge x a `SMT.and` bvslt x b
inRangeCC x (a, b) = bvsge x a `SMT.and` bvsle x b

smtArraySizeOf x = app (smtI "foster$arraySizeOf") [x]
-- }}}

-- {{{ Adding ident facts etc
insertIdentFact id expr idfacts =
  -- trace (show (text "insertIdentFact" <+> indent 4 (vsep [pretty (id,expr), pretty idfacts]))) $
  (id, expr):idfacts

addIdentFact facts id (SMTExpr expr decls _) ty =
  addSymbolicDecls
   (addSymbolicVars (addIdentFact''' facts id expr) [TypedId ty id]) decls

addIdentFact''' facts id expr =
    facts { identFacts = insertIdentFact id expr (identFacts facts) }

mkSymbolicVar :: TypedId MonoType -> SymDecl
mkSymbolicVar v = d
  where id = tidIdent v
        d  = case tidType v of
                FnType dom rng _ _ ->
                      SymDecl (nm id) (map smtType dom) (smtType rng)
                ty -> SymDecl (nm id) []                (smtType ty)

addSymbolicVars facts vs = facts { symbolicDecls = Set.union (Set.fromList (map mkSymbolicVar vs)) (symbolicDecls facts) }
addSymbolicDecls facts decls = facts { symbolicDecls = Set.union decls (symbolicDecls facts) }

withPathFact :: Facts -> SMT.Expr -> Facts
withPathFact  facts pathfact  = withPathFacts facts [pathfact]
withPathFacts facts pathfacts = facts { pathFacts = pathfacts ++ pathFacts facts }
-- }}}

-- According to de Moura at http://stackoverflow.com/questions/7411995/support-for-aufbv
-- it's better to use either UFBV or QF_AUFBV, rather than AUFBV...
-- the former is more useful for us.
-- TODO investigate Z3's newish support for floating-point numbers (QF_FPABV).
-- Maybe we want (set-option :int-real-coercions false) ?
--               (set-option :error-behavior immediate-exit) ?
-- Also, we carefully avoid doing multiple (check-sat)s per query or using
-- push/pop, because those features trigger Z3's incremental solver, which does
-- not accelerate bitvector queries, leading to 2+ orders of magnitude slowdown.
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
  CommentedScript [Cmds $
           [CmdSetOption (OptProduceModels True)
           ,CmdSetLogic (SMT.N "UFBV")
           ,CmdDeclareType (SMT.N "FosterArray") 0
           ,CmdDeclareFun (SMT.N "foster$arraySizeOf") [smtArray] (tBitVec 64)
           ]
        ++ tydecls
        ++ map (\(SymDecl nm tys ty) -> CmdDeclareFun nm tys ty) alldecls
       ,Cmnt "path facts"
       ,Cmds $ map CmdAssert (pathFacts facts)
       ,Cmnt "facts preconds"
       ,Cmds $ map CmdAssert (map snd $ identFacts facts)
       ,Cmnt "expr preconds"
       ,Cmds $ map CmdAssert (map snd $ idfacts)
       ]
       (SMT.not pred)

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
, scSMTStats :: IORef (Int, [(Double, Double)])
}

scAddFact id k = do
  sc <- get
  put $ sc { scExtraFacts = Map.insert id k (scExtraFacts sc) }

scGetFact id = do
  sc <- get
  return $ Map.lookup id (scExtraFacts sc)

------

-- Errors will be propagated, while unsat (success) results are trivial...
scRunZ3 :: KNMonoLike monolike => monolike -> CommentedScript -> SC ()
scRunZ3 expr script@(CommentedScript items _) = do
 smtStatsRef <- gets scSMTStats
 lift $ do
  let doc = prettyCommentedScript script
  (time, res) <- liftIO $ ioTime $ runZ3 (show doc) (Just "(get-model)")
  liftIO $ if (time > 0.9)
             then do
                putDocLn $ text "the following script took more than 900ms to verify:"
                putDocLn $ doc
             else return ()
  case res of
    Left x -> do compiledThrowE [text x, knMonoLikePretty expr, lineNumberedDoc doc]
    Right ["unsat"] -> do
      -- Run the script again, but without the target asserted.
      -- If the result remains unsat, then the context was inconsistent.
      -- If the result becomes sat, then the context was not inconsistent.
      (time', res') <- liftIO $ ioTime $ runZ3 (show $ vcat (map pretty items)) Nothing
      case res' of
        Left x -> compiledThrowE [text x, knMonoLikePretty expr, string (show doc)]
        Right ["sat"] -> do liftIO $ modifyIORef smtStatsRef (\(c, ts) -> (c + 1, (time, time'):ts))
                            return ()
        Right ["unsat"] -> do
         dbgStr $ "WARNING: scRunZ3 returning OK due to inconsistent context..."
         dbgStr $ "   This is either dead code or a buggy implementation of our SMT query generation."
         return ()
        Right strs -> do
         compiledThrowE $ [text "Removing the target assertion resulted in an invalid SMT query?!?"] ++ map text strs
    Right strs -> compiledThrowE ([text "Unable to verify precondition or postcondition associated with expression",
                               case maybeSourceRangeOf expr of
                                   Just sr -> prettyWithLineNumbers sr
                                   Nothing -> knMonoLikePretty expr,
                               lineNumberedDoc doc] ++ lineNumberedDocs strs)
  return ()

intLog10 n | n < 10 = 1
intLog10 n = intLog10 ((n `div` 10)) + 1

lineNumberedDoc doc = vcat (lineNumberedDocs $ lines (show doc))

lineNumberedDocs strings =
  let paddingSize = intLog10 (length strings) in
  [padded n paddingSize <> text ": " <+> text s | (n, s) <- (zip [(1::Int)..] strings)]

padded n k = (text $ replicate (k - (intLog10 n)) ' ' ) <> pretty n

class KNMonoLike e where
  maybeSourceRangeOf :: e -> Maybe SourceRange
  knMonoLikePretty :: e -> Doc

instance KNMonoLike (Fn RecStatus KNMono MonoType) where
  knMonoLikePretty e = pretty e
  maybeSourceRangeOf fn = Just (rangeOf $ fnAnnot fn)

instance KNMonoLike KNMono where
  knMonoLikePretty e = pretty e

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

    {-
dbgStr x = liftIO $ putStrLn x
dbgDoc x = liftIO $ putDocLn x
-}
dbgStr _x = return ()
dbgDoc _x = return ()

checkFn :: (Fn RecStatus KNMono MonoType) -> Facts -> Compiled (Maybe (Ident -> SC SMTExpr))
checkFn fn facts = do
  qref <- gets ccSMTStats
  evalStateT (checkFn' fn facts) (SCState Map.empty qref)

checkFn' fn facts0 = do
  facts'   <- withBindings (fnVar fn) (fnVars fn) facts0
  facts''  <- foldlM recordIfHasFnPrecondition facts' (fnVars fn)

  dbgIf dbgCheckFn $ text "checking body " <$> indent 2 (pretty (fnBody fn))
  f <- checkBody (fnBody fn) facts''
  dbgIf dbgCheckFn $ text "... checked body"

  whenRefined (monoFnTypeRange $ fnType fn) $ \v e -> do
    -- An expression summarizing our static knowledge of the fn body/return value.
    se <- case f of
            Nothing -> do
              dbgIf dbgCheckFn $ text "no refinement known for body"
              return $ bareSMTExpr SMT.true
            Just ft -> do
              rr <- ft (tidIdent v)
              dbgIf dbgCheckFn $ text "refinement for body: " <> pretty rr
              return rr

    let postcondId = Ident (T.pack ".postcond") 0
    f' <- checkBody e facts''
    se' <- case f' of
                Nothing -> do
                  dbgIf dbgCheckFn $ text "fn refinement checked, no extra refinement"
                  return $ bareSMTExpr SMT.true
                Just ff -> do
                  rr <- ff postcondId
                  dbgIf dbgCheckFn $ text "fn refinement checked: " <> pretty rr
                  return rr
    -- An expression of the form (v == ...)

    let thm = scriptImplyingBy (liftSMTExpr se (\body -> body SMT.==> smtId postcondId))
                               ((mergeSMTExprAsPathFact se' facts'')
                                 `addSymbolicVars` [v, TypedId boolMonoType postcondId])
    scRunZ3 fn thm

  return f


-- Return a modified facts environment which asserts (as path facts)
-- any refinements associated with the given list of binders.
withBindings :: TypedId MonoType -> [TypedId MonoType] -> Facts -> SC Facts
withBindings fnv vs facts0 = do
  -- For example, given f = { x : (% z : Int32 : ...) => y : Int32 => x + y }
  -- the relevant formals are [z] and the relevant actuals are [x].
  let (relevantFormals, relevantActuals) =
        unzip $ Prelude.concat [case tidType v of RefinedType v' _ _ -> [(v', v)]
                                                  _                  -> []
                               | v <- vs]

      -- To handle dependent refinements, each predicate takes all the fnvars...
      mbFnOfRefinement (RefinedType _ body _) =
        [Fn fnv relevantFormals body NotRec (annotForRange (MissingSourceRange "fnOfRefinement"))]
      mbFnOfRefinement _                   = []

      refinements = concatMap mbFnOfRefinement (map tidType vs)
      foldPathFact facts f = do dbgStr $ "withBindings calling smtEvalApp... { "
                                e <- smtEvalApp facts f relevantActuals
                                dbgStr $ "withBindings called  smtEvalApp... } "
                                return $ mergeSMTExprAsPathFact e facts
  facts <- foldlM foldPathFact facts0 refinements

  --dbgStr $ "%%%%%%%%%%%%%%%%%%%%%%%%%%%"
  --dbgStr $ "refinements: " ++ show (map pretty refinements)
  --dbgStr $ "fnVars fn:   " ++ show (fnVars fn)
  --dbgStr $ "relevantFormals: " ++ show relevantFormals
  --dbgStr $ "relevantActuals: " ++ show relevantActuals

  -- Before processing the body, add declarations for the function formals,
  -- and record the preconditions associated with any function-typed formals.
  let facts' = addSymbolicVars facts vs
  return facts'


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
  --   * An array literal of length y satisfies (arrayLength x == y)
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
    KNLiteral _ (LitByteArray bs) -> -- TODO: handle refinements?
        return $ withDecls facts $ \x ->
            return $ (smtArraySizeOf (smtId x) === litOfSize (fromIntegral $ BS.length bs) I64)

    KNLiteral     {} -> do dbgStr $ "no constraint for literal " ++ show expr
                           return Nothing

    KNVar v ->
       case tidType v of
         -- Gotta eta-expand to comply with restrictions on SMT-LIB 2 formulae.
         FnType ts _ _ _ -> do let ss = map (\c -> (c:[])) "abcdefghijklmnopqrstuvwxyz"
                               let sts = let zipTruncating = zip in  zipTruncating ss ts
                               let xs = map (\(s,_) -> app (SMT.I (smtN s) []) []) sts
                               return $ withDecls (addSymbolicVars facts [v]) $ \x -> return $
                                 SMT.Quant SMT.Forall [SMT.Bind (smtN s) (smtType t) | (s,t) <- sts]
                                                      (SMT.app (ident x) xs === SMT.app (ident (tidIdent v)) xs)
         _ -> return $ withDecls facts $ \x -> return $ smtId x === smtVar v

    KNArrayRead _ty (ArrayIndex a i _ sg) -> do
        case sg of
          SG_Static -> do
                  let precond = bvult (zero_extend 32 (smtVar i)) (smtArraySizeOf (smtVar a))
                  scRunZ3 expr $ scriptImplyingBy' precond facts
          _ -> return ()

        -- If the array has an annotation, use it.
        mb_f <- scGetFact (tidIdent a)
        case mb_f of
          Nothing -> do dbgStr $ "no constraint on output of array read"
                        return Nothing
          Just f -> do dbgStr $ "have a constraint on output of array read: " ++ show (f (tidIdent a))
                       return $ withDecls facts $ \x -> return $ f x


    KNArrayPoke _ty (ArrayIndex _a _i _ _) _v -> return Nothing

    KNAllocArray _ty v _amr _zi ->
        return $ withDecls facts $ \x -> do
                    return $ (smtArraySizeOf (smtId x) === sign_extend 32 (smtVar v))

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
              --dbgDoc $ text "obeysRefinement"
              --dbgDoc $ text "         v:" <+> indent 2 (pretty v    )
              --dbgDoc $ text "         e:" <+> indent 2 (pretty e    )
              --dbgDoc $ text "     entry:" <+> indent 2 (pretty entry)

              mb_f2 <- checkBody e facts
              SMTExpr body decls idfacts <- (trueOr mb_f2) resid

              let smtRepr (Right v) = smtVar v
                  smtRepr (Left (LitInt li)) =
                            litOfSize (fromInteger $ litIntValue li) (intSizeBitsOf (tidType v))
                  smtRepr (Left lit) = error $ "KNStaticChecks: smtRepr can't yet handle " ++ show lit

              let idfacts' = extendIdFacts resid body [] idfacts
                  facts'1 = addSymbolicVars facts [v, TypedId (PrimInt I1) resid]
                  facts'2 = if null lostFacts then facts'1 { identFacts = idfacts' }
                                              else error $ "xdont wanna lose these facts! : " ++ (show (pretty lostFacts))
                  facts'3 = addSymbolicDecls facts'2 decls
                  facts'4 = facts'3 `withPathFact` (smtVar v === smtRepr entry)
                  lostFacts = (identFacts facts'1) `butnot` idfacts'

              let thm = scriptImplyingBy' (smtId resid) facts'4
              --dbgStr "mach-array-lit w/ refinement type checking the following script:"
              --dbgDoc $ indent 4 (prettyCommentedScript thm)
              scRunZ3 expr thm
        mapM_ go entries

        return $ withDecls facts $ \x ->
            return $ (smtArraySizeOf (smtId x) === litOfSize (fromIntegral $ length entries) I64)

    KNArrayLit _ty _v entries ->
        return $ withDecls facts $ \x ->
            return $ (smtArraySizeOf (smtId x) === litOfSize (fromIntegral $ length entries) I64)

    KNCallPrim _ _ (NamedPrim tid) _  | primName tid `elem` ["print_i32", "expect_i32"] -> do
        return $ Nothing

    KNCallPrim _ _ (NamedPrim tid) vs | primName tid `elem` ["assert-invariants"] -> do
        scRunZ3 expr $ scriptImplyingBy' (smtAll (map smtVar vs)) facts
        return $ Nothing

    KNCallPrim _ _ (NamedPrim tid) [v] | primName tid `elem` ["prim_arrayLength"] -> do
        return $ withDecls facts $ \x -> return $ smtAll [smtId x === smtArraySizeOf (smtVar v)
                                                         ,smtId x `bvsge` bv 0 64]

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
        let precond [_s1, s2] = s2 =/= (litOfSize 0 sz)
            precond _ = error $ "KNStaticChecks: sdiv-unsafe requires exactly 2 args"
        scRunZ3 expr $ scriptImplyingBy' (precond (smtVars vs)) facts
        return $ withDecls facts $ \x -> return $ smtId x === lift2 bvsdiv (smtVars vs)

    KNCallPrim _ _ty prim vs -> do
        dbgStr $ "TODO: checkBody attributes for call prim " ++ show prim ++ " $ " ++ show vs
        return Nothing

    KNNotInlined _ e -> checkBody e facts
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
        mbf1 <- checkBody e1 (facts `withPathFact` (        (smtVar v)))
        mbf2 <- checkBody e2 (facts `withPathFact` (SMT.not (smtVar v)))
        let combine x = do
                se1 <- (maybeM mbf1) x
                se2 <- (maybeM mbf2) x
                return $ smtExprOr (smtExprAnd' se1 (smtVar v))
                                   (smtExprAnd' se2 (SMT.not (smtVar v)))
        return $ Just combine

    -- TODO we should return something involving the return-refinement type
    -- if the called function has one...
    KNCall ty v vs -> do
        -- Do any of the called function's args have preconditions?
        case tidType v of
          FnType formals _ _ _ -> do
            forM_ (zip formals vs) $ \(formalTy, _arg) -> do
              case formalTy of
                FnType {} ->
                  dbgStr "check precondition implication (TODO!)"
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

        dbgStr $ "KNCall " ++ show (pretty expr) ++ " :: " ++ show (pretty ty)
        -- Does the called function have a precondition?
        -- See also mkPrecondGen / compilePreconditionFn
        case fromMaybe [] $ getMbFnPreconditions facts (tidIdent v) of
          [] -> do
            dbgStr $ "TODO: call of function with result type " ++ show ty ++ " ; " ++ show (v)
            dbgStr $ "           (no precond)"
          fps -> do
            dbgStr $ "TODO: call of function with result type " ++ show ty ++ " ; " ++ show (tidIdent v)
            dbgStr $ "           (have precond)"
            let checkPrecond fp = do
                 SMTExpr e decls idfacts <- fp vs
                 dbgStr $ "checkPrecond[ " ++ show vs ++ " ] " ++ show (SMT.pp e) ++ ";;;;;" ++ show idfacts
                 let thm = scriptImplyingBy (SMTExpr e decls idfacts)  facts
                 dbgStr $ "fn precond checking this script:"
                 dbgStr $ show (prettyCommentedScript thm)
                 scRunZ3 expr thm
            mapM_ checkPrecond fps

        case ty of
            RefinedType rtv _rte _rtargs
              -- -> return Nothing -- $ withDecls facts $ \x -> return $ smtId x === smtVar rtv
                  --mbrte <- checkBody _rte facts
                        --mbe <- (maybeM mbrte) x
              -> do
                    resid <- lift $ ccFreshId $ T.pack (".fnres_" ++ show (tidIdent rtv))
                    dbgIf dbgRefinedCalls $ text "call of fn" <+> pretty v <+> text "with refined type..."
                    dbgIf dbgRefinedCalls $ indent 4 (text "rtv = " <> pretty rtv)
                    dbgIf dbgRefinedCalls $ indent 4 (text "rte = " <> pretty _rte)
                    facts' <- compileRefinementBoundTo resid facts rtv _rte
                    let facts'' = addSymbolicVars facts' [TypedId (tidType rtv) resid]
                    dbgIf dbgRefinedCalls $ indent 4 (text "facts' = " <> pretty facts'')
                    return $ withDecls facts'' $ \x -> do
                        dbgIf dbgRefinedCalls $ text "result of call to fn" <+> pretty v <+> text "being bound to" <+> pretty x
                        return $ (smtId x === smtId resid)
                        --return $ (smtId resid === smtVar rtv)
                        --return $ SMT.true
                        --return $ (smtId resid)
                        --dbgIf dbgRefinedCalls $ text "result of call to fn" <+> pretty v <$> pretty mbe
                        --return $ SMT.and (smtId resid) (smtId x === smtVar rtv)

            _ -> return Nothing

    KNLetVal      id   e1 e2    -> do
        --dbgStr $ "letval checking bound expr for " ++ show id
        --dbgDoc $ indent 8 (pretty e1)
        mb_f   <- checkBody e1 facts
        facts' <- whenRefinedElse (typeKN e1) (compileRefinementBoundTo id facts) facts
        case mb_f of
          Nothing -> do dbgStr $ "  no fact for id binding " ++ show id
                        dbgStr $ "       with type " ++ show (pretty (typeKN e1))
                        checkBody e2 (addSymbolicVars facts' [TypedId (typeKN e1) id])
          Just f  -> do dbgStr $ "have fact for id binding " ++ show id
                        newfact <- f id
                        checkBody e2 (addIdentFact facts' id newfact (typeKN e1))

    KNLetFuns     [id] [fn] b | identPrefix id == T.pack "assert-invariants-thunk" -> do
        _ <- checkFn'  fn facts
        do   checkBody b  facts

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

    KNAppCtor     {} -> return Nothing

    KNAlloc       {} -> return Nothing
    KNStore       {} -> return Nothing
    KNDeref       {} -> return Nothing

    KNTuple       {} -> return Nothing

    KNTyApp _t _v _ts -> -- We don't return a fact saying (x === v) because
                        -- doing so would produce invalid SMT when v is function-typed.
                        -- Instead, we record a meta fact (even-more-meta, that is)
                        -- of the correspondence...
                        return Nothing
    KNKillProcess {} -> return $ withDecls facts $ \_x -> return SMT.false

scIntrospect :: SC x -> SC (Either CompilerFailures x)
scIntrospect action = do state <- get
                         lift $ compiledIntrospect (evalStateT action state)
  where
    compiledIntrospect :: Compiled x -> Compiled (Either CompilerFailures x)
    compiledIntrospect action = do state <- get
                                   liftIO $ runCompiled action state

    runCompiled :: Compiled x -> CompilerContext -> IO (Either CompilerFailures x)
    runCompiled action state = runExceptT $ evalStateT action state


whenRefined ty f = whenRefinedElse ty f ()

whenRefinedElse ty f d =
  case ty of
    RefinedType v e _ -> f v e
    _                 -> return d

recordIfHasFnPrecondition facts v@(TypedId ty id) =
  case ty of
    FnType {} -> do
      dbgDoc $ text $ "computeRefinements for " ++ show v ++ " was "
      dbgDoc $ indent 4 $ pretty (computeRefinements v)
      case computeRefinements v of
        [] -> return $ facts
        preconds -> return $ facts { fnPreconds = Map.insert id (map (mkPrecondGen facts) preconds) (fnPreconds facts) }
    _ -> return $ facts

mkPrecondGen :: Facts -> (Fn RecStatus KNMono MonoType) -> ([MoVar] -> SC SMTExpr)
mkPrecondGen facts fn = \argVars -> do
  _uref <- lift $ gets ccUniqRef
  --fn' <- liftIO $ alphaRename' fn uref
  let fn' = fn
  sc <- get
  lift $ evalStateT (compilePreconditionFn fn' facts argVars) (sc { scExtraFacts = Map.empty })

-- Implicit precondition: fn is alpha-renamed.
compilePreconditionFn :: Fn RecStatus KNMono MonoType -> Facts
                      -> [TypedId MonoType] -> SC SMTExpr
compilePreconditionFn fn facts argVars = do
  dbgStr $ "compilePreconditionFn<" ++ show (length argVars) ++ " vs " ++ show (length (fnVars fn)) ++ " # " ++ show argVars ++ "> ;; " ++ show fn
  resid <- lift $ ccFreshId $ identPrefix $ fmapIdent (T.append (T.pack "res$")) $ tidIdent (fnVar fn)
  let facts' = addSymbolicVars facts ((TypedId (PrimInt I1) resid):(argVars ++ fnVars fn))
  facts'' <- foldlM recordIfHasFnPrecondition facts' (fnVars fn)
  bodyf <- checkBody (fnBody fn) facts''
  (SMTExpr body decls idfacts) <- (trueOr bodyf) resid
  let idfacts' = extendIdFacts resid body (zip (map tidIdent argVars)
                                               (map tidIdent $ fnVars fn)) idfacts
  return $ SMTExpr (smtId resid) decls idfacts'

compileRefinementBoundTo id facts v0 e0  = do
  (Fn v [] e _ _) <- lift $ alphaRenameMono (Fn v0 [] e0 NotRec (annotForRange (MissingSourceRange "knstatic-ref")))
  mb_f2 <- checkBody e facts
  resid <- lift $ ccFreshId $ T.pack ".true"
  (SMTExpr body decls idfacts) <- (trueOr mb_f2) resid
  let idfacts' = extendIdFacts resid (SMT.and (smtId resid) body) [(id, tidIdent v)] idfacts
  let facts'1 = addSymbolicVars facts [v, TypedId (PrimInt I1) resid]
  let lostFacts = (identFacts facts'1) `butnot` idfacts'
  let facts'2 = if null lostFacts then facts'1 { identFacts = idfacts' }
                                  else error $ "dont wanna lose these facts! : " ++ (show lostFacts)
  let facts'3 = addSymbolicDecls facts'2 decls
  return $ facts'3

-- Adds ``body`` as an associated fact of ``resid``,
-- and adds pairwise equality facts assoc w/ ``map fst equalIds``.
extendIdFacts resid body equalIds idfacts =
    foldl' (\idfacts (av,fv) -> (av, idsEq (av,fv)) : idfacts)
           ((resid, body):idfacts)
           equalIds

smtExprOr e1 e2 = smtExprMergeWith SMT.or e1 e2

smtExprMergeWith combine (SMTExpr e1 d1 f1) (SMTExpr e2 d2 f2) =
             SMTExpr (combine e1 e2) (Set.union d1 d2) (f1 ++ f2)

smtExprAnd' Nothing e' = bareSMTExpr e'
smtExprAnd' (Just (SMTExpr e decls idfacts)) e' = SMTExpr (SMT.and e e') decls idfacts

trueOr Nothing  = \id -> return $ bareSMTExpr (smtId id === SMT.true)
trueOr (Just f) = f

maybeM :: Maybe (t -> SC rv) -> (t -> SC (Maybe rv))
maybeM Nothing = \_ -> return Nothing
maybeM (Just f) = \id -> do rv <- f id ; return (Just rv)

bareSMTExpr e = SMTExpr e Set.empty []

idsEq  (v1, v2) = smtId  v1 === smtId  v2

getMbFnPreconditions facts id = Map.lookup id (fnPreconds facts)

primName tid = T.unpack (identPrefix (tidIdent tid))

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

instance Pretty Facts where
  pretty facts =
    parens (text "Facts"
              <$> text "fnPreconds:" <+> pretty (Map.keys $ fnPreconds facts)
              <$> text "identFacts:" <+> pretty (identFacts facts)
              <$> text "pathFacts:" <+> pretty (pathFacts facts)
              <$> text "symbolicDecls:" <+> pretty (Set.toList $ symbolicDecls facts))

prettyCommentedScript :: CommentedScript -> Doc
prettyCommentedScript (CommentedScript items target) =
  vsep (map pretty items) <$> pretty (Cmds [CmdAssert target])
-- }}}

-- {{{
dbgIf c d = if c then liftIO $ putDocLn d else return ()

dbgCheckFn      = False
dbgRefinedCalls = False
-- }}}
