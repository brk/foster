{-# LANGUAGE StandaloneDeriving, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2014 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.KNStaticChecks where

import qualified Data.Map as Map
import Data.Map(Map)
import Data.List(foldl')

import Foster.MonoType
import Foster.Base
import Foster.KNUtil
import Foster.Config

import qualified Data.Text as T

import Control.Monad.State(gets, liftIO, evalStateT, execStateT, StateT,
                           execState, State, forM,
                           liftM, liftM2, get, put, lift)

import qualified SMTLib2 as SMT
import           SMTLib2(app, Script(..), Command(..), Option(..), Type(..))
import qualified SMTLib2.Core as SMT
import           SMTLib2.Core(tBool, (===), (=/=))
import SMTLib2.BitVector

import Foster.RunZ3 (runZ3)

data Facts = Facts { fnPreconds :: Map Ident ([Ident] -> SMT.Expr)
                   , identFacts :: Map Ident SMT.Expr
                   , pathFacts  :: [SMT.Expr]
                   , symbolicDecls :: [(SMT.Name, [SMT.Type], SMT.Type)]
                   }
------
nm id = SMT.N (show id)

ident :: Ident -> SMT.Ident
ident id = SMT.I (nm id) []

smtId  id  = app (ident id) []
smtVar tid = smtId (tidIdent tid)

smtVars tids = map smtVar tids

addIdentFact facts id expr ty =
  addSymbolicVar facts' (TypedId ty id)
    where facts' = facts { identFacts = Map.insert id expr (identFacts facts) }

addSymbolicVar facts tid =
  let id = tidIdent tid in
  case tidType tid of
    FnType dom rng _precond _ _ ->
      facts { symbolicDecls = (nm id, map smtType dom, smtType rng) : symbolicDecls facts }
    ty ->
      facts { symbolicDecls = (nm id, [], smtType ty) : symbolicDecls facts }

smtType :: MonoType -> SMT.Type
smtType (PrimInt I1) = tBool
smtType (PrimInt sz) = tBitVec (fromIntegral $ intSizeOf sz)
smtType (ArrayType _) = smtArray
smtType (TupleType tys) = TApp (smtI ("FosterTuple" ++ show (length tys))) (map smtType tys)
smtType ty = error $ "smtType can't yet handle " ++ show ty

smtArray = TApp (smtI "FosterArray") []

litOfSize num sz = bv num (fromIntegral $ intSizeOf sz)

scriptImplyingBy :: SMT.Expr -> Facts -> Script
scriptImplyingBy pred facts =
  let preconds = map snd $ Map.toList $ identFacts facts in
  Script $ [CmdSetOption (OptProduceModels True)
           ,CmdSetLogic (SMT.N "QF_AUFBV")
           ,CmdDeclareType (SMT.N "FosterArray") 0
           ,CmdDeclareType (SMT.N "FosterTuple0") 0
           ,CmdDeclareType (SMT.N "FosterTuple2") 2
           ,CmdDeclareType (SMT.N "FosterTuple3") 3
           ,CmdDeclareType (SMT.N "FosterTuple4") 4
           ,CmdDeclareType (SMT.N "FosterTuple5") 5
           ,CmdDeclareType (SMT.N "FosterTuple6") 6
           ,CmdDeclareType (SMT.N "FosterTuple7") 7
           ,CmdDeclareType (SMT.N "FosterTuple8") 8
           ,CmdDeclareFun (SMT.N "foster$arraySizeOf") [smtArray] (tBitVec 64)
           ]
        ++ map (\(nm, tys, ty) -> CmdDeclareFun nm tys ty) (symbolicDecls facts)
        ++ map CmdAssert (pathFacts facts ++ preconds)
        ++ [CmdAssert $ SMT.not pred]
        ++ [CmdCheckSat]
------

type SC = StateT SCState Compiled
data SCState = SCState {
  scExtraFacts :: (Map Ident (Ident -> SMT.Expr))
}

scAddFact id k = do
  sc <- get
  put $ sc { scExtraFacts = Map.insert id k (scExtraFacts sc) }

scGetFact id = do
  sc <- get
  return $ Map.lookup id (scExtraFacts sc)

runStaticChecks :: ModuleIL KNMono MonoType -> Compiled ()
runStaticChecks m = do
  checkModuleExprs (moduleILbody m) (Facts Map.empty Map.empty [] [])

checkModuleExprs :: KNMono -> Facts -> Compiled ()
checkModuleExprs expr facts =
  case expr of
    KNLetFuns     [id] [fn] b -> do
        facts' <- recordFnPrecondition facts id fn
        checkFn fn facts'
        checkModuleExprs b facts'
    KNCall {} ->
      return ()
    _ -> error $ "Unexpected expression in checkModuleExprs"

checkFn fn facts = do
  evalStateT (checkFn' fn facts) (SCState Map.empty)

checkFn' fn facts = do
  let facts' = foldl' addSymbolicVar facts (fnVars fn)
  _ <- checkBody (fnBody fn) facts'
  return ()

withPathFact facts pathfact = facts { pathFacts = pathfact : pathFacts facts }

lift2 f [x, y] = f x y

inRangeCO x (a, b) = bvsge x a `SMT.and` bvslt x b
inRangeCC x (a, b) = bvsge x a `SMT.and` bvsle x b

smtI s = SMT.I (SMT.N s) []

smtArraySizeOf x = app (smtI "foster$arraySizeOf") [x]

putZ3Result (Left x) = putStrLn x
putZ3Result (Right strs) = mapM_ (putStrLn . ("\t"++)) strs

fnMap = Map.fromList    [("==", (===))
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

-- Returns an SMT expression summarizing the given expression.
checkBody :: KNMono -> Facts -> SC (Maybe (Ident -> SC SMT.Expr))
checkBody expr facts =
  case expr of
    KNLiteral (PrimInt sz) (LitInt i) -> do
        return $ Just $ \x -> return $ smtId x === litOfSize (fromInteger $ litIntValue i) sz
    KNLiteral     {} -> return Nothing
    KNVar         {} -> return Nothing
    KNKillProcess {} -> return Nothing
    KNTyApp       {} -> return Nothing
    KNTuple       {} -> return Nothing
    KNAllocArray  {} -> return Nothing

    KNArrayRead ty (ArrayIndex a i _ _)   -> do
        let precond = (sign_extend 32 (smtVar i)) `inRangeCO` (litOfSize 0 I64, smtArraySizeOf (smtVar a))
        let thm = scriptImplyingBy precond facts
        liftIO $ do res <- runZ3 (show $ SMT.pp thm)
                    putStrLn $ "precondition for " ++ show (SMT.pp thm) ++ ": "
                    putZ3Result res
        -- If the array has an annotation, use it.
        mb_f <- scGetFact (tidIdent a)
        case mb_f of
          Nothing -> do liftIO $ putStrLn $ "no constraint on output of array read"
                        return Nothing
          Just f -> do liftIO $ putStrLn $ "have a constraint on output of array read: " ++ show (f (tidIdent a))
                       return $ Just $ \x -> return $ f x

    KNArrayPoke ty (ArrayIndex a i _ _) v -> return Nothing

    KNArrayLit (ArrayType (PrimInt sz)) _v entries -> do
        {- TODO: attach this condition to the array itself, so that
                 the condition is asserted on the results of any reads from the array,
                 without needing to use a universal quantifier... -}
        let arrayReadResultConstraint id =
                case staticArrayValueBounds entries of
                      Just (mn, mx) -> (smtId id) `inRangeCC` (litOfSize mn sz, litOfSize mx sz)
                      Nothing -> SMT.true
        return $ Just $ \x -> do
                    scAddFact x arrayReadResultConstraint
                    return $ (smtArraySizeOf (smtId x) === litOfSize (fromIntegral $ length entries) I64)

    KNArrayLit {} -> return Nothing

    KNAlloc       {} -> return Nothing
    KNStore       {} -> return Nothing
    KNDeref       {} -> return Nothing

    KNCallPrim _ (NamedPrim tid) vs
        | T.unpack (identPrefix (tidIdent tid)) `elem` ["print_i32", "expect_i32"] -> do
        return $ Nothing

    KNCallPrim _ (NamedPrim tid) vs
        | T.unpack (identPrefix (tidIdent tid)) `elem` ["assert-invariants"] -> do
        let precond = smtAll (map smtVar vs)
        let thm = scriptImplyingBy precond facts
        liftIO $ do res <- runZ3 (show $ SMT.pp thm)
                    putStrLn $ "precondition for " ++ show (SMT.pp thm) ++ ": "
                    putZ3Result res
        return $ Nothing

    KNCallPrim (PrimInt szr) (PrimOp ('s':'e':'x':'t':'_':_) (PrimInt szi)) [v] -> do
        return $ Just $ \x -> return $ smtId x === sign_extend (fromIntegral $ intSizeOf szr - intSizeOf szi) (smtVar v)

    KNCallPrim (PrimInt szr) (PrimOp ('z':'e':'x':'t':'_':_) (PrimInt szi)) [v] -> do
        return $ Just $ \x -> return $ smtId x === zero_extend (fromIntegral $ intSizeOf szr - intSizeOf szi) (smtVar v)

    KNCallPrim _ (PrimOp opname (PrimInt _)) vs | Just op <- Map.lookup opname fnMap -> do
        return $ Just $ \x -> return $ smtId x === lift2 op (smtVars vs)

    KNCallPrim _ (PrimOp "bitshl" (PrimInt _)) vs -> do
        -- TODO check 2nd var <= sz
        return $ Just $ \x -> return $ smtId x === lift2 bvshl (smtVars vs)

    KNCallPrim _ (PrimOp "bitlshr" (PrimInt _)) vs -> do
        -- TODO check 2nd var <= sz
        return $ Just $ \x -> return $ smtId x === lift2 bvlshr (smtVars vs)

    KNCallPrim _ (PrimOp "bitashr" (PrimInt _)) vs -> do
        -- TODO check 2nd var <= sz
        return $ Just $ \x -> return $ smtId x === lift2 bvashr (smtVars vs)

    KNCallPrim (PrimInt _) (PrimOp "sdiv-unsafe" (PrimInt sz)) vs -> do
        let precond [s1, s2] = s2 =/= (litOfSize 0 sz)
        let thm = scriptImplyingBy (precond (smtVars vs)) facts
        liftIO $ do res <- runZ3 (show $ SMT.pp thm)
                    putStrLn $ "precondition for " ++ show (SMT.pp thm) ++ ": "
                    putZ3Result res
        return $ Just $ \x -> return $ smtId x === lift2 bvsdiv (smtVars vs)

    KNCallPrim _ty prim vs -> do
        liftIO $ putStrLn $ "TODO: checkBody attributes for call prim " ++ show prim ++ " $ " ++ show vs
        return Nothing

    KNAppCtor     {} -> return Nothing
    KNInlined _t0 _to _tn _old new -> checkBody new facts
    KNCase        ty v arms     -> do
        -- TODO: better path conditions for individual arms
        _ <- forM arms $ \arm -> do
            case caseArmGuard arm of
                Nothing -> checkBody (caseArmBody arm) facts
                Just g -> error $ "can't yet support case arms with guards in KNStaticChecks"
        return Nothing
        --error $ "checkBody cannot yet support KNCase" -- KNCase ty v (map (fmapCaseArm id (q tailq) id) arms)
    KNIf          ty v e1 e2    -> do
        _ <- checkBody e1 (facts `withPathFact` (        (smtVar v)))
        _ <- checkBody e2 (facts `withPathFact` (SMT.not (smtVar v)))
        return Nothing

    KNLetVal      id   e1 e2    -> do
        mb_f <- checkBody e1 facts
        case mb_f of
          Nothing -> checkBody e2 (addSymbolicVar facts (TypedId (typeKN e1) id))
          Just f  -> do newfact <- f id
                        checkBody e2 (addIdentFact facts id newfact (typeKN e1))

    KNCall ty v vs -> do
        precond <- getFnPrecondition facts (tidIdent v)
        liftIO $ putStrLn $ "TODO: call of function with type " ++ show ty
        liftIO $ putStrLn $ "TODO: check attributes for " ++ show vs
        return Nothing

    KNLetFuns     [id] [fn] b | identPrefix id == T.pack "assert-invariants-thunk" -> do
        checkFn'  fn facts
        checkBody b  facts
        return Nothing

    KNLetFuns     [id] [fn] b -> do
        facts' <- recordFnPrecondition facts id fn
        checkFn'  fn facts'
        checkBody b  facts'
        return Nothing

    KNLetRec      ids es  b     ->
        error $ "KNStaticChecks.hs: checkBody can't yet support recursive non-function bindings."
    KNLetFuns     ids fns b     ->
        error $ "KNStaticChecks.hs: checkBody can't yet support recursive function nests."

fromJust (Just a) = a
fromJust Nothing = error $ "can't unJustify Nothing"

recordFnPrecondition facts id fn = do
  liftIO $ putStrLn $ "TODO: record precondition for fn " ++ show id
  return $ facts

getFnPrecondition facts id = do
  liftIO $ putStrLn $ "TODO: check precondition for " ++ show id
  return ()

