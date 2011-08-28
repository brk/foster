-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CFG where

import Foster.Base
import Foster.TypeIL
import Foster.KNExpr

import Control.Monad.State

type CFBlock = Block CFMiddle CFLast

computeCFGIO :: Fn KNExpr TypeIL -> IO (Fn [CFBlock] TypeIL)
computeCFGIO fn = do
  let (letable, cfgState) = _computeCFG fn
  putStrLn $ (show $ fnVar fn) ++ " \n\t~~~~~~~~~~letable: " ++ show letable
                                ++ "\n\t~~~~~~~~~~preblock:" ++
        show (cfgPreBlock cfgState)
  return $ fn { fnBody = Prelude.reverse (cfgAllBlocks cfgState) }

_computeCFG :: Fn KNExpr TypeIL -> ((), CFGState)
_computeCFG fn =
  let state0 = CFGState 1 (Just (Ident "begin" 0, [])) [] in
  let ret fn var = case (identPrefix $ tidIdent $ fnVar fn) of
                         "main" -> cfgEndWith (CFRetVoid)
                         _ -> cfgEndWith (CFRet var) in
  runState (computeBlocks (fnBody fn) Nothing (ret fn)) state0

computeCFG :: Fn KNExpr TypeIL -> Fn [CFBlock] TypeIL
computeCFG fn =
  let (letable, cfgState) = _computeCFG fn in
  fn { fnBody = Prelude.reverse (cfgAllBlocks cfgState) }

showCFBlocks blocks = out $ (joinWith "\n\n\t" $ map show blocks)

instance (Show m, Show l) => Show (Block m l) where
  show (Block id mids last) =
        "CFBlock " ++ show id ++ "\n\t\t"
        ++ (joinWith "\n\t\t" (map show mids))
        ++ "\n\t" ++ show last

instance Show CFGState where
  show (CFGState u preblock allblocks) =
        "CFGState:"
        ++ "\n\t" ++ show u
        ++ "\n\t" ++ show preblock
        ++ "\n\t" ++ (joinWith "\n\n\t" $ map show allblocks)

cfgMidLet :: CFLetable -> CFG ()
cfgMidLet letable = do id <- cfgFresh ".cfg_seq"
                       cfgAddMiddle (CFLetVal id letable)

cfgAddLet :: Maybe Ident -> CFLetable -> TypeIL -> CFG AIVar
cfgAddLet maybeid letable ty = do
        id <- (case maybeid of
                Just id -> return id
                Nothing -> cfgFresh ".cfg_seq")
        cfgAddMiddle (CFLetVal id letable)
        return (TypedId ty id)

-- computeBlocks takes an expression and a contination,
-- which determines what to do with the let-bound result of the expression.
computeBlocks :: KNExpr -> Maybe Ident -> (AIVar -> CFG ()) -> CFG ()
computeBlocks expr idmaybe k = do
    case expr of
        KNIf t v a b      -> do
            slot_id <- cfgFresh "if_slot"
            ifthen <- cfgFresh "if_then"
            ifelse <- cfgFresh "if_else"
            ifcont <- cfgFresh "if_cont"

            let slotvar = TypedId (PtrTypeIL t) slot_id
            let slot = CFAllocate (ILAllocInfo t MemRegionStack Nothing False)
            cfgAddMiddle (CFLetVal slot_id slot)

            cfgEndWith (CFIf t v ifthen ifelse)

            cfgNewBlock ifthen
            computeBlocks a Nothing (\var -> cfgMidLet (CFStore var slotvar))
            cfgEndWith (CFBr ifcont)

            cfgNewBlock ifelse
            computeBlocks b Nothing (\var -> cfgMidLet (CFStore var slotvar))
            cfgEndWith (CFBr ifcont)

            cfgNewBlock ifcont
            cfgAddLet idmaybe (CFDeref slotvar) t >>= k

        KNUntil t a b     -> do
            until_test <- cfgFresh "until_test"
            until_body <- cfgFresh "until_body"
            until_cont <- cfgFresh "until_cont"
            cfgEndWith (CFBr until_test)

            cfgNewBlock until_test
            computeBlocks a Nothing (\var ->
              cfgEndWith (CFIf (typeKN a) var until_cont until_body))

            cfgNewBlock until_body
            computeBlocks b Nothing (\var -> cfgEndWith (CFBr until_test))

            cfgNewBlock until_cont
            cfgAddLet idmaybe (CFTuple []) (TupleTypeIL []) >>= k

        KNLetVal id (KNVar v) cont ->
            -- TODO it's not fantastic to be forced to have explicit
            -- substitution for k-normal forms. But we don't have many choices
            -- given code like     let x = 0  ;  y = x ;  in x + y
            computeBlocks (knSubst id v cont) idmaybe k

        KNLetVal id expr cont -> do
            -- expr could be a KNCase, so it must be processed by computeBlocks.
            -- Because we want the result from processing expr to be let-bound
            -- to an identifier of our choosing (rather than the sub-call's
            -- choosing, that is), we provide it explicitly as idmaybe.
            computeBlocks expr (Just id) (\_var -> return ())
            computeBlocks cont idmaybe k

        KNLetFuns ids fns e -> do
            cfgAddMiddle (CFLetFuns ids $ map computeCFG fns)
            computeBlocks e idmaybe k

        KNCase t v bs -> do
            slot_id <- cfgFresh "case_slot"
            case_cont <- cfgFresh "case_cont"

            let slotvar = TypedId (PtrTypeIL t) slot_id
            let slot = CFAllocate (ILAllocInfo t MemRegionStack Nothing False)
            cfgAddMiddle (CFLetVal slot_id slot)

            bbs <- mapM (\(pat, _) -> do block_id <- cfgFresh "case_arm"
                                         return $ (pat, block_id)) bs
            cfgEndWith (CFCase t v bbs)

            let computeCaseBlocks ((_pat, e), (_, block_id)) = do
                    cfgNewBlock block_id
                    id <- cfgFresh "case_arm_val"
                    computeBlocks e Nothing (\var -> cfgMidLet (CFStore var slotvar))
                    cfgEndWith (CFBr case_cont)
            mapM_ computeCaseBlocks (zip bs bbs)

            cfgNewBlock case_cont
            cfgAddLet idmaybe (CFDeref slotvar) t >>= k

        KNVar v -> k v
        _ -> do cfgAddLet idmaybe (knToCFLetable expr) (typeKN expr) >>= k

knToCFLetable :: KNExpr -> CFLetable
knToCFLetable expr =
  case expr of
            KNVar        v      -> error $ "can't make CFLetable from KNVar!"
            KNBool       b      -> CFBool       b
            KNInt        t i    -> CFInt        t i
            KNTuple      vs     -> CFTuple      vs
            KNCallPrim   t p vs -> CFCallPrim   t p vs
            KNCall       t b vs -> CFCall       t b vs
            KNAppCtor    t c vs -> CFAppCtor    t c vs
            KNAlloc      v      -> CFAlloc      v
            KNDeref      v      -> CFDeref      v
            KNStore      a b    -> CFStore      a b
            KNAllocArray t v    -> CFAllocArray t v
            KNArrayRead  t a b  -> CFArrayRead  t a b
            KNArrayPoke  a b c  -> CFArrayPoke  a b c
            KNTyApp t v argty   -> CFTyApp t v argty
            _                   -> error $ "non-letable thing seen by letable: "
                                         ++ show expr

data CFMiddle =
          CFLetVal      Ident     CFLetable
        | CFLetFuns     [Ident]   [Fn [CFBlock] TypeIL]
        deriving Show

data CFLetable =
          CFBool        Bool
        | CFInt         TypeIL LiteralInt
        | CFTuple       [AIVar]

        | CFCallPrim    TypeIL ILPrim [AIVar]
        | CFCall        TypeIL AIVar  [AIVar]
        | CFAppCtor     TypeIL CtorId [AIVar]
        -- Stack/heap slot allocation
        | CFAllocate    ILAllocInfo
        -- Mutable ref cells
        | CFAlloc       AIVar
        | CFDeref       AIVar
        | CFStore       AIVar AIVar
        -- Array operations
        | CFAllocArray  TypeIL AIVar
        | CFArrayRead   TypeIL AIVar  AIVar
        | CFArrayPoke          AIVar  AIVar  AIVar
        | CFTyApp       TypeIL AIVar TypeIL
        deriving (Show)

data CFLast =
          CFRetVoid
        | CFRet         AIVar
        | CFBr          BlockId
        | CFIf          TypeIL AIVar  BlockId   BlockId
        | CFCase        TypeIL AIVar [(Pattern, BlockId)]
        deriving (Show)


data CFGState = CFGState {
    cfgUniq         :: Uniq
  , cfgPreBlock     :: Maybe (BlockId, [CFMiddle])
  , cfgAllBlocks    :: [CFBlock]
}

type CFG a = State CFGState a

cfgFresh :: String -> CFG BlockId
cfgFresh s = do
        old <- get
        put (old { cfgUniq = (cfgUniq old) + 1 })
        return (Ident s (cfgUniq old))

cfgNewBlock :: BlockId -> CFG ()
cfgNewBlock id = do
        old <- get
        case cfgPreBlock old of
          Nothing      -> do put (old { cfgPreBlock = Just (id, []) })
          Just (id, _) -> error $ "Tried to start new block "
                               ++ " with unfinished old block " ++ show id

cfgAddMiddle :: CFMiddle -> CFG ()
cfgAddMiddle mid = do
        old <- get
        case cfgPreBlock old of
          Just (id, mids) -> do put (old { cfgPreBlock = Just (id, mid:mids) })
          Nothing         -> error $ "Tried to add middle without a block"

cfgEndWith :: CFLast -> CFG ()
cfgEndWith last = do
        old <- get
        case cfgPreBlock old of
          Nothing          -> error $ "Tried to finish block but no preblock!"
                                     ++ "Tried to end with " ++ show last
          Just (id, mids) -> do
            let newblock = Block id (Prelude.reverse mids) last
            put (old { cfgPreBlock     = Nothing
                     , cfgAllBlocks    = newblock : (cfgAllBlocks old) })


substFn id var fn =
  let ids = map tidIdent (fnVars fn) in
  if id `elem` ids
    then error $ "knSubstFn found re-bound id " ++ show id
    else fn { fnBody = (knSubst id var (fnBody fn)) }

knVarSubst id v1 v2 = if id == tidIdent v2 then v1 else v2

-- Replace all uses of  id  with  v  in expr.
knSubst id var expr =
  let substV = knVarSubst id var in
  let substE = knSubst    id var in
  case expr of
        KNTuple vs -> KNTuple (map substV vs)
        KNBool _                -> expr
        KNInt t _               -> expr
        KNVar v                 -> KNVar (substV v)
        KNLetVal x b e          -> if x == id
                                     then error $ "knSubst found re-bound id " ++ show id
                                     else KNLetVal x (substE b) (substE e)
        KNLetFuns ids fns e     -> if id `elem` ids
                                     then error $ "knSubst found re--bound id " ++ show id
                                     else KNLetFuns ids (map (substFn id var) fns) (substE e)
        KNCall t v vs           -> KNCall t (substV v) (map substV vs)
        KNCallPrim t prim vs    -> KNCallPrim t prim (map substV vs)
        KNAppCtor t ctor vs     -> KNAppCtor t ctor (map substV vs)
        KNAllocArray elt_ty v   -> KNAllocArray elt_ty (substV v)
        KNIf t a b c            -> KNIf t (substV a) (substE b) (substE c)
        KNUntil t a b           -> KNUntil t (substE a) (substE b)
        KNAlloc v               -> KNAlloc (substV v)
        KNDeref v               -> KNDeref (substV v)
        KNStore v1 v2           -> KNStore (substV v1) (substV v2)
        KNArrayRead t v1 v2     -> KNArrayRead t (substV v1) (substV v2)
        KNArrayPoke v1 v2 v3    -> KNArrayPoke (substV v1) (substV v2) (substV v3)
        KNCase t v patexprs     -> KNCase t (substV v) (map (\(p,e) -> (p, substE e)) patexprs)
        KNTyApp overallType v t -> KNTyApp overallType (substV v) t
