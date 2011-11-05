{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CFG
( computeCFGIO
, Insn(..)
, BlockId
, BasicBlockGraph(..)
, BasicBlock
, splitBasicBlock
, CFMiddle(..)
, CFLast(..)
, CFFn
) where

import Foster.Base(Uniq, Fn(..), TypedId(..), Ident(..), identPrefix, Pattern(..))
import Foster.TypeIL(TypeIL(..), AIVar, ILAllocInfo(..), AllocMemRegion(..))
import Foster.KNExpr(KNExpr(..), typeKN)
import Foster.Letable(Letable(..))

import Compiler.Hoopl

import qualified Data.Text as T

import Control.Monad.State
import Data.IORef
import Prelude hiding (id, last)

-- This is the "entry point" into CFG-building for the outside.
-- We take (and update) a mutable reference as a convenient way of
-- threading through the small amount of globally-unique state we need.
computeCFGIO :: IORef Uniq -> Fn KNExpr TypeIL -> IO CFFn
computeCFGIO uref fn = do
  u <- readIORef uref
  let cfgState = internalComputeCFG u fn
  writeIORef uref (cfgUniq cfgState + 1)
  return $ extractFunction cfgState fn

-- A mirror image for internal use (when converting nested functions).
-- As above, we thread through the updated unique value from the subcomputation!
cfgComputeCFG :: Fn KNExpr TypeIL -> CFG CFFn
cfgComputeCFG fn = do
  u0 <- gets cfgUniq
  let cfgState = internalComputeCFG u0 fn
  cfgPutUniq $ cfgUniq cfgState + 1
  return $ extractFunction cfgState fn

-- A helper for the CFG functions above, to run computeBlocks.
internalComputeCFG :: Int -> Fn KNExpr TypeIL -> CFGState
internalComputeCFG uniq fn =
  let preblock = (Left "postalloca" , []) in
  let state0 = CFGState uniq (Just preblock) [] in
  execState runComputeBlocks state0
  where
    runComputeBlocks = do computeBlocks (fnBody fn) Nothing (ret fn)

    -- Make sure that the main function returns void.
    ret f var = if isMain f then cfgEndWith (CFRetVoid)
                            else cfgEndWith (CFRet var)
            where isMain f = (identPrefix $ tidIdent $ fnVar f) == T.pack "main"

-- The other helper, to collect the scattered results and build the actual CFG.
extractFunction st fn =
  let blocks = Prelude.reverse (cfgAllBlocks st) in
  fn { fnBody = BasicBlockGraph (entryId blocks) (catClosedGraphs blocks) }
  where -- Dunno why this function isn't in Hoopl...
        catClosedGraphs :: [Graph Insn C C] -> Graph Insn C C
        catClosedGraphs = foldr (|*><*|) emptyClosedGraph

        entryId [] = error $ "can't get entry block id from empty list!"
        entryId (bb:_) = id where (id, _, _) = splitBasicBlock bb

cfgFreshSlotVar :: TypeIL -> String -> CFG AIVar
cfgFreshSlotVar t n = do
    id <- cfgFreshId n
    let slot = ILAllocate (ILAllocInfo t MemRegionStack Nothing False)
    cfgAddMiddle (ILetVal id slot)
    return $ TypedId (PtrTypeIL t) id

-- computeBlocks takes an expression and a contination,
-- which determines what to do with the let-bound result of the expression.
computeBlocks :: KNExpr -> Maybe Ident -> (AIVar -> CFG ()) -> CFG ()
computeBlocks expr idmaybe k = do
    case expr of
        -- compile (if v then a else b) to
        -- slot = undef; if v then v_a = [[a]]; slot := v_a;
        --                    else v_b = [[b]]; slot := v_b;
        -- slot^
        KNIf t v a b -> do
            [ifthen, ifelse, ifcont] <- mapM cfgFresh
                                               ["if_then", "if_else", "if_cont"]
            slotvar <- cfgFreshSlotVar t "if_slot"
            cfgEndWith (CFIf t v ifthen ifelse)

            cfgNewBlock ifthen
            computeBlocks a Nothing $ \var -> cfgMidStore var slotvar
            cfgEndWith (CFBr ifcont)

            cfgNewBlock ifelse
            computeBlocks b Nothing $ \var -> cfgMidStore var slotvar
            cfgEndWith (CFBr ifcont)

            cfgNewBlock ifcont
            cfgAddLet idmaybe (ILDeref slotvar) t >>= k

        KNUntil _t a b -> do
            [until_test, until_body, until_cont] <- mapM cfgFresh
                                      ["until_test", "until_body", "until_cont"]
            cfgEndWith (CFBr until_test)

            cfgNewBlock until_test
            computeBlocks a Nothing $ \var -> cfgEndWith (CFIf (typeKN a) var
                                                          until_cont until_body)

            cfgNewBlock until_body
            computeBlocks b Nothing $ \_var -> cfgEndWith (CFBr until_test)

            cfgNewBlock until_cont
            cfgAddLet idmaybe (ILTuple []) (TupleTypeIL []) >>= k

        KNLetVal id (KNVar v) cont ->
            -- TODO it's not fantastic to be forced to have explicit
            -- substitution for k-normal forms. But we don't have many choices
            -- given code like     let x = 0  ;  y = x ;  in x + y
            computeBlocks (knSubst id v cont) idmaybe k

        KNLetVal id bexp cont -> do
            -- exp could be a KNCase, so it must be processed by computeBlocks.
            -- Because we want the result from processing expr to be let-bound
            -- to an identifier of our choosing (rather than the sub-call's
            -- choosing, that is), we provide it explicitly as idmaybe.
            computeBlocks bexp (Just id) $ \_var -> return ()
            computeBlocks cont idmaybe k

        KNLetFuns ids fns e -> do
            funs <- mapM cfgComputeCFG fns
            cfgAddMiddle (ILetFuns ids $ funs)
            computeBlocks e idmaybe k

        -- Cases are translated very straightforwardly here; we put off
        -- fancier pattern match compilation for later. Giving each arm's
        -- expression a label here conveniently prevents code duplication
        -- during match compilation.
        --
        -- A case expression of overall type t, such as
        --
        --      case scrutinee of p1 -> e1
        --                     of p2 -> e2 ...
        --
        -- gets translated into (the moral equivalent of)
        --
        --      case_slot = alloca t                        ;
        --      case scrutinee of p1 -> goto case_arm1
        --                     of p2 -> goto case_arm2 ...  ;
        --      case_value = load case_slot
        --  case_arm1:
        --      ev = [[e1]]; store ev in case_slot; goto case_cont
        --  case_arm2:
        --      ev = [[e2]]; store ev in case_slot; goto case_cont
        --  ...
        --  case_cont:
        --      ...
        --
        -- The one point this glosses over is how the variables bound by
        -- p1 become visible in the translation of e1. Currently this is
        -- done by some magic in LLCodegen, but it should be represented
        -- more explicitly.
        KNCase t v bs -> do
            slotvar <- cfgFreshSlotVar t "case_slot"
            case_cont <- cfgFresh "case_cont"

            -- Compute the new block ids, along with their patterns.
            bbs <- mapM (\(pat, _) -> do block_id <- cfgFresh "case_arm"
                                         return $ (pat, block_id)) bs

            cfgEndWith (CFCase t v bbs)

            -- Fill in each arm's block with [[e]] (and a store at the end).
            let computeCaseBlocks ((_pat, e), (_, block_id)) = do
                    cfgNewBlock block_id
                    computeBlocks e Nothing $ \var -> cfgMidStore var slotvar
                    cfgEndWith (CFBr case_cont)
            mapM_ computeCaseBlocks (zip bs bbs)

            -- The overall value of the case is the value stored in the slot.
            cfgNewBlock case_cont
            cfgAddLet idmaybe (ILDeref slotvar) t >>= k

        KNVar v -> k v
        _ -> do cfgAddLet idmaybe (knToLetable expr) (typeKN expr) >>= k

knToLetable :: KNExpr -> Letable
knToLetable expr =
  case expr of
            KNVar        _v     -> error $ "can't make Letable from KNVar!"
            KNBool       b      -> ILBool       b
            KNInt        t i    -> ILInt        t i
            KNTuple      vs     -> ILTuple      vs
            KNCallPrim   t p vs -> ILCallPrim   t p vs
            KNCall       t b vs -> ILCall       t b vs
            KNAppCtor    t c vs -> ILAppCtor    t c vs
            KNAlloc      v      -> ILAlloc      v
            KNDeref      v      -> ILDeref      v
            KNStore      a b    -> ILStore      a b
            KNAllocArray t v    -> ILAllocArray t v
            KNArrayRead  t a b  -> ILArrayRead  t a b
            KNArrayPoke  a b c  -> ILArrayPoke  a b c
            KNTyApp t v argty   -> ILTyApp t v argty
            _                   -> error $ "non-letable thing seen by letable: "
                                         ++ show expr

data CFMiddle = CFLetVal      Ident     Letable
              | CFLetFuns     [Ident]   [CFFn]

data CFLast = CFRetVoid
            | CFRet         AIVar
            | CFBr          BlockId
            | CFIf          TypeIL AIVar  BlockId   BlockId
            | CFCase        TypeIL AIVar [(Pattern, BlockId)]
            deriving (Show)

data Insn e x where
              ILabel   :: BlockId            -> Insn C O
              ILetVal  :: Ident   -> Letable -> Insn O O
              ILetFuns :: [Ident] -> [CFFn]  -> Insn O O
              ILast    :: CFLast             -> Insn O C

data CFGState = CFGState {
    cfgUniq         :: Uniq
  , cfgPreBlock     :: Maybe (Either String BlockId, [Insn O O])
  , cfgAllBlocks    :: [Graph Insn C C]
}

type CFG a = State CFGState a

cfgMidStore var slotvar = do id <- cfgFreshId ".cfg_store"
                             cfgAddMiddle (ILetVal id $ ILStore var slotvar)

cfgAddLet :: Maybe Ident -> Letable -> TypeIL -> CFG AIVar
cfgAddLet idmaybe letable ty = do
        id <- (case idmaybe of
                Just id -> return id
                Nothing -> cfgFreshId ".cfg_seq")
        cfgAddMiddle (ILetVal id letable)
        return (TypedId ty id)

cfgNewUniq :: CFG Uniq
cfgNewUniq = do u <- gets cfgUniq ; cfgPutUniq (u + 1) ; return u

cfgPutUniq :: Uniq -> CFG ()
cfgPutUniq u = do old <- get ; put (old { cfgUniq = u })

cfgFreshId :: String -> CFG Ident
cfgFreshId s = do u <- cfgNewUniq ; return (Ident (T.pack s) u)

cfgFresh :: String -> CFG BlockId
cfgFresh s = do u <- freshLabel ; return (s, u)

cfgNewBlock :: BlockId -> CFG ()
cfgNewBlock bid = do
    old <- get
    case cfgPreBlock old of
        Nothing      -> do put (old { cfgPreBlock = Just (Right bid, []) })
        Just (id, _) -> error $ "Tried to start new block "
                               ++ " with unfinished old block " ++ show id

cfgAddMiddle :: Insn O O -> CFG ()
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
                                   ++ " Tried to end with " ++ show last
        Just (stringOrBlockId, mids) -> do
            id <- case stringOrBlockId of
                    Left s -> cfgFresh s
                    Right bid -> return bid
            let first = mkFirst (ILabel id)
            let middles = mkMiddles (Prelude.reverse mids)
            let newblock = first <*> middles <*> mkLast (ILast last)
            put (old { cfgPreBlock     = Nothing
                     , cfgAllBlocks    = newblock : (cfgAllBlocks old) })

-- For all a, CFG a is a UniqueMonad. GHC barfed on trying to use CFG directly.
instance UniqueMonad (State CFGState) where
  freshUnique = cfgNewUniq >>= (return . intToUnique)

knVarSubst id v1 v2 = if id == tidIdent v2 then v1 else v2

-- Replace all uses of  id  with  v  in expr.
knSubst id var expr =
  let substV = knVarSubst id var in
  let substE = knSubst    id var in
  case expr of
    KNTuple vs -> KNTuple (map substV vs)
    KNBool _                -> expr
    KNInt _t _              -> expr
    KNVar v                 -> KNVar        (substV v)
    KNCall t v vs           -> KNCall     t (substV v) (map substV vs)
    KNCallPrim t prim vs    -> KNCallPrim t prim       (map substV vs)
    KNAppCtor t ctor vs     -> KNAppCtor  t ctor       (map substV vs)
    KNAllocArray elt_ty v   -> KNAllocArray elt_ty (substV v)
    KNIf t a b c            -> KNIf        t (substV a) (substE b) (substE c)
    KNUntil t a b           -> KNUntil     t (substE a) (substE b)
    KNAlloc v               -> KNAlloc       (substV v)
    KNDeref v               -> KNDeref       (substV v)
    KNStore v1 v2           -> KNStore       (substV v1) (substV v2)
    KNArrayRead t v1 v2     -> KNArrayRead t (substV v1) (substV v2)
    KNArrayPoke v1 v2 v3    -> KNArrayPoke   (substV v1) (substV v2) (substV v3)
    KNTyApp overallType v t -> KNTyApp overallType (substV v) t
    KNCase t v pes          -> KNCase      t (substV v)
                                             (map (\(p,e) -> (p, substE e)) pes)
    KNLetVal x b e -> if x == id
                        then error $ "knSubst found re-bound id " ++ show id
                        else KNLetVal x (substE b) (substE e)
    KNLetFuns ids fns e ->
                       if id `elem` ids
                        then error $ "knSubst found re--bound id " ++ show id
                        else KNLetFuns ids (map (substFn id var) fns) (substE e)

substFn id var fn =
  let ids = map tidIdent (fnVars fn) in
  if id `elem` ids
    then error $ "knSubstFn found re-bound id " ++ show id
    else fn { fnBody = (knSubst id var (fnBody fn)) }

instance NonLocal Insn where
  entryLabel (ILabel (_,l)) = l
  successors (ILast last) =
    case last of
        CFRetVoid            -> []
        CFRet  _             -> []
        CFBr   b             -> [blockLabel b]
        CFIf _ _ bthen belse -> [blockLabel bthen, blockLabel belse]
        CFCase _ _ patsbids  -> [blockLabel b | (_, b) <- patsbids]
    where blockLabel (_, label) = label

-- Decompose a BasicBlock into a triple of its subpieces.
splitBasicBlock :: BasicBlock -> SplitBasicBlock
splitBasicBlock g =
  case foldGraphNodes split g ([], [], []) of
      ([f], ms, [l]) -> (f, Prelude.reverse ms, l)
      (bs, _, _) -> error $ "splitBasicBlock has wrong # of ids: " ++ show bs
    where
  split :: Insn e x -> SplitBasicBlockIntermediate -> SplitBasicBlockIntermediate
  split   (ILabel   b ) (bs, ms, ls) = (b:bs,   ms,   ls)
  split i@(ILetVal  {}) (bs, ms, ls) = (  bs, i:ms,   ls)
  split i@(ILetFuns {}) (bs, ms, ls) = (  bs, i:ms,   ls)
  split i@(ILast    {}) (bs, ms, ls) = (  bs,   ms, i:ls)

-- We'll accumulate all the first & last nodes from the purported
-- basic block, but the final result must have only one first & last node.
type SplitBasicBlockIntermediate = ([BlockId], [Insn O O], [Insn O C])
type SplitBasicBlock             = ( BlockId,  [Insn O O],  Insn O C )

-- We represent basic blocks as Graphs rather than Blocks because
-- it's easier to glue together Graphs when building the basic blocks.
type BasicBlock = Graph Insn C C
data BasicBlockGraph = BasicBlockGraph { bbgEntry :: BlockId,
                                         bbgBody :: (Graph Insn C C) }
type CFFn = Fn BasicBlockGraph TypeIL

-- We pair a name for later codegen with a label for Hoopl's NonLocal class.
type BlockId = (String, Label)

