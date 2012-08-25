{-# LANGUAGE GADTs, TypeSynonymInstances #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CFG
( computeCFGs
, incrPredecessorsDueTo
, Insn(..)
, BlockId, BlockEntry
, BasicBlockGraph(..)
, BasicBlock
, splitBasicBlock -- used in closure conversion
, CFLast(..)
, CFBody(..)
, CFFn
) where

import Foster.Base
import Foster.TypeIL(TypeIL(..), AIVar, boolTypeIL)
import Foster.KNExpr(KNExpr(..), typeKN, TailQ(..))
import Foster.Letable(Letable(..))

import Compiler.Hoopl

import qualified Data.Text as T
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.State
import Data.IORef
import Prelude hiding (id, last)

data CFBody = CFB_LetFuns [Ident] [CFFn] CFBody
            | CFB_Call    TailQ TypeIL AIVar [AIVar]

-- |||||||||||||||||||| Entry Point & Helpers |||||||||||||||||||{{{

-- This is the "entry point" into CFG-building for the outside.
-- We take (and update) a mutable reference as a convenient way of
-- threading through the small amount of globally-unique state we need.
computeCFGs :: IORef Uniq -> KNExpr -> IO CFBody
computeCFGs uref expr =
  case expr of
    KNLetFuns ids fns body -> do
      cffns <- mapM (computeCFGIO uref) fns
      cfbody <- computeCFGs uref body
      return $ CFB_LetFuns ids cffns cfbody
    -- We've kept a placeholder call to the main function here until now,
    -- but at this point we can get rid of it, since we're convering to a
    -- flat-list representation with an implicit call to main.
    KNCall tq t v vs -> return $ CFB_Call tq t v vs
    _ -> error $ "computeCFGIO expected a series of KNLetFuns bindings! had " ++ show expr

computeCFGIO :: IORef Uniq -> Fn KNExpr TypeIL -> IO CFFn
computeCFGIO uref fn = do
  cfgState <- internalComputeCFG uref fn
  return $ extractFunction cfgState fn

-- A mirror image for internal use (when converting nested functions).
-- As above, we thread through the updated unique value from the subcomputation!
cfgComputeCFG :: Fn KNExpr TypeIL -> CFG CFFn
cfgComputeCFG fn = do
  uref <- gets cfgUniq
  cfgState <- liftIO $ internalComputeCFG uref fn
  return $ extractFunction cfgState fn

-- A helper for the CFG functions above, to run computeBlocks.
internalComputeCFG :: IORef Int -> Fn KNExpr TypeIL -> IO CFGState
internalComputeCFG uniqRef fn = do
  let state0 = CFGState uniqRef Nothing [] Nothing Nothing Nothing Map.empty
  execStateT runComputeBlocks state0
  where
    runComputeBlocks = do
        header <- cfgFresh "postalloca"
        cfgSetHeader header
        retcont <- cfgFresh "rk"
        cfgSetRetCont retcont
        cfgSetFnVar (fnVar fn)
        cfgNewBlock header (fnVars fn)
        computeBlocks (fnBody fn) Nothing (ret fn retcont)

    -- Make sure that the main function returns void.
    ret f k v = if isMain f then cfgEndWith (CFCont k [])
                            else cfgEndWith (CFCont k [v])
            where isMain f = (identPrefix $ tidIdent $ fnVar f) == T.pack "main"

-- The other helper, to collect the scattered results and build the actual CFG.
extractFunction st fn =
  let blocks = Prelude.reverse (cfgAllBlocks st) in
  let elab    = entryLab blocks in
  let (Just rk) = cfgRetCont st in
  fn { fnBody = BasicBlockGraph elab rk (catClosedGraphs blocks)
                                (computeNumPredecessors elab blocks) }
  where -- Dunno why this function isn't in Hoopl...
        catClosedGraphs :: NonLocal i => [Graph i C C] -> Graph i C C
        catClosedGraphs = foldr (|*><*|) emptyClosedGraph

        entryLab [] = error $ "can't get entry block label from empty list!"
        entryLab (bb:_) = lab where (lab, _, _) = splitBasicBlock bb

        computeNumPredecessors elab =
          -- The entry (i.e. postalloca) label will get an incoming edge in LLVM
          let startingMap = Map.singleton (blockId elab) 1 in
          foldr (\bb m ->
                let  (_, _, terminator) = splitBasicBlock bb in
                incrPredecessorsDueTo terminator m) startingMap

blockId :: BlockEntry -> BlockId
blockId = fst

incrPredecessorsDueTo terminator m =
    foldr (\tgt mm -> Map.insertWith (+) tgt 1 mm) m (blockTargetsOf terminator)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

caseIf a b = [(pat True, a), (pat False, b)]
         where pat bval = (P_Bool (error "kn.if.srcrange")
                                  boolTypeIL bval, [])

-- ||||||||||||||||||||||||| KNExpr -> CFG ||||||||||||||||||||||{{{
-- computeBlocks takes an expression and a contination,
-- which determines what to do with the let-bound result of the expression.
computeBlocks :: KNExpr -> Maybe Ident -> (AIVar -> CFG ()) -> CFG ()
computeBlocks expr idmaybe k = do
    case expr of
        KNIf t v a b -> do
            computeBlocks (KNCase t v $ caseIf a b) idmaybe k

        KNUntil _t a b rng -> do
            [until_test, until_body, until_cont] <- mapM cfgFresh
                                      ["until_test", "until_body", "until_cont"]
            cfgEndWith (CFCont until_test [])

            cfgNewBlock until_test []
            computeBlocks a Nothing $ \var -> cfgEndWith
                                     (CFCase var (caseIf until_cont until_body))

            cfgNewBlock until_body []
            computeBlocks b Nothing $ \_ -> cfgEndWith (CFCont until_test [])

            cfgNewBlock until_cont []
            cfgAddLet idmaybe (ILTuple [] (AllocationSource "until" rng))
                              (TupleTypeIL []) >>= k

        KNLetVal id (KNVar v) expr -> do
            cont <- cfgFresh "rebind_cont"
            cfgEndWith (CFCont cont [v])
            cfgNewBlock      cont [TypedId (tidType v) id]
            computeBlocks expr idmaybe k

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
        -- during match compilation, and delaying pattern match compilation
        -- makes closure conversion somewhat easier.
        --
        -- A case expression of overall type t, such as
        --
        --      case scrutinee of p1 -> e1
        --                     of p2 -> e2 ...
        --
        -- gets translated into (the moral equivalent of)
        --
        --      case scrutinee of p1 -> goto case_arm1
        --                     of p2 -> goto case_arm2 ...
        --  case_arm1: ev = [[e1]]; goto case_cont [ev]
        --  case_arm2: ev = [[e2]]; goto case_cont [ev]
        --  case_cont [case_value]:
        --      ...
        --
        -- The one point this glosses over is how the variables bound by
        -- p1 become visible in the translation of e1. Currently this is
        -- done by some magic in LLCodegen, but it should be represented
        -- more explicitly.
        KNCase t v bs -> do
            -- Compute the new block ids, along with their patterns.
            bids <- mapM (\_ -> cfgFresh "case_arm") bs
            let bbs = zip (map fst bs) bids
            cfgEndWith (CFCase v bbs)

            case_cont <- cfgFresh "case_cont"

            -- Fill in each arm's block with [[e]] (and a store at the end).
            let computeCaseBlocks (e, (_, block_id)) = do
                    cfgNewBlock block_id []
                    computeBlocks e Nothing $ \var ->
                        cfgEndWith (CFCont case_cont [var])
            mapM_ computeCaseBlocks (zip (map snd bs) bbs)

            -- The overall value of the case is the value stored in the slot.
            phi <- cfgFreshVarI idmaybe t ".case.phi"
            cfgNewBlock case_cont [phi]
            k phi

        (KNCall srctail ty b vs) -> do
            -- We can't just compare [[b == fnvar]] because b might be a
            -- let-bound result of type-instantiating a polymorphic function.
            isTailCall <- cfgIsThisFnVar b
            case (srctail, isTailCall) of
                -- Direct tail recursion becomes a jump
                -- (reassigning the arg slots).
                (YesTail, True) -> do
                    Just header <- gets cfgHeader
                    cfgEndWith (CFCont header vs)

                -- Calls to other functions in tail position use the function's
                -- return continuation rather than a new continuation.
                (YesTail, False) -> do
                    Just retk <- gets cfgRetCont
                    cfgEndWith (CFCall retk ty b vs)

                -- Non-tail calls specify a new block as their continuation,
                -- and the block's parameter becomes the result of the call.
                (_, _) -> do
                    cont <- cfgFresh "call_cont"
                    res  <- cfgFreshVarI idmaybe ty "call_res"
                    cfgEndWith (CFCall cont ty b vs)
                    cfgNewBlock cont [res]
                    k res

        KNVar v -> k v
        _ -> do cfgAddLet idmaybe (knToLetable expr) (typeKN expr) >>= k
  where
    knToLetable :: KNExpr -> Letable
    knToLetable expr =
      case expr of
         KNVar        _v     -> error $ "can't make Letable from KNVar!"
         KNString     s      -> ILText       s
         KNBool       b      -> ILBool       b
         KNInt        t i    -> ILInt        t i
         KNFloat      t f    -> ILFloat      t f
         KNTuple      vs rng -> ILTuple      vs (AllocationSource "tuple" rng)
         KNCallPrim   t p vs -> ILCallPrim   t p vs
         KNAppCtor    t c vs -> ILAppCtor    t c vs
         KNAlloc      v rgn  -> ILAlloc      v rgn
         KNDeref      v      -> ILDeref      v
         KNStore      a b    -> ILStore      a b
         KNAllocArray t v    -> ILAllocArray t v
         KNArrayRead  t ari  -> ILArrayRead  t ari
         KNArrayPoke  ari c  -> ILArrayPoke  ari c
         KNTyApp t v argtys  -> ILTyApp t v argtys
         KNKillProcess t m   -> ILKillProcess t m
         _                   -> error $ "non-letable thing seen by letable: "
                                      ++ show expr

    cfgFreshVarI idmaybe t n = do
        id <- (case idmaybe of
                Just id -> return id
                Nothing -> cfgFreshId n)
        return $ TypedId t id

    cfgAddLet :: Maybe Ident -> Letable -> TypeIL -> CFG AIVar
    cfgAddLet idmaybe letable ty = do
        tid@(TypedId _ id) <- cfgFreshVarI idmaybe ty ".cfg_seq"
        cfgAddMiddle (ILetVal id letable)
        Just fnvar <- gets cfgCurrentFnVar
        case letable of
            ILTyApp _ v _ | v == fnvar -> cfgAddFnVarAlias id fnvar
            _                          -> return ()
        return tid

    cfgFreshId :: String -> CFG Ident
    cfgFreshId s = do u <- cfgNewUniq ; return (Ident (T.pack s) u)

    cfgAddMiddle :: Insn O O -> CFG ()
    cfgAddMiddle mid = do
        old <- get
        case cfgPreBlock old of
            Just (id, phis, mids) -> do put (old { cfgPreBlock = Just (id, phis, mid:mids) })
            Nothing         -> error $ "Tried to add middle without a block"
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||| CFG Monadic Helpers ||||||||||||||||||||{{{
cfgEndWith :: CFLast -> CFG ()
cfgEndWith last = do
    old <- get
    case cfgPreBlock old of
        Nothing          -> error $ "Tried to finish block but no preblock!"
                                   ++ " Tried to end with " ++ show last
        Just (id, phis, mids) -> do
            let first = mkFirst (ILabel (id, phis))
            let middles = mkMiddles (Prelude.reverse mids)
            let newblock = first <*> middles <*> mkLast (ILast last)
            put (old { cfgPreBlock     = Nothing
                     , cfgAllBlocks    = newblock : (cfgAllBlocks old) })

cfgNewBlock :: BlockId -> [AIVar] -> CFG ()
cfgNewBlock bid phis = do
    old <- get
    case cfgPreBlock old of
        Nothing      -> do put (old { cfgPreBlock = Just (bid, phis, []) })
        Just (id, _, _) -> error $ "Tried to start new block "
                               ++ " with unfinished old block " ++ show id

cfgFresh :: String -> CFG BlockId
cfgFresh s = do u <- freshLabel ; return (s, u)

cfgNewUniq :: CFG Uniq
cfgNewUniq = do uref <- gets cfgUniq ; mutIORef uref (+1)
  where
    mutIORef :: IORef a -> (a -> a) -> CFG a
    mutIORef r f = liftIO $ modifyIORef r f >> readIORef r

cfgSetHeader header = do old <- get ; put old { cfgHeader = Just header }
cfgSetRetCont retcont = do old <- get ; put old { cfgRetCont = Just retcont }
cfgSetFnVar fnvar = do old <- get ; put old { cfgCurrentFnVar = Just fnvar }

cfgAddFnVarAlias :: Ident -> AIVar -> CFG ()
cfgAddFnVarAlias i v = do old <- get
                          let ama = cfgKnownFnVars old
                          put old { cfgKnownFnVars = Map.insert i v ama }

cfgIsThisFnVar :: AIVar -> CFG Bool
cfgIsThisFnVar b = do old <- get
                      let v = cfgCurrentFnVar old
                      return $ Just b == v || Map.lookup (tidIdent b) (cfgKnownFnVars old) == v

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||| CFG Data Types |||||||||||||||||||||||{{{
data CFLast = CFCont        BlockId [AIVar] -- either ret or br
            | CFCall        BlockId TypeIL AIVar [AIVar]
            | CFCase        AIVar [PatternBinding BlockId TypeIL]
            deriving (Show)

data Insn e x where
              ILabel   :: BlockEntry         -> Insn C O
              ILetVal  :: Ident   -> Letable -> Insn O O
              ILetFuns :: [Ident] -> [CFFn]  -> Insn O O
              ILast    :: CFLast             -> Insn O C

data CFGState = CFGState {
    cfgUniq         :: IORef Uniq
  , cfgPreBlock     :: Maybe (BlockId, [AIVar], [Insn O O])
  , cfgAllBlocks    :: [BasicBlock]
  , cfgHeader       :: Maybe BlockId
  , cfgRetCont      :: Maybe BlockId
  , cfgCurrentFnVar :: Maybe AIVar
  , cfgKnownFnVars  :: Map Ident AIVar
}

type CFG = StateT CFGState IO
instance UniqueMonad CFG where freshUnique = cfgNewUniq >>= return . intToUnique

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

instance NonLocal Insn where
  entryLabel (ILabel ((_,l), _)) = l
  successors (ILast last) = map blockLabel (blockTargetsOf (ILast last))
                          where blockLabel (_, label) = label

blockTargetsOf :: Insn O C -> [BlockId]
blockTargetsOf (ILast last) =
    case last of
        CFCont b _           -> [b]
        CFCall b _ _ _       -> [b]
        CFCase _ patsbids    -> [b | (_, b) <- patsbids]

-- Decompose a BasicBlock into a triple of its subpieces.
splitBasicBlock :: BasicBlock -> SplitBasicBlock
splitBasicBlock g =
  case foldGraphNodes split g ([], [], []) of
      ([f], ms, [l]) -> (f, Prelude.reverse ms, l)
      (bs, _, _) -> error $ "splitBasicBlock has wrong # of ids: " ++ show bs
    where
  split :: Insn e x -> SplitBasicBlockIntermediate -> SplitBasicBlockIntermediate
  split   (ILabel  b  ) (bs, ms, ls) = (b:bs,   ms,   ls)
  split i@(ILetVal  {}) (bs, ms, ls) = (  bs, i:ms,   ls)
  split i@(ILetFuns {}) (bs, ms, ls) = (  bs, i:ms,   ls)
  split i@(ILast    {}) (bs, ms, ls) = (  bs,   ms, i:ls)

-- We'll accumulate all the first & last nodes from the purported
-- basic block, but the final result must have only one first & last node.
type SplitBasicBlockIntermediate = ([BlockEntry], [Insn O O], [Insn O C])
type SplitBasicBlock             = ( BlockEntry,  [Insn O O],  Insn O C )

-- We represent basic blocks as Graphs rather than Blocks because
-- it's easier to glue together Graphs when building the basic blocks.
type BasicBlock = Graph Insn C C
data BasicBlockGraph = BasicBlockGraph { bbgEntry :: BlockEntry
                                       , bbgRetK  :: BlockId
                                       , bbgBody  :: BasicBlock
                                       , bbgNumPreds :: Map BlockId Int }
type CFFn = Fn BasicBlockGraph TypeIL
type BlockEntry = (BlockId, [TypedId TypeIL])

-- We pair a name for later codegen with a label for Hoopl's NonLocal class.
type BlockId = (String, Label)

