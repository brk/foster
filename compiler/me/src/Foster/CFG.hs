{-# LANGUAGE GADTs, TypeSynonymInstances, RankNTypes, ScopedTypeVariables,
             PatternGuards, TypeFamilies, DoRec, NoMonoLocalBinds #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CFG
( computeCFGs
, Insn(..)
, BlockId, BlockEntry'
, BasicBlockGraph(..)
, BasicBlock
, CFLast(..)
, CFBody(..)
, CFFn
, renderCFG
, blockId
, blockTargetsOf
, rebuildGraphM
, rebuildGraphAccM
, graphOfClosedBlocks
, runWithUniqAndFuel
, M
, FosterNode(..)
) where

import Foster.Base
import Foster.MonoType
import Foster.KNExpr(KNExpr'(..), typeKN, TailQ(..))
import Foster.Letable(Letable(..), isPure)

import Compiler.Hoopl
import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.Boxes as Boxes

import Debug.Trace(trace)

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map(Map)
import Data.Set(Set)
import Data.Maybe(fromMaybe, fromJust, isJust)
import Data.List(nubBy, last)
import Control.Monad.State
import Data.IORef
import Prelude hiding (id, last)

data CFBody = CFB_LetFuns [Ident] [CFFn] CFBody
            | CFB_Call    TailQ MonoType MoVar [MoVar]

type KNMono = KNExpr' MonoType

-- |||||||||||||||||||| Entry Point & Helpers |||||||||||||||||||{{{

-- This is the "entry point" into CFG-building for the outside.
-- We take (and update) a mutable reference as a convenient way of
-- threading through the small amount of globally-unique state we need.
computeCFGs :: IORef Uniq -> KNMono -> IO CFBody
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

computeCFGIO :: IORef Uniq -> Fn (KNMono) MonoType -> IO CFFn
computeCFGIO uref fn = do
  cfgState <- internalComputeCFG uref fn
  extractFunction cfgState fn

-- A mirror image for internal use (when converting nested functions).
-- As above, we thread through the updated unique value from the subcomputation!
cfgComputeCFG :: Fn (KNMono) MonoType -> CFG CFFn
cfgComputeCFG fn = do
  uref <- gets cfgUniq
  cfgState <- liftIO $ internalComputeCFG uref fn
  liftIO $ extractFunction cfgState fn

-- A helper for the CFG functions above, to run computeBlocks.
internalComputeCFG :: IORef Int -> Fn (KNMono) MonoType -> IO CFGState
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
    ret :: forall ty expr. Fn expr ty -> BlockId -> MoVar -> CFG ()
    ret f k v = if isMain f then cfgEndWith (CFCont k [])
                            else cfgEndWith (CFCont k [v])
            where isMain :: forall ty expr. Fn expr ty -> Bool
                  isMain f = (identPrefix $ tidIdent $ fnVar f) == T.pack "main"

-- The other helper, to collect the scattered results and build the actual CFG.
extractFunction :: CFGState -> Fn KNMono MonoType -> IO CFFn
extractFunction st fn = do
  let blocks = Prelude.reverse (cfgAllBlocks st)
  let elab    = entryLab blocks
  let (Just rk) = cfgRetCont st
  let bbg = BasicBlockGraph elab rk (catClosedGraphs (map blockGraph blocks))

  let optimizations = [ elimContInBBG
                      , runCensusRewrites' , elimContInBBG
                     -- ,runLiveness
                      ]
  bbgs <- scanlM (\bbg opt -> opt (cfgUniq st) bbg) bbg optimizations

  putStrLn "BEFORE/AFTER"
  let sndEq (_, a) (_, b) = a == b
  let annotate (n, s) = s ++ "\n        (stage " ++ show n ++ ")"
  let catboxes bbgs = Boxes.hsep 1 Boxes.left $ map (boxify . measure . annotate) $
                            (nubBy sndEq $ zip [1..] $ map (show . pretty) bbgs)
  -- Discards duplicates before annotating
  Boxes.printBox $ catboxes bbgs
  putStrLn ""

  let bbg' = last bbgs
  let jumpTo bbg = case bbgEntry bbg of (bid, _) -> ILast $ CFCont bid undefined
  Boxes.printBox $ catboxes $ map blockGraph $
                     preorder_dfs $ mkLast (jumpTo bbg') |*><*| bbgBody bbg'
  return $ fn { fnBody = bbg' }
  where
        entryLab :: forall x. [Block Insn C x] -> BlockEntry
        entryLab [] = error $ "can't get entry block label from empty list!"
        entryLab (bb:_) = let (ILabel elab) = firstNode bb in elab

blockId :: BlockEntry' t -> BlockId
blockId = fst

measure :: String -> Boxes.Box
measure s = Boxes.vcat Boxes.left (map Boxes.text $ lines s)

boxify :: Boxes.Box -> Boxes.Box
boxify b = v Boxes.<> (h Boxes.// b Boxes.// h) Boxes.<> v
             where v = Boxes.vcat Boxes.left (take (Boxes.rows b + 2) (repeat (Boxes.char '|')))
                   h = Boxes.text $          (take (Boxes.cols b    ) (repeat '-'))

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

caseIf a b = [(pat True, a), (pat False, b)]
         where pat :: forall a. Bool -> (Pattern MonoType, [a])
               pat bval = (P_Bool (error "kn.if.srcrange")
                                  boolMonoType bval, [])

-- ||||||||||||||||||||||||| KNMono -> CFG ||||||||||||||||||||||{{{
-- computeBlocks takes an expression and a contination,
-- which determines what to do with the let-bound result of the expression.
computeBlocks :: KNMono -> Maybe Ident -> (MoVar -> CFG ()) -> CFG ()
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
                              (TupleType []) >>= k

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
            let computeCaseBlocks :: forall t. (KNMono, (t, BlockId)) -> CFG ()
                computeCaseBlocks (e, (_, block_id)) = do
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
    knToLetable :: KNMono -> Letable MonoType
    knToLetable expr =
      case expr of
         KNVar        _v     -> error $ "can't make Letable from KNVar!"
         KNString   _ s      -> ILText       s
         KNBool     _ b      -> ILBool       b
         KNInt        t i    -> ILInt        t i
         KNFloat      t f    -> ILFloat      t f
         KNTuple    _ vs rng -> ILTuple      vs (AllocationSource "tuple" rng)
         KNCallPrim   t p vs -> ILCallPrim   t p vs
         KNAppCtor    t c vs -> ILAppCtor    t c vs
         KNAlloc    _ v rgn  -> ILAlloc      v rgn
         KNDeref    t v      -> ILDeref      t v
         KNStore    _ a b    -> ILStore      a b
         KNAllocArray t v    -> ILAllocArray t v
         KNArrayRead  t ari  -> ILArrayRead  t ari
         KNArrayPoke  _ ari c-> ILArrayPoke  ari c
         KNTyApp      t v [] -> ILBitcast    t v
         KNTyApp          {} -> error $ "knToLetable saw tyapp that was not "
                                      ++ "eliminated by monomorphization: "
                                      ++ show expr
         KNKillProcess t m   -> ILKillProcess t m
         _                   -> error $ "non-letable thing seen by letable: "
                                      ++ show expr

    cfgFreshVarI idmaybe t n = do
        id <- (case idmaybe of
                Just id -> return id
                Nothing -> cfgFreshId n)
        return $ TypedId t id

    cfgAddLet :: Maybe Ident -> Letable MonoType -> MonoType -> CFG MoVar
    cfgAddLet idmaybe letable ty = do
        tid@(TypedId _ id) <- cfgFreshVarI idmaybe ty ".cfg_seq"
        cfgAddMiddle (ILetVal id letable)
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
            let middles = blockFromList (Prelude.reverse mids)
            let newblock = blockJoin (ILabel (id, phis)) middles (ILast last)
            put (old { cfgPreBlock     = Nothing
                     , cfgAllBlocks    = newblock : (cfgAllBlocks old) })

cfgNewBlock :: BlockId -> [MoVar] -> CFG ()
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

cfgSetHeader header   = do old <- get ; put old { cfgHeader = Just header }
cfgSetRetCont retcont = do old <- get ; put old { cfgRetCont = Just retcont }
cfgSetFnVar fnvar = do old <- get ; put old { cfgCurrentFnVar = Just fnvar }

cfgIsThisFnVar :: MoVar -> CFG Bool
cfgIsThisFnVar b = do old <- get
                      let v = cfgCurrentFnVar old
                      return $ Just b == v || Map.lookup (tidIdent b) (cfgKnownFnVars old) == v

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||| CFG Data Types |||||||||||||||||||||||{{{
data CFLast = CFCont        BlockId [MoVar] -- either ret or br
            | CFCall        BlockId MonoType MoVar [MoVar]
            | CFCase        MoVar [PatternBinding BlockId MonoType]
            deriving (Show)

data Insn e x where
              ILabel   :: BlockEntry                  -> Insn C O
              ILetVal  :: Ident   -> Letable MonoType -> Insn O O
              ILetFuns :: [Ident] -> [CFFn]           -> Insn O O
              ILast    :: CFLast                      -> Insn O C

data CFGState = CFGState {
    cfgUniq         :: IORef Uniq
  , cfgPreBlock     :: Maybe (BlockId, [MoVar], [Insn O O])
  , cfgAllBlocks    :: [BasicBlock]
  , cfgHeader       :: Maybe BlockId
  , cfgRetCont      :: Maybe BlockId
  , cfgCurrentFnVar :: Maybe MoVar
  , cfgKnownFnVars  :: Map Ident MoVar
}

type CFG = StateT CFGState IO
instance UniqueMonad CFG where freshUnique = cfgNewUniq >>= return . intToUnique

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

instance NonLocal Insn where
  entryLabel (ILabel ((_,l), _)) = l
  successors (ILast last) = map blockLabel (blockTargetsOf (ILast last))
                          where blockLabel (_, label) = label

instance HooplNode Insn where
  mkBranchNode l = ILast (CFCont ("hoopl.br", l)  [])
  mkLabelNode  l = ILabel       (("hoopl.br", l), [])

blockTargetsOf :: Insn O C -> [BlockId]
blockTargetsOf (ILast last) =
    case last of
        CFCont b _           -> [b]
        CFCall b _ _ _       -> [b]
        CFCase _ patsbids    -> [b | (_, b) <- patsbids]

type BasicBlock = Block Insn C C
data BasicBlockGraph = BasicBlockGraph { bbgEntry :: BlockEntry
                                       , bbgRetK  :: BlockId
                                       , bbgBody  :: Graph Insn C C
                                       }
type CFFn = Fn BasicBlockGraph MonoType
type BlockEntry = BlockEntry' MonoType
type BlockEntry' t = (BlockId, [TypedId t])

-- We pair a name for later codegen with a label for Hoopl's NonLocal class.
type BlockId = (String, Label)


-- ||||||||||||||||||||| CFG Pretty Printing ||||||||||||||||||||{{{

renderCFG :: (ModuleIL CFBody MonoType) -> Bool -> IO (Either () String)
renderCFG cfg put = if put then putDoc (pretty cfg) >>= (return . Left)
                        else return . Right $ show (pretty cfg)

comment d = text "/*" <+> d <+> text "*/"

prettyId (TypedId _ i) = text (show i)

showTyped :: Doc -> MonoType -> Doc
showTyped d t = parens (d <+> text "::" <+> pretty t)

instance Pretty (Fn BasicBlockGraph MonoType) where
  pretty fn = group (lbrace <+>
                         (align (vcat (map (\v -> showTyped (pretty v) (tidType v) <+> text "=>")
                                (fnVars fn))))
                    <$> indent 4 (pretty (fnBody fn))
                    <$> rbrace)
                    -- <$> (pretty $ Map.toList $ getCensus (fnBody fn))

instance Pretty Label where pretty l = text (show l)

instance Pretty BasicBlock where
  pretty bb = foldBlockNodesF prettyInsn bb empty

instance Pretty (Graph Insn C C) where
  pretty bg = foldGraphNodes  prettyInsn bg empty

prettyInsn :: Insn e x -> Doc -> Doc
prettyInsn i d = d <$> pretty i

prettyBlockId (b,l) = text b <> text "." <> text (show l)

instance Pretty (Insn e x) where
  pretty (ILabel   bentry     ) = line <> prettyBlockId (fst bentry) <+> list (map pretty (snd bentry))
  pretty (ILetVal  id  letable) = indent 4 (text "let" <+> text (show id) <+> text "="
                                                       <+> pretty letable)
  pretty (ILetFuns ids fns    ) = let recfun = if length ids == 1 then "fun" else "rec" in
                                  indent 4 (align $
                                   vcat [text recfun <+> text (show id) <+> text "=" <+> pretty fn
                                        | (id,fn) <- zip ids fns])
  pretty (ILast    cf         ) = pretty cf

instance Pretty CFLast where
  pretty (CFCont bid     vs) = text "cont" <+> prettyBlockId bid <+>              list (map pretty vs)
  pretty (CFCall bid _ v vs) = text "call" <+> prettyBlockId bid <+> pretty v <+> list (map pretty vs)
  pretty (CFCase v pats)    = align $
                               text "case" <+> pretty v <$> indent 2
                                  (vcat [ text "of" <+> fill 20 (pretty pat) <+> text "->" <+> prettyBlockId bid
                                        | ((pat, _tys), bid) <- pats
                                        ])

instance Pretty t => Pretty (Letable t) where
  pretty l =
    case l of
      ILText      s         -> string (T.unpack s)
      ILBool      b         -> text (if b then "True" else "False")
      ILInt       _ i       -> text (litIntText i)
      ILFloat     _ f       -> text (litFloatText f)
      ILTuple     vs _asrc  -> parens (hsep $ punctuate comma (map pretty vs))
      ILKillProcess t m     -> text ("prim KillProcess " ++ show m ++ " :: ") <> pretty t
      ILOccurrence  _ v occ -> prettyOccurrence v occ
      ILCallPrim  _ p vs    -> (text "prim" <+> pretty p <+> hsep (map prettyId vs))
      ILCall      _ v vs    -> pretty v <+> hsep (map pretty vs)
      ILAppCtor   _ c vs    -> (text "~" <> parens (text (ctorCtorName (ctorInfoId c)) <+> hsep (map prettyId vs)))
      ILAlloc     v rgn     -> text "(ref" <+> pretty v <+> comment (pretty rgn) <> text ")"
      ILDeref     t v       -> pretty v <> text "^"
      ILStore     v1 v2     -> text "store" <+> pretty v1 <+> text "to" <+> pretty v2
      ILAllocArray _ _v     -> text $ "ILAllocArray..."
      ILArrayRead  _t (ArrayIndex _v1 _v2 _rng _s)  -> text $ "ILArrayRead..."
      ILArrayPoke  (ArrayIndex _v1 _v2 _rng _s) _v3 -> text $ "ILArrayPoke..."
      ILBitcast   t v       -> text "bitcast " <+> pretty v <+> text "to" <+> text "..."
      ILAllocate info       -> text "allocate " <+> pretty (allocType info)

instance Pretty BasicBlockGraph where
 pretty bbg =
         (indent 4 (text "ret k =" <+> pretty (bbgRetK bbg)
                <$> text "entry =" <+> pretty (fst $ bbgEntry bbg)
                <$> text "------------------------------"))
          <> pretty (bbgBody bbg)

instance Pretty CFBody where
  pretty (CFB_LetFuns ids fns body) =
                                   text "letfuns"
                                   <$> indent 2 (vcat [text (show id) <+> text "="
                                                                      <+> pretty fn
                                                      | (id, fn) <- zip ids fns
                                                      ])
                                   <$> text "in"
                                   <$> pretty body
                                   <$> text "end"
  pretty (CFB_Call {}) = text "call main..."

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

graphOfClosedBlocks :: NonLocal i => [Block i C C] -> Graph i C C
graphOfClosedBlocks = foldr ((|*><*|) . blockGraph) emptyClosedGraph

class FosterNode i where branchTo :: BlockId -> i O C

instance FosterNode Insn where branchTo bid = ILast $ CFCont bid []

 -- Dunno why this function isn't in Hoopl...
catClosedGraphs :: NonLocal i => [Graph i C C] -> Graph i C C
catClosedGraphs = foldr (|*><*|) emptyClosedGraph

-- ||||||||||||||||||||||||||| UniqMonadIO ||||||||||||||||||||||{{{
-- Basically a copy of UniqueMonadT, specialized to IO, with a
-- more suitable "run" function, and using Uniq instead of Unique.
newtype UniqMonadIO a = UMT { unUMT :: [Uniq] -> IO (a, [Uniq]) }

instance Monad UniqMonadIO where
  return a = UMT $ \us -> return (a, us)
  m >>= k  = UMT $ \us -> do { (a, us') <- unUMT m us; unUMT (k a) us' }

instance UniqueMonad UniqMonadIO where
  freshUnique = UMT $ f
    where f (u:us) = return (intToUnique u, us)
          f _ = error "freshUnique(UniqMonadIO): empty list"

runUniqMonadIO :: [Uniq] -> UniqMonadIO a -> IO (a, Uniq)
runUniqMonadIO uniques m = do { (a, u) <- unUMT m uniques; return (a, head u) }

instance CheckpointMonad UniqMonadIO where
  type Checkpoint UniqMonadIO = [Uniq]
  checkpoint = UMT $ \us -> return (us, us)
  restart us = UMT $ \_  -> return ((), us)

-- We can't use the IORef directly as a source of uniques,
-- due to the requirement for checkpointing. But in order to
-- avoid generating duplicate labels, we also need to not discard
-- the final state of the unique generator (which SimpleUniqueMonad does).
-- Thus all this nonsense.
runWithUniqAndFuel :: IORef Uniq -> Fuel -> M a -> IO a
runWithUniqAndFuel r f x = do startUniq <- readIORef r
                              let usrc = [startUniq..]
                              (v, u) <- runUniqMonadIO usrc (runWithFuel f x)
                              writeIORef r (u + 1)
                              return v

type M a = InfiniteFuelMonad UniqMonadIO a
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||||| CFG Analysis ||||||||||||||||||||||{{{
instance Pretty Ident where pretty id = text (show id)
instance LabelsPtr (BlockId, ts) where targetLabels ((_, label), _) = [label]
instance Pretty (Set.Set HowUsed) where pretty s = string (show s)

-- Simplified interface for rebuilding graphs in the common case where
-- the client doesn't want to bother threading any state through.
rebuildGraphM :: (Monad m, NonLocal o, FosterNode i, NonLocal i)
                         => BlockId -> Graph i C C
                         -> (forall e x. i e x -> m (Graph o e x))
                         -> m (Graph o C C)
rebuildGraphM entrybid body transform = do
  let transform' () insn = do g <- transform insn; return (g, ())
  (g, ()) <- rebuildGraphAccM entrybid body () transform'
  return g

-- More complete interface supporting threaded state.
rebuildGraphAccM :: (Monad m, NonLocal o, FosterNode i, NonLocal i)
                         => BlockId -> Graph i C C -> acc
                         -> (forall e x. acc -> i e x -> m (Graph o e x, acc))
                         -> m (Graph o C C, acc)
rebuildGraphAccM entrybid body init transform = do
   let rebuildBlockGraph blk_cc acc0 = do {
      ; let (f, ms, l) = unblock ( blockSplit blk_cc )
      ; (fg, acc1) <- transform acc0 f
      ; (gs, accn) <- mapFoldM' ms acc1 (\insn acc -> transform acc insn)
      ; (lg, accm) <- transform accn l
      ; return $ (fg <*> catGraphs gs <*> lg, accm)
   }
   let blocks = postorder_dfs (mkLast (branchTo entrybid) |*><*| body)
   (mb, acc) <- mapFoldM' blocks init rebuildBlockGraph
   return $ (catClosedGraphs mb, acc)
  where
   unblock (f, ms_blk, l) = (f, blockToList ms_blk, l)

-- |||||||||||||||||||| Cont-Cont Elimination |||||||||||||||||||{{{
--data Renamer   = Renamer BlockId (Maybe ([MoVar] -> [MoVar]))
--instance Show Renamer where show (Renamer bid _) = "(Renamer " ++ show bid ++ ")"

data CFGTrivia = CFGTrivia { cfgTrivEndsCont   :: Maybe (BlockId, [MoVar])
                           , cfgTrivEquivs     :: Map.Map BlockId BlockId
                           } deriving Show

elimContInBBG :: IORef Uniq -> BasicBlockGraph -> IO BasicBlockGraph
elimContInBBG uref bbg = runWithUniqAndFuel uref infiniteFuel (elimContInBBG' bbg)
  where elimContInBBG' :: BasicBlockGraph -> M BasicBlockGraph
        elimContInBBG' bbg = do
         (bb', _, _) <- analyzeAndRewriteBwd bwd (JustC [bbgEntry bbg])
                                                        (bbgBody  bbg)
                                                        mapEmpty
         return $ bbg { bbgBody = bb' }

        _bwd = debugBwdTransfers trace showing (\_ _ -> True) bwd
        bwd = BwdPass { bp_lattice  = contEquivLattice
                      , bp_transfer = contContFind
                      , bp_rewrite  = contContElim
                      }

        contEquivLattice :: DataflowLattice CFGTrivia
        contEquivLattice = DataflowLattice
                          { fact_name = "Continuned continuations"
                          , fact_bot  = CFGTrivia Nothing Map.empty
                          , fact_join = fj
                          }
                            where fj _ (OldFact old) (NewFact new) = (ch, j)
                                    where
                                      j = (CFGTrivia Nothing m)
                                      o = cfgTrivEquivs old
                                      m = Map.union o (cfgTrivEquivs new)
                                      ch = changeIf (Map.size m > Map.size o)

        contContFind :: BwdTransfer Insn CFGTrivia
        contContFind = mkBTransfer go
          where
            go :: Insn e x -> Fact x CFGTrivia -> CFGTrivia
            go (ILabel   (bid, vs)   ) s =
                 let s' = s { cfgTrivEndsCont = Nothing } in
                 case {-trace ("F("++show bid++")") $-} cfgTrivEndsCont s of
                   Just (otherid, ovs) ->
                       if bid /= otherid && vs == ovs
                         then -- let o = Renamer otherid (renamerFunc vs ovs) in
                              s' { cfgTrivEquivs = Map.insert bid otherid (cfgTrivEquivs s') }
                         else s'
                   Nothing -> s'
            go (ILetVal  {}         ) s = s { cfgTrivEndsCont = Nothing }
            go (ILetFuns _ids _fns  ) s = s { cfgTrivEndsCont = Nothing }
            go node@(ILast    cf    ) fdb =
              let s = joinFacts contEquivLattice (error "fake label") (successorFacts' node fdb) in
              --let s = {-trace ("fact base F: " ++ showFactBase fdb) $-}
              --          joinOutFacts' contEquivLattice node fdb in
              case cf of
                    (CFCont bid vs) -> s { cfgTrivEndsCont = Just (bid, vs) }
                    (CFCall {})     -> s { cfgTrivEndsCont = Nothing }
                    (CFCase {})     -> s { cfgTrivEndsCont = Nothing }

            -- Example to illuminate what these variable names mean:
            --     k []    = j [a,b]      ==> k []    = c [b,z,a]
            --     j [x,y] = c [y,z,x]    ==> ...
            -- bid/vs is j/[x,y], otherid/ovs is c/[y,z,x], & [a,b] (will b) avs
            renamerFunc vs ovs = if vs == ovs then Nothing
                                   else Just (\avs -> applySubst
                                                     (buildSubst vs avs) ovs)
            buildSubst oldvars newvars = Map.fromList (zip oldvars newvars)
            applySubst subst   tgtvars = map (\v -> Map.findWithDefault v v subst) tgtvars

            fact :: FactBase CFGTrivia -> Label -> CFGTrivia
            fact f l = fromMaybe (fact_bot contEquivLattice) $ lookupFact l f

            successorFacts' :: NonLocal n => n O C -> FactBase f -> [f]
            successorFacts' n fb = [ fromJust f | id <- successors n,
                                            let f = lookupFact id fb, isJust f ]

        contContElim :: FuelMonad m => BwdRewrite m Insn CFGTrivia
        contContElim = mkBRewrite d
          where
            d :: FuelMonad m => Insn e x -> Fact x CFGTrivia -> m (Maybe (Graph Insn e x))
            d (ILast (CFCont bid     vs)) triv = return $ rw bid triv
                            --(\(Renamer newbid mf) -> CFCont newbid (r mf vs))
                                            (\newbid -> CFCont newbid vs)
            --d (ILast (CFCall bid t v vs)) triv = return $ rw bid triv
            --                --(\(Renamer newbid mf) -> case mf of Nothing -> CFCall newbid t v vs
            --                --                                    Just _  -> CFCall    bid t v vs)
            d _ _ = return Nothing

            -- r Nothing  vs =   vs
            -- r (Just f) vs = f vs

            rw :: BlockId -> FactBase CFGTrivia -> (BlockId -> CFLast) -> Maybe (Graph Insn O C)
            rw bid@(_,lab) fdb k =
              case lookupFact lab fdb of
                Nothing -> Nothing
                Just triv ->
                  case Map.lookup bid (cfgTrivEquivs triv) of
                    Just otherid -> Just $ mkLast (ILast $ k otherid)
                    Nothing      -> Nothing

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| Census-based Rewrites |||||||||||||||||||{{{
data RecStatus = YesRec | NotRec deriving (Eq, Ord, Show)
data HowUsed = UnknownCall BlockId
             | KnownCall   BlockId {- provided cont; -}
                           (RecStatus,BlockId) {- of known fn entry point -}
             | UsedFirstClass | UsedSecondClass -- as cont arg
                 deriving (Eq, Ord, Show)

type CenFuns = Map.Map Ident CFFn

-- Build a mapping from the (local, not global) idents to the
-- locally-defined (and thus known) functions they are bound to.
getCensusFns :: BasicBlockGraph -> CenFuns
getCensusFns bbg = gobbg bbg Map.empty
  where
    gobbg bbg m = foldGraphNodes go (bbgBody bbg) m

    go :: Insn e x -> CenFuns -> CenFuns
    go (ILetFuns ids fns    ) m = foldr gobbg m' (map fnBody fns)
                                   where m' = Map.union m $ Map.fromList (zip ids fns)
    go _                      m = m

type Census = Map.Map Ident (Set.Set HowUsed)

getCensus :: BasicBlockGraph -> Census
getCensus bbg = let cf = getCensusFns bbg in
                getCensusForFn cf bbg Map.empty
  where
    addUsed c lst = Map.unionWith Set.union c
                                (Map.fromList [(tidIdent v, Set.singleton u)
                                              | (v, u) <- lst])

    getCensusForFn cf bbg m = foldGraphNodes (go cf) (bbgBody bbg) m

    go :: CenFuns -> Insn e x -> Census -> Census
    go _  (ILabel   _bentry    ) m = m
    go _  (ILetVal  _id letable) m = censusLetable letable m
    go cf (ILetFuns _ids fns   ) m = foldr (getCensusForFn cf) m (map fnBody fns)
    go cf (ILast    cflast     ) m =
      case cflast of
            (CFCont _bid    vs) -> addUsed m [(v, UsedSecondClass) | v <- vs]
            (CFCall bid _ v vs) ->
                 case Map.lookup (tidIdent v) cf of
                   Nothing -> addUsed m $ (v, UnknownCall bid):
                                         [(v, UsedFirstClass) | v <- vs]
                   Just fn -> addUsed m $ (v, (KnownCall bid (fnEntryId fn))):
                                         [(v, UsedFirstClass) | v <- vs]
            (CFCase v _pats)    -> addUsed m [(v, UsedSecondClass)]

    fnEntryId fn = let bbg = fnBody fn in
                   let st = case fnIsRec fn of
                             Just True  -> YesRec
                             Just False -> NotRec
                             Nothing    -> NotRec
                   in (st, blockId $ bbgEntry bbg)

    censusLetable letable m =
      case letable of
        ILText         {}        -> m
        ILBool         {}        -> m
        ILInt          {}        -> m
        ILFloat        {}        -> m
        ILKillProcess  {}        -> m
        ILOccurrence   {}        -> m
        ILBitcast      _ v       -> addUsed m [(v, UsedFirstClass)] -- conservatively :(
        ILTuple        vs _asrc  -> addUsed m [(v, UsedFirstClass) | v <- vs]
        ILCallPrim     _ _ vs    -> addUsed m [(v, UsedFirstClass) | v <- vs]
        ILCall         _ v _vs   -> error $ "census encountered non-tail ILCall of " ++ show v
        ILAppCtor      _ _ vs    -> addUsed m [(v, UsedFirstClass) | v <- vs]
        ILAlloc        v _rgn    -> addUsed m [(v, UsedFirstClass)]
        ILDeref        t v       -> addUsed m [(v, UsedFirstClass)]
        ILStore        v1 v2     -> addUsed m [(v1, UsedFirstClass), (v2, UsedFirstClass)]
        ILAllocArray    _ v      -> addUsed m [(v, UsedFirstClass)]
        ILArrayRead  _t (ArrayIndex v1 v2 _rng _s) -> addUsed m [(v1, UsedFirstClass), (v2, UsedFirstClass)]
        ILArrayPoke  (ArrayIndex v1 v2 _rng _s) v3 -> addUsed m [(v1, UsedFirstClass), (v2, UsedFirstClass),
                                                                 (v3, UsedFirstClass)]

runCensusRewrites' :: IORef Uniq -> BasicBlockGraph -> IO BasicBlockGraph
runCensusRewrites' uref bbg = do
     runWithUniqAndFuel uref infiniteFuel (go (getCensus bbg) bbg)
  where go :: Census -> BasicBlockGraph -> M BasicBlockGraph
        go ci bbg = do
         let (bid,_) = bbgEntry bbg
         bb' <- rebuildGraphM bid (bbgBody bbg) (transform ci)
         return $ bbg { bbgBody = bb' }

        getKnownCall ci id =
          case fmap Set.toList (Map.lookup id ci) of
            Just [kn] -> Just kn
            _         -> Nothing

        transform ci = rw
         where
          rw :: Insn e x -> M (Graph Insn e x)
          rw n = case n of
             ILabel   {} -> do return $ mkFirst  n
             ILetFuns [id] [fn]
               | Just (KnownCall bid (NotRec, _)) <- getKnownCall ci id
                         -> do let ag = aGraphOfGraph emptyGraph
                               fng <- aGraphOfFn fn bid
                               graphOfAGraph (addBlocks ag fng)
             ILetFuns _ids _fns    -> return $ mkMiddle n
             ILetVal  _id _letable -> return $ mkMiddle n
             ILast (CFCall _ _t v vs)
               | Just (KnownCall _bid (NotRec, fn_ent)) <- getKnownCall ci (tidIdent v)
                     -> return $ mkLast $ ILast (CFCont (contified fn_ent) vs)
             ILast _ -> return $ mkLast n

        contified ("postalloca", l) = ("contified_postalloca", l)
        contified entry             = entry

        -- Rewrite the function's body so that returns become jumps to the
        -- continuation that all callers had provided.
        aGraphOfFn fn retbid = do
          let ret bid = if bid == bbgRetK (fnBody fn) then retbid else bid
          let rw :: Insn e x -> Insn e x
              rw (ILabel (entry,vs)) = ILabel (contified entry, vs)
              rw (ILast (CFCont bid           vs)) =
                  ILast (CFCont (ret bid)     vs)
              rw (ILast (CFCall bid       t v vs)) =
                  ILast (CFCall (ret bid) t v vs)
              rw (ILast (CFCase v arms)) =
                 (ILast (CFCase v (map (\(p,k) -> (p,ret k)) arms)))
              rw insn = insn
          let g = mapGraph rw $ bbgBody $ fnBody fn
          return $ aGraphOfGraph g
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| Free identifiers ||||||||||||||||||||||||{{{
type IdentSetPair = (Set.Set Ident, Set.Set Ident)

instance TExpr BasicBlockGraph MonoType where
  freeTypedIds bbg =
       let (bvs,fvs) = foldGraphNodes go (bbgBody bbg) (Set.empty, Set.empty) in
       filter (\v -> Set.notMember (tidIdent v) bvs) (Set.toList fvs)
       -- We rely on the fact that these graphs are alpha-converted, and thus
       -- have a unique-binding property. This means we can  get away with just
       -- sticking all the binders in one set, and all the occurrences in
       -- another, and get the right answer back out.
     where insert :: Ord a => Set a -> [a] -> Set a
           insert s ids = Set.union s (Set.fromList ids)
           insertV s vs = Set.union s (Set.fromList $ map tidIdent vs)

           go :: Insn e x -> (Set Ident, Set MoVar) -> (Set Ident, Set MoVar)
           go (ILabel (_,bs))    (bvs,fvs) = (insertV bvs bs, fvs)
           go (ILetVal id lt)    (bvs,fvs) = (Set.insert id bvs, insert fvs $ freeTypedIds lt)
           go (ILetFuns ids fns) (bvs,fvs) = (insert bvs ids, insert fvs (concatMap freeTypedIds fns))
           go (ILast cflast)     (bvs,fvs) = case cflast of
                    CFCont _ vs          -> (bvs, insert fvs vs)
                    CFCall _ _ v vs      -> (bvs, insert fvs (v:vs))
                    CFCase v patbinds    -> (insertV bvs pvs, Set.insert v fvs)
                         where pvs = concatMap (\((_,vs),_) -> vs) patbinds

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||| Liveness ||||||||||||||||||||||||||||||||{{{
type Live = Set.Set Ident

liveLattice :: DataflowLattice Live
liveLattice = DataflowLattice
  { fact_name = "Live variables"
  , fact_bot  = Set.empty
  , fact_join = add
  }
    where add _ (OldFact old) (NewFact new) = (ch, j)
            where
              j = new `Set.union` old
              ch = changeIf (Set.size j > Set.size old)

liveness :: BwdTransfer Insn Live
liveness = mkBTransfer go
  where
    go :: Insn e x -> Fact x Live -> Live
    go (ILabel   (bid, vs)  ) s = s
    go (ILetVal  id letable ) s = Set.union  (without s [id]) (Set.fromList $ freeIdents letable)
    go (ILetFuns ids fns    ) s = Set.unions ((without s ids):(map (Set.fromList . freeIdents) fns))
    go node@(ILast    cflast) fdb =
          let s = Set.unions (map (fact fdb) (successors node)) in
          case cflast of
            (CFCont _bid    vs) -> insert s vs
            (CFCall bid _ v vs) -> insert s (v:vs)
            (CFCase v _pats)    -> insert s [v]

    without s ids = Set.difference s (Set.fromList ids)
    insert s vs = Set.union s (Set.fromList (map tidIdent vs))

    fact :: FactBase (Set.Set Ident) -> Label -> Live
    fact f l = fromMaybe (fact_bot liveLattice) $ lookupFact l f

deadBindElim :: forall m . FuelMonad m => BwdRewrite m Insn Live
deadBindElim = mkBRewrite d
  where
    d :: Insn e x -> Fact x Live -> m (Maybe (Graph Insn e x))
    d (ILetVal id letable) live |
      not (id `Set.member` live) && isPure letable = return $ Just emptyGraph
    d (ILetFuns [id] [_])  live |
      not (id `Set.member` live)                   = return $ Just emptyGraph
    -- If LetFuns forms a SCC, then we can't drop any entry unless we can drop
    -- every entry. However, if it's not a SCC, then we can drop any entry which
    -- is dead and does not appear in any of the other functions.
    d (ILetFuns ids fns)   live = do
      let inOthers = map (\(id, ofns) ->
                         Set.member id (Set.fromList (concatMap freeIdents ofns)))
                         (zip ids (others fns))
      let kept = filter (\(id,_fn,inother) -> Set.member id live || inother) (zip3 ids fns inOthers)
      return $ if null kept then Just emptyGraph
                            else let (ids' , fns' , _) = unzip3 kept in
                                 Just (mkMiddle $ ILetFuns  ids' fns' )
      --return $ trace (concatMap (\id -> show id ++ " live?" ++ show (id `Set.member` live) ++ "\n") ids) Nothing
    d _ _ = return Nothing

    -- others [1,2,3,4] = [[2,3,4],[1,3,4],[1,2,4],[1,2,3]]
    others xs = map (\n -> take n xs ++ tail (drop n xs)) [0..length xs - 1]

runLiveness :: IORef Uniq -> BasicBlockGraph -> IO BasicBlockGraph
runLiveness uref bbg = runWithUniqAndFuel uref infiniteFuel (go bbg)
  where go bbg = do
            (bb', _, _) <- analyzeAndRewriteBwd bwd' (JustC [bbgEntry bbg])
                                                           (bbgBody  bbg)
                                                           mapEmpty
            return $ bbg { bbgBody = bb' }

        bwd' = debugBwdTransfers trace showing (\_ _ -> True) bwd
        bwd = BwdPass { bp_lattice  = liveLattice
                      , bp_transfer = liveness
                      , bp_rewrite  = deadBindElim
                      }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

instance AExpr (Letable ty)    where freeIdents x = map tidIdent $ ((freeTypedIds x) :: [TypedId ty])
instance AExpr BasicBlockGraph where freeIdents x = map tidIdent $ ((freeTypedIds x) :: [TypedId MonoType])

showing :: Insn e x -> String
--showing insn = "SHOWING: " ++ show (pretty insn) ++ "\nEND SHOWING\n"
showing insn = show (pretty insn)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
