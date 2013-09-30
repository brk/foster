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
, blockId
, blockTargetsOf
, mapGraphNodesM_
, rebuildGraphM
, rebuildGraphAccM
, graphOfClosedBlocks
, FosterNode(..)
, catClosedGraphs
, runWithUniqAndFuel, M
) where

import Foster.Base
import Foster.MonoType
import Foster.KNExpr(KNExpr'(..), typeKN, KNMono, FnMono)
import Foster.Letable(Letable(..))

import Compiler.Hoopl
import Text.PrettyPrint.ANSI.Leijen

import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Map(Map)
import Data.Set(Set)
import Control.Monad.State
import Data.IORef
import Prelude hiding (id, last)

data CFBody = CFB_LetFuns [Ident] [CFFn] CFBody
            | CFB_Call    TailQ MonoType MoVar [MoVar]

-- Next stage: optimizeCFGs in CFGOptimizations.hs

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

computeCFGIO :: IORef Uniq -> FnMono -> IO CFFn
computeCFGIO uref fn = do
  cfgState <- internalComputeCFG uref fn
  extractFunction cfgState fn

-- A mirror image for internal use (when converting nested functions).
-- As above, we thread through the updated unique value from the subcomputation!
cfgComputeCFG :: FnMono -> CFG CFFn
cfgComputeCFG fn = do
  uref      <- gets cfgUniq
  cfgState  <- liftIO $ internalComputeCFG uref fn
  liftIO $ extractFunction cfgState fn

-- A helper for the CFG functions above, to run computeBlocks.
internalComputeCFG :: IORef Int -> FnMono -> IO CFGState
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
    ret :: forall ty expr. Fn RecStatus expr ty -> BlockId -> MoVar -> CFG ()
    ret f k v = if isMain f then cfgEndWith (CFCont k [])
                            else cfgEndWith (CFCont k [v])
            where isMain :: forall ty expr. Fn RecStatus expr ty -> Bool
                  isMain f = (identPrefix $ tidIdent $ fnVar f) == T.pack "main"

-- The other helper, to collect the scattered results and build the actual CFG.
extractFunction :: CFGState -> Fn RecStatus KNMono MonoType -> IO CFFn
extractFunction st fn = do
  let blocks = Prelude.reverse (cfgAllBlocks st)
  let elab    = entryLab blocks
  let (Just rk) = cfgRetCont st
  let bbg = BasicBlockGraph elab rk (catClosedGraphs (map blockGraph blocks))
  return fn { fnBody = bbg }
  where
        entryLab :: forall x. [Block Insn C x] -> BlockEntry
        entryLab [] = error $ "can't get entry block label from empty list!"
        entryLab (bb:_) = let _r :: Insn C O -- needed for GHC 6.12 compat
                              _r@(ILabel elab) = firstNode bb in elab

blockId :: BlockEntry' t -> BlockId
blockId = fst

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

caseIf a b = [CaseArm (pat True)  a Nothing [] rng,
              CaseArm (pat False) b Nothing [] rng]
         where rng = MissingSourceRange "cfg.if.rng"
               pat :: Bool -> PatternRepr MonoType
               pat bval = PR_Atom $ P_Bool rng boolMonoType bval

-- ||||||||||||||||||||||||| KNMono -> CFG ||||||||||||||||||||||{{{
-- computeBlocks takes an expression and a contination,
-- which determines what to do with the let-bound result of the expression.
computeBlocks :: KNMono -> Maybe Ident -> (MoVar -> CFG ()) -> CFG ()
computeBlocks expr idmaybe k = do
    case expr of
        KNIf t v a b -> do -- Compile [if v then ...] as [case v of ...].
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

        -- Perform on-demand let-flattening, which enables a CPS tranform with a mostly-first-order flavor.
        KNLetVal id (KNLetVal  x   e   c) b -> computeBlocks (KNLetVal x e      (KNLetVal id c b)) idmaybe k
        KNLetVal id (KNLetFuns ids fns a) b -> computeBlocks (KNLetFuns ids fns (KNLetVal id a b)) idmaybe k

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

        KNLetRec [id] [bexp] e -> do
            -- With KNLetFuns, we maintain a special binding form for SCCs of
            -- mutually-recursive functions, because we'll sometimes optimize
            -- them to continuations and/or inline them away entirely.
            -- We also 'evaluate' them specially, avoiding extra allocations.
            --
            -- For more complex recursive bindings, we'll just do the (second)
            -- simplest thing that works, at least for now.
            -- TODO: extend this to use the 'immediate in-place update' scheme.

            -- Let-bind un-initialized blocks to the ids
            --
            -- It's tempting to say "allocate a block for type (typeKN bexp)",
            -- but that's wrong for two (related) reasons. First, at this stage
            -- in the game, the visible representation is the pointer, not the
            -- underlying struct. Second, the same datatype can be constructed
            -- from different-sized blocks/ctors, which means there's no way
            -- to derive a representation struct from a type alone.

            -- We also need to separate the internal and external
            -- representations of the block.
            stor <- cfgFreshId ".rec.storage"
            let allocInfo = allocInfoForKNExpr bexp
            let obj = TypedId (PtrType (allocType allocInfo)) stor

            cfgAddMiddle (ILetVal stor (ILAllocate allocInfo))
            cfgAddMiddle (ILetVal id   (ILBitcast (typeKN bexp) obj))

            -- Emit code to evaluate the expressions (bound to temporaries).
            tmpgen <- cfgFreshId ".rec.tmp.gen"
            computeBlocks bexp (Just tmpgen) $ \_var -> return ()

            -- Overwrite the id-bound blocks with the temporary values.
            tmpid <- cfgFreshId ".rec.tmp"
            cfgAddMiddle (ILetVal tmpid (ILBitcast (tidType obj)
                                          (TypedId (typeKN bexp) tmpgen)))

            let tmp = TypedId (tidType obj) tmpid
            tupstorid <- cfgFreshId ".rec.tupstore"
            cfgAddMiddle (ILetVal tupstorid (ILObjectCopy tmp obj))

            -- Emit code to evaluate the body of the letrec.
            computeBlocks e idmaybe k
            -- Paper references:
            --  * "Fixing Letrec"
            --  * "Compilation of Extended Recursion in Call-by-value Functional Languages"

        KNLetRec {} -> error $ "CFG.hs: no support yet for multi-extended-letrec"

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
        --      case scrutinee of p1       -> e1
        --                     of p2 if g2 -> e2 ...
        --
        -- gets translated into (the moral equivalent of)
        --
        --      case scrutinee of p1 -> goto case_arm1
        --                     of p2 -> goto case_arm2 ...
        --  case_arm1: ev = [[e1]]; goto case_cont [ev]
        --  case_arm2: _t = [[g2]]; goto (_t ? a2gt : a2gf) []
        --       a2gt: ev = [[e2]]; goto case_cont [ev]
        --       a2gf: ... continue pattern matching ...
        --  case_cont [case_value]:
        --      ...
        --
        -- The one point this glosses over is how the variables bound by
        -- p1 become visible in the translation of e1. Currently this is
        -- done by some magic in LLCodegen, but it should be represented
        -- more explicitly.
        KNCase t v bs -> do
            -- Compute the new block ids, along with their patterns.
            --bids <- mapM (\_ -> cfgFresh "case_arm") bs

            let computeCaseIds arm = do
                  bid <- cfgFresh "case_arm"
                  tru <- liftMaybe (\_ -> cfgFresh "case_arm.tru") (caseArmGuard arm)
                  fls <- liftMaybe (\_ -> cfgFresh "case_arm.fls") (caseArmGuard arm)
                  return (arm, bid, tru, fls)
            arms_bids <- mapM computeCaseIds bs
            case_cont <- cfgFresh "case_cont"

            let bbs = [CaseArm p bid tru b rng | (CaseArm p _ _ b rng, bid, tru, _fls) <- arms_bids]
            --let bbs = [CaseArm p bid Nothing b rng | (CaseArm p _ _ b rng, bid) <- zip bs bids]

            --let badArms = [arm | arm@(CaseArm _ _ (Just _) _ _) <- bs]
            cfgEndWith (CFCase v bbs)

            let computeCaseBlocks (arm, block_id, mb_tru, mb_fls) = do
                    let e = caseArmBody arm
                    case caseArmGuard arm of
                      Nothing -> do
                        -- Fill in each arm's block with [[e]] (and a store at the end).
                        cfgNewBlock block_id []
                        computeBlocks e Nothing $ \var ->
                            cfgEndWith (CFCont case_cont [var])
                      Just  g -> do
                        let Just tru = mb_tru
                        let Just fls = mb_fls
                        cfgNewBlock block_id []
                        computeBlocks g Nothing $ \guard ->
                            cfgEndWith (CFCase guard (caseIf tru fls))

                        -- We'll fill in the 'fls' block implementation later...
                        cfgNewBlock fls []
                        cfgEndWith (CFCont tru []) -- What do we do here?!?
                        -- We want to emit code to resume pattern-matching against
                        -- the remaining contenders/rows of the match matrix,
                        -- but the match matrix will not be determined until later.

                        cfgNewBlock tru []
                        computeBlocks e Nothing $ \var ->
                            cfgEndWith (CFCont case_cont [var])
            mapM_ computeCaseBlocks arms_bids

            -- The overall value of the case is the value stored in the slot.
            phi <- cfgFreshVarI idmaybe t ".case.phi"
            cfgNewBlock case_cont [phi]
            k phi

        KNCall srctail ty b vs -> do
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
         KNLiteral    t lit  -> ILLiteral    t lit
         KNVar        _v     -> error $ "can't make Letable from KNVar!"
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

    allocInfoForKNExpr bexp =
      case bexp of
        KNLetVal     _ _  b -> allocInfoForKNExpr b
        KNLetFuns    _ _  b -> allocInfoForKNExpr b
        KNAppCtor    _ (cid,rep) vs ->
          let structty = StructType (map tidType vs) in
          let tynm = ctorTypeName cid ++ "." ++ ctorCtorName cid in
          AllocInfo structty   MemRegionGlobalHeap   tynm
                    (Just rep) Nothing "KNLetRecTmp" DoZeroInit
        KNCall _ _ base _ -> error $ "allocInfoForKNExpr can't handle " ++ show (textOf bexp 0) ++ " ;; " ++ show base
        _ -> error $ "allocInfoForKNExpr can't handle " ++ show (textOf bexp 0)

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
            Nothing         -> error $ "Tried to add middle without a block: " ++ show (pretty mid)
                                         ++ "\n" ++ show (pretty (cfgAllBlocks old))
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
            | CFCase        MoVar [CaseArm PatternRepr BlockId MonoType]
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
        CFCase _ arms        -> concatMap caseArmExprs arms

type BasicBlock = Block Insn C C
data BasicBlockGraph = BasicBlockGraph { bbgEntry :: BlockEntry
                                       , bbgRetK  :: BlockId
                                       , bbgBody  :: Graph Insn C C
                                       }
type CFFn = Fn RecStatus BasicBlockGraph MonoType
type BlockEntry = BlockEntry' MonoType
type BlockEntry' t = (BlockId, [TypedId t])

-- We pair a name for later codegen with a label for Hoopl's NonLocal class.
type BlockId = (String, Label)


-- ||||||||||||||||||||| CFG Pretty Printing ||||||||||||||||||||{{{

comment d = text "/*" <+> d <+> text "*/"

prettyId (TypedId _ i) = text (show i)
prettyTypedVar (TypedId t i) = text (show i) <+> text "::" <+> pretty t

showTyped :: Doc -> MonoType -> Doc
showTyped d t = parens (d <+> text "::" <+> pretty t)

fnFreeIds :: (Fn RecStatus BasicBlockGraph MonoType) -> [MoVar]
fnFreeIds fn = freeTypedIds fn

instance Pretty (Fn RecStatus BasicBlockGraph MonoType) where
  pretty fn = group (lbrace <+>
                         (align (vcat (map (\v -> showTyped (pretty v) (tidType v) <+> text "=>")
                                (fnVars fn))))
                    <$> indent 4 (pretty (fnBody fn))
                    <$> rbrace)
                     <+> text "free-ids" <+> text (show (map prettyTypedVar (fnFreeIds fn)))

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
  pretty (CFCase v arms)     = align $
                               text "case" <+> pretty v <$> indent 2
                                  (vcat [ text "of" <+> fill 20 (pretty pat)
                                                    <+> (case guard of
                                                           Nothing -> empty
                                                           Just g  -> text "if" <+> prettyBlockId g)
                                                    <+> text "->" <+> prettyBlockId bid
                                        | (CaseArm pat bid guard _ _) <- arms
                                        ])

instance Pretty t => Pretty (Letable t) where
  pretty l =
    case l of
      ILLiteral   _ lit     -> pretty lit
      ILTuple     vs _asrc  -> parens (hsep $ punctuate comma (map pretty vs))
      ILKillProcess t m     -> text ("prim KillProcess " ++ show m ++ " :: ") <> pretty t
      ILOccurrence  _ v occ -> prettyOccurrence v occ
      ILCallPrim  _ p vs    -> (text "prim" <+> pretty p <+> hsep (map prettyId vs))
      ILCall      _ v vs    -> pretty v <+> hsep (map pretty vs)
      ILAppCtor   _ (c,r) vs ->(parens (text (ctorCtorName c)
                                        <>  text "~" <> text (show r)
                                        <+> hsep (map prettyId vs)))
      ILAlloc     v rgn     -> text "(ref" <+> pretty v <+> comment (pretty rgn) <> text ")"
      ILDeref     _ v       -> pretty v <> text "^"
      ILStore     v1 v2     -> text "store" <+> pretty v1 <+> text "to" <+> pretty v2
      ILAllocArray _ _v     -> text $ "ILAllocArray..."
      ILArrayRead  _t (ArrayIndex v1 v2 _rng _s)  -> text "ILArrayRead" <+> prettyId v1 <> text "[" <> prettyId v2 <> text "]"
      ILArrayPoke  (ArrayIndex _v1 _v2 _rng _s) _v3 -> text $ "ILArrayPoke..."
      ILBitcast   _ v       -> text "bitcast " <+> pretty v <+> text "to" <+> text "..."
      ILAllocate _info      -> text "allocate ..." -- <+> pretty (allocType info)
      ILObjectCopy from to  -> text "copy object" <+> pretty from <+> text "to" <+> pretty to

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

instance LabelsPtr (BlockId, ts) where targetLabels ((_, label), _) = [label]

-- |||||||||||||||||||| Free identifiers ||||||||||||||||||||||||{{{
instance TExpr BasicBlockGraph MonoType where
  freeTypedIds bbg =
       -- Compute the bound and free variables of the set of instructions
       -- in the graph, and discard any free variables which are also bound.
       --
       let (bvs,fvs) = foldGraphNodes go (bbgBody bbg) (Set.empty, Set.empty) in
       filter (\v -> Set.notMember (tidIdent v) bvs) (Set.toList fvs)
       --
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
                    CFCase v arms        -> (insertV bvs pvs, Set.insert v fvs)
                         where pvs = concatMap caseArmBindings arms

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

 -- Dunno why this function isn't in Hoopl...
catClosedGraphs :: NonLocal i => [Graph i C C] -> Graph i C C
catClosedGraphs = foldr (|*><*|) emptyClosedGraph

mapGraphNodesM_ :: Monad m => (forall e x. Insn e x -> m ())
                           -> BlockId -> Graph Insn C C -> m ()
mapGraphNodesM_ a entrybid g = do
   let mapBlockM_ blk_cc = do {
      ; let (f, ms_blk, l) = blockSplit blk_cc
      ; a f
      ; mapM_ a (blockToList ms_blk)
      ; a l
   }
   mapM_ mapBlockM_ $ postorder_dfs (mkLast (branchTo entrybid) |*><*| g)

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

type M {-a-} = InfiniteFuelMonad UniqMonadIO {-a-}
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

