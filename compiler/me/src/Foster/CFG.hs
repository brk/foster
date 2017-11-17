{-# LANGUAGE GADTs, TypeSynonymInstances, RankNTypes, ScopedTypeVariables,
             PatternGuards, TypeFamilies, NoMonoLocalBinds #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CFG
( Insn(..)
, BlockId, BlockEntry'
, BasicBlockGraph(..)
, BasicBlock
, CFLast(..)
, CFFn
, blockTargetsOf
, mapGraphNodesM_
, rebuildGraphM
, rebuildGraphAccM
, graphOfClosedBlocks, graphBlocks
, FosterNode(..)
, catClosedGraphs
, prettyCFFn
, runWithUniqAndFuel, M
, PreCloConv(..)
) where

import Prelude hiding ((<$>))

import Foster.Base
import Foster.Kind
import Foster.MonoType
import Foster.Letable(Letable(..))

import Control.Monad(ap)
import qualified Control.Applicative as AP(Applicative(..))

import Compiler.Hoopl
import qualified Compiler.Hoopl as H((<*>))
import Text.PrettyPrint.ANSI.Leijen

import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad.State
import Data.IORef

-- ||||||||||||||||||||||| CFG Data Types |||||||||||||||||||||||{{{
data CFLast = CFCont        BlockId [MoVar] -- either ret or br
            | CFCase        MoVar [CaseArm PatternRepr BlockId MonoType]
            deriving (Show)

data Insn e x where
              ILabel   :: BlockEntry                  -> Insn C O
              ILetVal  :: Ident   -> Letable MonoType -> Insn O O
              ILetFuns :: [Ident] -> [CFFn]           -> Insn O O
              ILast    :: CFLast                      -> Insn O C
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

prettyTypedVar (TypedId t i) = prettyIdent i <+> text "::" <+> pretty t

showTyped :: Doc -> MonoType -> Doc
showTyped d t = parens (d <+> text "::" <+> pretty t)

fnFreeIds :: (Fn RecStatus BasicBlockGraph MonoType) -> [MoVar]
fnFreeIds fn = freeTypedIds fn

prettyCFFn :: Fn RecStatus BasicBlockGraph MonoType -> Doc
prettyCFFn fn = group (lbrace <+>
                         (align (vcat (map (\v -> showTyped (pretty v) (tidType v) <+> text "=>")
                                (fnVars fn))))
                    <$> indent 4 (pretty (fnBody fn))
                    <$> rbrace)
                     <+> text "free-ids" <+> text (show (map prettyTypedVar (fnFreeIds fn)))
                     <$> text "::" <+> prettyTypedVar (fnVar fn)

instance Pretty Label where pretty l = text (show l)

instance Pretty BasicBlock where
  pretty bb = foldBlockNodesF prettyInsn bb empty

instance Pretty (Graph Insn C C) where
  pretty bg = foldGraphNodes  prettyInsn bg empty

instance Pretty (Graph Insn O O) where
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
      ILTuple _knd vs _asrc -> (if _knd == KindAnySizeType then text "#" else text "") <>
                                 parens (hsep $ punctuate comma (map pretty vs))
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
      ILAllocArray _ _v _ _ -> text $ "ILAllocArray..."
      ILArrayRead  _t (ArrayIndex v1 v2 _rng _s)  -> text "ILArrayRead" <+> prettyId v1 <> text "[" <> prettyId v2 <> text "]"
      ILArrayPoke  (ArrayIndex _v1 _v2 _rng _s) _v3 -> text $ "ILArrayPoke..."
      ILArrayLit _ _v _vals -> text $ "ILArrayLit..."
      ILBitcast   t v       -> text "bitcast " <+> prettyTypedVar v <+> text "to" <+> pretty t
      ILAllocate _info      -> text "allocate ..." -- <+> pretty (allocType info)
      ILObjectCopy from to  -> text "copy object" <+> pretty from <+> text "to" <+> pretty to

instance Pretty BasicBlockGraph where
 pretty bbg =
         (indent 4 (text "ret k =" <+> pretty (bbgRetK bbg)
                <$> text "entry =" <+> pretty (fst $ bbgEntry bbg)
                <$> text "------------------------------"))
          <> pretty (bbgBody bbg)

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
                    CFCase v arms        -> (insertV bvs pvs, Set.insert v fvs)
                         where pvs = concatMap caseArmBindings arms

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

 -- Dunno why this function isn't in Hoopl...
catClosedGraphs :: NonLocal i => [Graph i C C] -> Graph i C C
catClosedGraphs = foldr (|*><*|) emptyClosedGraph

mapGraphNodesM_ :: (Monad m, FosterNode i, NonLocal i)
                => (forall e x. i e x -> m ())
                           -> BlockId -> Graph i C C -> m ()
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
--
-- Passing Nothing for entrybid means visit graph nodes in arbitrary order,
-- preserving unreachable blocks;
-- Passing Just entrybid means visit graph nodes in DFS order,
-- dropping unreachable blocks.
rebuildGraphM :: (Monad m, NonLocal o, FosterNode i, NonLocal i)
                         => Maybe BlockId -> Graph i C C
                         -> (forall e x. i e x -> m (Graph o e x))
                         -> m (Graph o C C)
rebuildGraphM mb_entrybid body transform = do
  let transform' () insn = do g <- transform insn; return (g, ())
  (g, ()) <- rebuildGraphAccM mb_entrybid body () transform'
  return g

-- More complete interface supporting threaded state.
rebuildGraphAccM :: (Monad m, NonLocal o, FosterNode i, NonLocal i)
                         => Maybe BlockId -> Graph i C C -> acc
                         -> (forall e x. acc -> i e x -> m (Graph o e x, acc))
                         -> m (Graph o C C, acc)
rebuildGraphAccM mb_entrybid body init transform = do
   let rebuildBlockGraph blk_cc acc0 = do {
      ; let (f, ms, l) = unblock ( blockSplit blk_cc )
      ; (fg, acc1) <- transform acc0 f
      ; (gs, accn) <- mapFoldM' ms acc1 (\insn acc -> transform acc insn)
      ; (lg, accm) <- transform accn l
      ; return $ (fg H.<*> catGraphs gs H.<*> lg, accm)
   }
   let blocks = case mb_entrybid of
                  Just entrybid -> postorder_dfs (mkLast (branchTo entrybid) |*><*| body)
                  Nothing       -> graphBlocks body
   (mb, acc) <- mapFoldM' blocks init rebuildBlockGraph
   return $ (catClosedGraphs mb, acc)
  where
   unblock (f, ms_blk, l) = (f, blockToList ms_blk, l)

-- Akin to preorder_dfs but preserves unreachable blocks.
graphBlocks :: NonLocal i => Graph i C C -> [Block i C C]
graphBlocks g =
  case g of
    --GNil -> []
    --GUnit b -> [b]
    GMany NothingO body NothingO -> mapElems body


-- ||||||||||||||||||||||||||| UniqMonadIO ||||||||||||||||||||||{{{
-- Basically a copy of UniqueMonadT, specialized to IO, with a
-- more suitable "run" function, and using Uniq instead of Unique.
newtype UniqMonadIO a = UMT { unUMT :: [Uniq] -> IO (a, [Uniq]) }

instance Monad UniqMonadIO where
  return a = UMT $ \us -> return (a, us)
  m >>= k  = UMT $ \us -> do { (a, us') <- unUMT m us; unUMT (k a) us' }

instance Functor        UniqMonadIO where fmap  = liftM
instance AP.Applicative UniqMonadIO where pure  = return
                                          (<*>) = ap

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

data PreCloConv = PreCloConv ([CFFn], [ToplevelBinding MonoType]) -- [(Ident, MonoType, [Literal])]