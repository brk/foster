{-# LANGUAGE StandaloneDeriving, Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt fCFe or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.PatternMatch(DecisionTree(..), DataTypeSigs, compilePatterns)
where

import Prelude hiding ((<$>))

import qualified Data.List as List
import Data.Set(Set)
import qualified Data.Set  as Set(size, toList, map,
                                  singleton, unions, empty)
import Data.Map(Map)
import qualified Data.Map  as Map(lookup, size)

import qualified Data.Text as T(concat, pack, unpack)

import Foster.Base
import Foster.SourceRange(SourceRange)

import Prettyprinter hiding (column)

{-
Straightforward implementation of pattern match compilation
as laid out by Luc Maranget in his ML'08 paper
        Compiling Pattern Matching to Good Decision Trees

For now, we use only the naive leftmost-outermost-first
column selection heuristic. Subtree sharing is implemented
in CloConv.hs @ compileDecisionTree.
-}

data DecisionTree a t
    =  DT_Fail [SourceRange]
    |  DT_Leaf  a                -- The expression/block id to evaluate/jump to.
         [(TypedId t, Occurrence t)]  -- Subterms of scrutinee to bind in leaf.
    |  DT_Switch
                     (Occurrence t)  -- Subterm of scrutinee to switch on.
                [((CtorId, CtorRepr), DecisionTree a t)] -- Map of ctors to decision trees.
                  (Maybe (DecisionTree a t)) -- Default decision tree, if any.

-- Avoiding all these type parameters seems like a
-- pretty good use case for parameterized modules!

{-
   A ClauseRow represents the patterns being matched for one arm of a case expression.

   The rowAction is passed through to DT_Leaf when a row trivially matches.
   The rowOrigPat is used for computing the bindings scoped to a DT_Leaf.
        Regardless of what merged patterns end up in rowPatterns, the rowOriginalPat
        is used to generate (variable, occurence-of-scrutinee) pairs.
   The rowPatterns are used for representing the subterms of of the scrutinee being matched.

-}

data ClauseMatrix a t = ClauseMatrix [ClauseRow a t]
data ClauseRow a t  = ClauseRow { rowOrigPat  :: (SPattern t)
                                , rowPatterns :: [SPattern t]
                                , rowAction   :: a
                                ,_rowSourceRange :: SourceRange }

data SPattern t = SP_Wildcard
                | SP_Variable (TypedId t)
                | SP_Ctor     (LLCtorInfo t) [SPattern t]
                | SP_Or                      [SPattern t]
               deriving (Show)

instance Pretty (SPattern t) where
  pretty (SP_Wildcard) = text "_"
  pretty (SP_Variable tid) = pretty (tidIdent tid)
  pretty (SP_Or pats) = parens (hsep $ punctuate (text " or ") (map pretty pats))
  pretty (SP_Ctor cinfo pats) = parens (pretty (ctorLLInfoId cinfo)
                                      <> pretty (ctorLLInfoRepr cinfo)
                                     <+> hsep (map pretty pats))


type DataTypeSigs = Map DataTypeName DataTypeSig

compilePatterns :: (IntSizedBits t, PrettyT t)
                => [CaseArm PatternRepr a t]
                -> DataTypeSigs
                -> DecisionTree a t
compilePatterns bs allSigs =

 cc [[]] matrix (ranges matrix) allSigs where

  matrix = ClauseMatrix $ map compilePatternRow bs

  compilePatternRow (CaseArm p a _ _ r) = ClauseRow (compilePattern p)
                                                    [compilePattern p] a r

  compilePattern :: IntSizedBits t => PatternRepr t -> SPattern t
  compilePattern p = case p of
    (PR_Atom (P_Wildcard _ _))   -> SP_Wildcard
    (PR_Atom (P_Variable _ v))   -> SP_Variable v
    (PR_Atom (P_Bool     _ _ b)) -> SP_Ctor (boolCtor b)     []
    (PR_Atom (P_Int     _ ty i)) -> SP_Ctor (intCtor ty i)   []
    (PR_Ctor  _ _ pats nfo) -> SP_Ctor            nfo   (map compilePattern pats)
    (PR_Tuple _ _ pats)     -> SP_Ctor (tupleCtor pats) (map compilePattern pats)
    (PR_Or    _ _ pats)     -> SP_Or                    (map compilePattern pats)
    where
          ctorInfo tynm dcnm dctys repr isLoneCtor =
             LLCtorInfo (CtorId tynm dcnm (Prelude.length $ dctys)) repr dctys isLoneCtor

          boolCtor False = ctorInfo "Bool"  "False" []                (CR_Value 0)   False
          boolCtor True  = ctorInfo "Bool"  "True"  []                (CR_Value 1)   False
          tupleCtor pats = ctorInfo "()"    "()"    (map typeOf pats) (CR_Default 0) True
          intCtor ty li  = ctorInfo ctnm (brackets ctnm) []           (CR_Value tag) False
                             where
                              brackets t = T.concat ["<", t, ">"]
                              isb  = intSizeBitsOf ty
                              bits = intSizeOf     isb
                              ctnm = T.pack $ show $ pretty isb
                              tag  = if litIntMinBits li <= bits
                                      then litIntValue li
                                      else error $ "PatternMatch.hs: cannot cram a literal (" ++ T.unpack (litIntText li) ++ ")"
                                               ++ " needing " ++ show (litIntMinBits li)
                                               ++ " bits into Int"++ show bits++"!"

-- "Compilation is defined by cases as follows."
cc :: PrettyT t => [Occurrence t] -> ClauseMatrix a t -> [SourceRange] -> DataTypeSigs -> DecisionTree a t

-- No row to match -> failure
cc _ (ClauseMatrix []) rngs _allSigs = DT_Fail rngs

-- If first row is all variables, match always succeeds.
cc _occs cm _rngs _allSigs | allGuaranteedMatch (rowPatterns $ firstRow cm) =
  {-trace ("\nmatched first row with pattern " ++ highlightFirstLine (rowSourceRange r) ++
         "\n i.e.:  " ++ show (rowPatterns $ firstRow cm) ++
         "\n, remaining rows are : " ++ show (map (highlightFirstLine . rowSourceRange) rest) ++ "\n") $
  -}
    DT_Leaf (rowAction r)
            (computeBindings (emptyOcc, rowOrigPat r))
      where r = firstRow cm
            --(ClauseMatrix (_:rest)) = cm
            emptyOcc = []
            computeBindings :: (Occurrence t, SPattern t) -> [(TypedId t, Occurrence t)]
            computeBindings ( occ, SP_Variable v   ) = [(v, occ)]
            computeBindings (_occ, SP_Wildcard     ) = []
            computeBindings ( occ, SP_Or pats      ) = concatMap (\p -> computeBindings (occ, p)) pats
            computeBindings ( occ, SP_Ctor ctorinfo pats) =
              let occs = expand occ ctorinfo in
              concatMap computeBindings (zip occs pats)

-- "In any other case, matrix P has at least one row and at least one
-- column (m > 0, n > 0). Furthermore, there exists at least one
-- column of which at least one pattern is not a wildcard. Select
-- one such column i."
cc occs cm rngs allSigs =
  let i = columnNumWithNonTrivialPattern cm in
  if  i == 0
   then
      let spPatterns = cm `column` i in
      let headCtorInfos = Set.unions (map headCtorInfo spPatterns) in
      let (o1:orest) = occs in
      let caselist = [ ((c, r),
                           cc (expand o1  llci ++ orest)
                              (specialize (c,r) cm)  (ranges cm) allSigs)
                     | llci@(LLCtorInfo c r _ _) <- Set.toList headCtorInfos] in
      -- The selected column contains some set of constructors C1 .. Ck.
      -- Pair each constructor with the clause matrix obtained from
      -- specializing the current match matrix w/r/t that constructor,
      -- and produce a Switch node examining the ctor of the i'th occurrence.
      let defaultCase = if isSignature (Set.map ctorLLInfoId headCtorInfos) allSigs
                         then Nothing
                         else let ad = cc orest (defaultMatrix cm) (ranges cm) allSigs in
                              Just ad in
      DT_Switch o1 caselist defaultCase
    else
      let o' = swapOcc i occs in
      let m' = swapCol i cm   in
      {- DT_Swap i $ -} cc o' m' rngs allSigs

allGuaranteedMatch pats = List.all trivialMatch pats
                             where trivialMatch (SP_Wildcard  ) = True
                                   trivialMatch (SP_Variable _) = True
                                   trivialMatch (SP_Ctor   _ _) = False
                                   trivialMatch (SP_Or       _) = False

firstRow (ClauseMatrix (r:_)) = r
firstRow (ClauseMatrix []) = error "precondition violated for firstRow helper!"

headCtorInfo :: SPattern ty -> Set (LLCtorInfo ty)
headCtorInfo (SP_Wildcard    ) = Set.empty
headCtorInfo (SP_Variable   _) = Set.empty
headCtorInfo (SP_Ctor cinfo _) = Set.singleton cinfo
headCtorInfo (SP_Or      pats) = Set.unions (map headCtorInfo pats)

columnNumWithNonTrivialPattern cm =
  loop cm 0 where
  loop cm n = if allGuaranteedMatch (cm `column` n)
                then loop cm (n + 1)
                else n

-- Given an occurrence and a constructor (which must match the type of the occurrence),
-- return a list of occurrences corresponding to the subterms of the constructor.
expand :: Occurrence t -> LLCtorInfo t -> [Occurrence t]
expand occ cinfo = [extendOccurrence occ n cinfo | n <- [0 .. ctorInfoArity cinfo - 1]]

extendOccurrence :: Occurrence t -> Int -> LLCtorInfo t -> Occurrence t
extendOccurrence occ n cinfo = occ ++ [(n, cinfo)]

ctorInfoArity (LLCtorInfo cid _ _ _) = ctorArity cid

instance Pretty (ClauseMatrix a t) where
  pretty (ClauseMatrix rows) =
      parens $ vsep [parens (pretty $ rowPatterns row) | row <- rows]

-- Specialization filters out rows which cannot match the given
-- constructor, and generates new patterns for subterms of the constructor.
-- The height of the matrix will not grow, but the width can grow or shrink.
--
-- As an example, the specialization w/r/t Nil of
--    []      a     -> 1
--    b      []     -> 2
--    (c::d) (e::f) -> 3
--
-- is
--    a  -> 1
--    [] -> 2
--
-- and w/r/t Cons is
--    b   _b2 []     -> 2
--    c   d   (e::f) -> 3
--
-- Note that ``specialize`` should always be used with ``expand''!
specialize :: (CtorId, CtorRepr) -> ClauseMatrix a t -> ClauseMatrix a t
specialize cinfo (ClauseMatrix rows) =
{-
  trace ("specialized\n" ++ show (pretty $ ClauseMatrix rows)
         ++ "\nw.r.t. "  ++ show (pretty $ ctorInfoId cinfo)
                         ++ show (pretty $ ctorInfoRepr cinfo)
                         ++ " and got\n" ++ show (pretty cm)) -}
 ClauseMatrix (concat [specializeRow row cinfo | row <- rows])
  where

    compatWith (LLCtorInfo c1 r1 _ _) (c2, r2) = c1 == c2 && r1 == r2

    specializeRow (ClauseRow orig []       a rng) _cinfo = [ClauseRow orig [] a rng]
    specializeRow (ClauseRow orig (p:rest) a rng)  cinfo@(ctor, _) =
      case p of
        SP_Variable _ -> [ClauseRow orig (wilds ++ rest) a rng]
          where wilds = List.replicate (ctorArity ctor) (SP_Wildcard)
        SP_Wildcard   -> [ClauseRow orig (wilds ++ rest) a rng]
          where wilds = List.replicate (ctorArity ctor) (SP_Wildcard)
        SP_Ctor c pats | c `compatWith` cinfo -> [ClauseRow orig (pats ++ rest) a rng]
        SP_Ctor _ _pats -> [] -- Unequal ctors -> no match
        SP_Or pats ->
            concatMap (\q -> specializeRow (ClauseRow orig (q:rest) a rng) cinfo) pats

defaultMatrix (ClauseMatrix rows) =
  ClauseMatrix (concatMap defaultRows rows)
  where
    defaultRows row =
      case row of
        ClauseRow orig []                     a rng -> [ClauseRow orig []   a rng]
        ClauseRow orig ((SP_Wildcard  ):rest) a rng -> [ClauseRow orig rest a rng]
        ClauseRow orig ((SP_Variable _):rest) a rng -> [ClauseRow orig rest a rng]
        ClauseRow _    ((SP_Ctor _   _):_   ) _   _ -> [] -- No row...
        ClauseRow orig ((SP_Or pats)   :rest) a rng ->
            concatMap (\p -> defaultRows (ClauseRow orig (p:rest) a rng)) pats

column :: ClauseMatrix a t -> Int -> [SPattern t]
column (ClauseMatrix rows) i = map (rowIndex i) rows

rowIndex :: Int -> ClauseRow a t -> SPattern t
rowIndex i (ClauseRow _ row _ _) = row !! i

ranges (ClauseMatrix rows) = map (\(ClauseRow _ _ _ r) -> r) rows

swapListElements j k elts =
  [case n of
    i | i == j -> elts !! k
      | i == k -> elts !! j
      | otherwise -> e
  | (e, n) <- List.zip elts [0..]]

swapOcc :: Int -> [Occurrence t] -> [Occurrence t]
swapOcc i occs = swapListElements i 0 occs

swapRow i (ClauseRow orig pats a rng) = ClauseRow orig pats' a rng
  where pats' = swapListElements i 0 pats

swapCol :: Int -> ClauseMatrix a t -> ClauseMatrix a t
swapCol i (ClauseMatrix rows) = ClauseMatrix (map (swapRow i) rows)

-- better :: (Set CtorId) -> (Map DataTypeName (Set CtorId)) -> Bool
isSignature :: (Set CtorId) -> (Map DataTypeName DataTypeSig) -> Bool
isSignature ctorSet allSigs =
  case Set.toList (Set.map ctorTypeName ctorSet) of
    ["Int8"]   -> False
    ["Int16"]  -> False
    ["Int32"]  -> False
    ["Int64"]  -> False
    ["Word"]   -> False
    ["WordX2"] -> False
    ["()"]     -> True
    ["Bool"]   -> Set.size ctorSet == 2
    [typename] ->
      case Map.lookup typename allSigs of
       (Just (DataTypeSig map)) -> Set.size ctorSet == Map.size map
       Nothing ->
         error $ "Error in PatternMatch.isSignature: "
              ++ "Unknown type name " ++ T.unpack typename ++ "! ctorSet = " ++ show ctorSet
    _ -> error $ "Error in PatternMatch.isSignature: "
              ++ "Multiple type names in ctor set: " ++ show ctorSet

deriving instance (Show a, Show t) => Show (DecisionTree a t)

instance Ord (CtorInfo t) where
  compare a b = compare (ctorInfoId a) (ctorInfoId b)

instance (Summarizable a, Structured a, PrettyT t) => Summarizable (DecisionTree a t) where
    textOf e _width =
      case e of
        DT_Fail _                -> text "DT_Fail      "
        DT_Leaf a idsoccs        -> text "DT_Leaf      " <> prettyT idsoccs <$> showStructure a
        DT_Switch  occ idsdts _  -> text "DT_Switch    " <> prettyT occ <+> prettyT (subIds idsdts)
               where   subIds idsDts          = map fst idsDts

instance Structured (DecisionTree a t) where
    childrenOf e =
      case e of
        DT_Fail {}               -> []
        DT_Leaf {}               -> []
        DT_Switch _occ idsdts md -> subDts idsdts md
                where  subDts idsDts Nothing  = map snd idsDts
                       subDts idsDts (Just d) = map snd idsDts ++ [d]
