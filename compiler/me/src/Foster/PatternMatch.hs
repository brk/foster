{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt fCFe or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.PatternMatch where

import qualified Data.List as List
import Data.Set(Set)
import qualified Data.Set  as Set(size, fromList, toList, map)
import Data.Map(Map)
import qualified Data.Map  as Map(lookup, size)

import qualified Data.Text as T

import Foster.Base

import Text.PrettyPrint.ANSI.Leijen hiding (column)

{-
Straightforward implementation of pattern match compilation
as laid out by Luc Maranget in his ML'08 paper
        Compiling Pattern Matching to Good Decision Trees

For now, we do not enforce maximal sharing of decision subtrees,
and use only the naive leftmost-outermost-first column selection
heuristic.
-}

data DecisionTree a t
    =  DT_Fail
    |  DT_Leaf  a                -- The expression/block id to evaluate/jump to.
         [(TypedId t, Occurrence t)]  -- Subterms of scrutinee to bind in leaf.
    |  DT_Switch
                      (Occurrence t)  -- Subterm of scrutinee to switch on.
                [(CtorId, DecisionTree a t)] -- Map of ctors to decision trees.
                  (Maybe (DecisionTree a t)) -- Default decision tree, if any.

-- Avoiding all these type parameters seems like a
-- pretty good use case for parameterized modules!

type ClauseCol t = [SPattern t]
data ClauseMatrix a t = ClauseMatrix [ClauseRow a t]
data ClauseRow a t  = ClauseRow { rowOrigPat  :: (SPattern t)
                                , rowPatterns :: [SPattern t]
                                , rowAction   :: a }

data SPattern t = SP_Wildcard
                | SP_Variable (TypedId t)
                | SP_Ctor     (CtorInfo t) [SPattern t]
               deriving (Show)

type DataTypeSigs = Map DataTypeName DataTypeSig

compilePatterns :: IntSized t
                => [((Pattern t, _binds), a)]
                -> DataTypeSigs
                -> DecisionTree a t
compilePatterns bs allSigs =
 cc [[]] (ClauseMatrix $ map compilePatternRow bs) allSigs where

  compilePatternRow ((p, _binds), a) = ClauseRow (compilePattern p)
                                                 [compilePattern p] a
  compilePattern :: IntSized t => Pattern t -> SPattern t
  compilePattern p = case p of
    (P_Wildcard _ _)       -> SP_Wildcard
    (P_Variable _ v)       -> SP_Variable v
    (P_Bool     _ _ b)     -> SP_Ctor (boolCtor b)     []
    (P_Int     _ ty i)     -> SP_Ctor (intCtor ty i)   []
    (P_Ctor  _ _ pats nfo) -> SP_Ctor nfo              (map compilePattern pats)
    (P_Tuple _ _ pats)     -> SP_Ctor (tupleCtor pats) (map compilePattern pats)
    where
          ctorInfo tynm dcnm dctys dctag =
             let dttyformals = [] in -- assume used only for simple data types
             let dctor = DataCtor (T.pack dcnm) dctag dttyformals dctys in
             CtorInfo (CtorId tynm dcnm (Prelude.length $ dctys) dctag) dctor

          boolCtor False = ctorInfo "Bool"  "False" []                     0
          boolCtor True  = ctorInfo "Bool"  "True"  []                     1
          tupleCtor pats = ctorInfo "()"    "()"    (map patternType pats) 0
          intCtor ty li  = ctorInfo ctnm ("<"++ctnm++">") [] tag
                             where
                              bits = intSizeOf ty
                              ctnm = "Int" ++ show bits
                              tag  = if litIntMinBits li <= bits
                                      then fromInteger $ litIntValue li
                                      else error $ "cannot cram " ++ show bits
                                               ++ " bits into Int"++ show (litIntMinBits li)++"!"
          patternType :: Pattern ty -> ty
          patternType pattern = case pattern of
                  P_Wildcard  _rng ty     -> ty
                  P_Variable  _rng tid    -> tidType tid
                  P_Ctor      _rng ty _ _ -> ty
                  P_Bool      _rng ty _   -> ty
                  P_Int       _rng ty _   -> ty
                  P_Tuple     _rng ty _   -> ty

-- "Compilation is defined by cases as follows."
cc :: [Occurrence t] -> ClauseMatrix a t -> DataTypeSigs -> DecisionTree a t

-- No row to match -> failure
cc _ (ClauseMatrix []) _allSigs = DT_Fail

-- If first row is all variables, match always succeeds.
cc _occs cm _allSigs | allGuaranteedMatch (rowPatterns $ firstRow cm) =
    DT_Leaf (rowAction r)
            (computeBindings emptyOcc (rowOrigPat r))
      where r = firstRow cm
            emptyOcc = []
            computeBindings :: Occurrence t -> SPattern t -> [(TypedId t, Occurrence t)]
            computeBindings  occ (SP_Variable v   ) = [(v, occ)]
            computeBindings _occ (SP_Wildcard     ) = []
            computeBindings  occ (SP_Ctor ctorinfo pats) =
              let occs = expand occ ctorinfo (Prelude.length pats) in
              concatMap (uncurry computeBindings) (zip occs pats)

-- "In any other case, matrix P has at least one row and at least one
-- column (m > 0, n > 0). Furthermore, there exists at least one
-- column of which at least one pattern is not a wildcard. Select
-- one such column i."
cc occs cm allSigs =
  let i = columnNumWithNonTrivialPattern cm in
  if  i == 0
   then
      let spPatterns = cm `column` i in
      let headCtorInfos = Set.fromList (concatMap headCtorInfo spPatterns) in
      let (o1:orest) = occs in
      let caselist = [ (ctorInfoId c,
                           cc (expand o1 c (ctorInfoArity c) ++ orest)
                              (specialize c cm) allSigs)
                     | c <- Set.toList headCtorInfos] in
      if isSignature (Set.map ctorInfoId headCtorInfos) allSigs
        then DT_Switch o1 caselist Nothing
        else let ad = cc orest (defaultMatrix cm) allSigs in
             DT_Switch o1 caselist (Just ad)
    else
      let o' = swapOcc i occs in
      let m' = swapCol i cm   in
      {- DT_Swap i $ -} cc o' m' allSigs

allGuaranteedMatch pats = List.all trivialMatch pats
                             where trivialMatch (SP_Wildcard  ) = True
                                   trivialMatch (SP_Variable _) = True
                                   trivialMatch (SP_Ctor   _ _) = False

firstRow (ClauseMatrix (r:_)) = r
firstRow (ClauseMatrix []) = error "precondition violated for firstRow helper!"

headCtorInfo (SP_Wildcard    ) = []
headCtorInfo (SP_Variable   _) = []
headCtorInfo (SP_Ctor cinfo _) = [cinfo]

columnNumWithNonTrivialPattern cm =
  loop cm 0 where
  loop cm n = if allGuaranteedMatch (cm `column` n)
                then loop cm (n + 1)
                else n

expand :: Occurrence t -> CtorInfo t -> Int -> [Occurrence t]
expand occ cid a = [occ ++ [(n, cid)] | n <- [0 .. a - 1]]

ctorInfoArity (CtorInfo cid _) = ctorArity cid

specialize :: CtorInfo t -> ClauseMatrix a t -> ClauseMatrix a t
specialize (CtorInfo ctor _) (ClauseMatrix rows) =
  ClauseMatrix [specializeRow row ctor | row <- rows
                                       , isCompatible row ctor]
  where
    isCompatible row ctor =
      case rowPatterns row of
        []               -> False
        ((SP_Wildcard             ):_) -> True
        ((SP_Variable            _):_) -> True
        ((SP_Ctor (CtorInfo c _) _):_) -> c == ctor

    specializeRow (ClauseRow orig []       a) _ctor = ClauseRow orig [] a
    specializeRow (ClauseRow orig (p:rest) a)  ctor =
      case p of
        SP_Variable _ -> ClauseRow orig (wilds ++ rest) a
          where wilds = List.replicate (ctorArity ctor) (SP_Wildcard)
        SP_Wildcard   -> ClauseRow orig (wilds ++ rest) a
          where wilds = List.replicate (ctorArity ctor) (SP_Wildcard)
        SP_Ctor (CtorInfo c _)  pats | c == ctor -> ClauseRow orig (pats ++ rest) a
        SP_Ctor (CtorInfo c _) _pats -> error $ "specializeRow with unequal ctor?!? "
                                               ++ show c ++ " // " ++ show ctor

defaultMatrix (ClauseMatrix rows) =
  ClauseMatrix (concat [defaultRow row | row <- rows])
  where
    defaultRow row =
      case row of
        ClauseRow orig []                     a -> [ClauseRow orig []   a]
        ClauseRow orig ((SP_Wildcard  ):rest) a -> [ClauseRow orig rest a]
        ClauseRow orig ((SP_Variable _):rest) a -> [ClauseRow orig rest a]
        ClauseRow _    ((SP_Ctor _   _):_   ) _ -> [] -- No row...

column :: ClauseMatrix a t -> Int -> [SPattern t]
column (ClauseMatrix rows) i = map (rowIndex i) rows

rowIndex :: Int -> ClauseRow a t -> SPattern t
rowIndex i (ClauseRow _ row _) = row !! i

swapListElements j k elts =
  [case n of
    i | i == j -> elts !! k
      | i == k -> elts !! j
      | otherwise -> e
  | (e, n) <- List.zip elts [0..]]

swapOcc :: Int -> [Occurrence t] -> [Occurrence t]
swapOcc i occs = swapListElements i 0 occs

swapRow i (ClauseRow orig pats a) = ClauseRow orig pats' a
  where pats' = swapListElements i 0 pats

swapCol :: Int -> ClauseMatrix a t -> ClauseMatrix a t
swapCol i (ClauseMatrix rows) = ClauseMatrix (map (swapRow i) rows)

-- better :: (Set CtorId) -> (Map DataTypeName (Set CtorId)) -> Bool
isSignature :: (Set CtorId) -> (Map DataTypeName DataTypeSig) -> Bool
isSignature ctorSet allSigs =
  case Set.toList (Set.map ctorTypeName ctorSet) of
    ["Int8"]  -> False
    ["Int16"] -> False
    ["Int32"] -> False
    ["Int64"] -> False
    ["()"] -> True
    ["Bool"] -> Set.size ctorSet == 2
    [typename] ->
      case Map.lookup typename allSigs of
       (Just (DataTypeSig map)) -> Set.size ctorSet == Map.size map
       Nothing ->
         error $ "Error in PatternMatch.isSignature: "
              ++ "Unknown type name " ++ typename ++ "! ctorSet = " ++ show ctorSet
    _ -> error $ "Error in PatternMatch.isSignature: "
              ++ "Multiple type names in ctor set: " ++ show ctorSet

deriving instance (Show a, Show t) => Show (DecisionTree a t)

instance Eq (CtorInfo t) where
  a == b = (ctorInfoId a) == (ctorInfoId b)

instance Ord (CtorInfo t) where
  compare a b = compare (ctorInfoId a) (ctorInfoId b)

instance (Structured a, Show t) => Structured (DecisionTree a t) where
    textOf e _width =
      case e of
        DT_Fail                  ->  text $ "DT_Fail      "
        DT_Leaf a idsoccs        -> (text $ "DT_Leaf    " ++ show idsoccs) <$> showStructure a
        DT_Switch  occ idsdts _  ->  text $ "DT_Switch    " ++ (show occ) ++ (show $ subIds idsdts)
               where   subIds idsDts          = map fst idsDts
    childrenOf e =
      case e of
        DT_Fail                  -> []
        DT_Leaf {}               -> []
        DT_Switch _occ idsdts md -> subDts idsdts md
                where  subDts idsDts Nothing  = map snd idsDts
                       subDts idsDts (Just d) = map snd idsDts ++ [d]
