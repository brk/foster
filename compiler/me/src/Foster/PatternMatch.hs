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

import Foster.Base

{-
Straightforward implementation of pattern match compilation
as laid out by Luc Maranget in his ML'08 paper
        Compiling Pattern Matching to Good Decision Trees

For now, we do not enforce maximal sharing of decision subtrees,
and use only the naive leftmost-outermost-first column selection
heuristic.
-}

data Show a =>
   DecisionTree a = DT_Fail
                  | DT_Leaf   a  [(Ident, Occurrence)]
                  | DT_Swap   Int      (DecisionTree a)
                  | DT_Switch Occurrence (SwitchCase a)
                  deriving (Show)

data Show a =>
   SwitchCase a = SwitchCase [(CtorId, DecisionTree a)]
                               (Maybe (DecisionTree a))
                  deriving (Show)

-- Avoiding all these type parameters is actually a
-- pretty good use case for parameterized modules!
data Show a =>
     Action a   = Action     a          deriving (Show)

type Occurrence = [Int]
type ClauseCol  = [SPattern]
data Show a =>
     ClauseMatrix a = ClauseMatrix [ClauseRow a] deriving Show
data Show a =>
     ClauseRow a    = ClauseRow { rowOrigPat  ::  SPattern
                                , rowPatterns :: [SPattern]
                                , rowAction   :: a }  deriving Show

data SPattern = SP_Wildcard
              | SP_Variable  Ident
              | SP_Ctor      CtorId  [SPattern]
             deriving (Show)

instance (Show a, Structured a) => Structured (DecisionTree a) where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
          DT_Fail           -> out $ "DT_Fail      "
          DT_Leaf a idsoccs -> (out $ "DT_Leaf    " ++ show idsoccs ++ "\n") ++ (showStructure a)
          DT_Swap i dt      -> out $ "DT_Swap      " ++ (show i)
          DT_Switch occ sc  -> out $ "DT_Switch    " ++ (show occ) ++ (show $ subIds sc)
    structuredChildren e = map SS $ childrenOf e
    childrenOf e =
      case e of
        (DT_Fail)     -> []
        (DT_Leaf _ _) -> []
        (DT_Swap i dt)      -> [dt]
        (DT_Switch occ sc)  -> subDts sc

subIds (SwitchCase idsDts _) = map fst idsDts
subDts (SwitchCase idsDts Nothing)  = map snd idsDts
subDts (SwitchCase idsDts (Just d)) = map snd idsDts ++ [d]

compilePatterns :: Show a => [(Pattern, a)] -> DataTypeSigs -> DecisionTree a
compilePatterns bs allSigs =
 cc [[]] (ClauseMatrix $ map compilePatternRow bs) allSigs
 where
  compilePatternRow (p, a) = ClauseRow (compilePattern p)
                                       [compilePattern p] a
  compilePattern p = case p of
    (P_Wildcard _  )   -> SP_Wildcard
    (P_Variable _ v)   -> SP_Variable v
    (P_Bool     _ b)   -> SP_Ctor (boolCtor b)  []
    (P_Int      _ i)   -> SP_Ctor (int32Ctor i) []
    (P_Ctor _ pats cid) ->SP_Ctor cid (map compilePattern pats)
    (P_Tuple _ pats)   -> SP_Ctor (tupleCtor pats)  (map compilePattern pats)
  boolCtor False = CtorId "Bool" "False" 0 0
  boolCtor True  = CtorId "Bool" "True"  0 1

  tupleCtor pats = CtorId "()" "()" (Prelude.length pats) 0

  int32Ctor li = CtorId "Int32" "<Int32>" 0
                               (if litIntMinBits li <= 32
                                  then fromInteger $ litIntValue li
                                  else error "cannot cram >32 bits into Int32!")

computeBindings :: (Occurrence, SPattern) -> [(Ident, Occurrence)]
computeBindings (occ, SP_Variable i) = [(i, occ)]
computeBindings (occ, SP_Wildcard  ) = []
computeBindings (occ, SP_Ctor _ pats) =
  let occs = expand occ (Prelude.length pats) in
  concatMap computeBindings (zip occs pats)

-- "Compilation is defined by cases as follows."
cc :: Show a => [Occurrence] -> ClauseMatrix a -> DataTypeSigs -> DecisionTree a

-- No row to match -> failure
cc _ (ClauseMatrix []) allSigs = DT_Fail

-- If first row is all variables, match always succeeds.
cc occs cm allSigs | allGuaranteedMatch (rowPatterns $ firstRow cm) =
        -- TODO need to bind these identifiers
        let r = firstRow cm in
        DT_Leaf (rowAction r) (computeBindings ([], rowOrigPat r))

-- "In any other case, matrix P has at least one row and at least one
-- column (m > 0, n > 0). Furthermore, there exists at least one
-- column of which at least one pattern is not a wildcard. Select
-- one such column i."
cc occs cm allSigs =
  let i = columnNumWithNonTrivialPattern cm in
  if  i == 0
   then
      let c = cm `column` i in
      let hctors = Set.fromList (concat $ map headCtor c) in
      let (o1:orest) = occs in
      let caselist = [ (c, cc (expand o1 (ctorArity c) ++ orest)
                              (specialize c cm) allSigs)
                     | c <- Set.toList hctors] in
      if isSignature hctors allSigs
        then DT_Switch o1 (noDefault caselist)
        else let ad = cc orest (defaultMatrix cm) allSigs in
             DT_Switch o1 (caselist `withDefault` ad)
    else
      let o' = swapOcc i occs in
      let m' = swapCol i cm   in
      {- DT_Swap i $ -} cc o' m' allSigs

allGuaranteedMatch pats = List.all trivialMatch pats

trivialMatch (SP_Wildcard  ) = True
trivialMatch (SP_Variable _) = True
trivialMatch (SP_Ctor   _ _) = False

firstRow (ClauseMatrix (r:_)) = r
firstRow (ClauseMatrix []) = error "precondition violated for firstRow helper!"

headCtor (SP_Wildcard  ) = []
headCtor (SP_Variable _) = []
headCtor (SP_Ctor c   _) = [c]

noDefault   caselist    = SwitchCase caselist Nothing
withDefault caselist ad = SwitchCase caselist (Just ad)

columnNumWithNonTrivialPattern cm =
  loop cm 0 where
  loop cm n = if allGuaranteedMatch (cm `column` n)
                then loop cm (n + 1)
                else n

expand occ a = [occ ++ [n] | n <- [0 .. a - 1]]

specialize ctor (ClauseMatrix rows) =
  ClauseMatrix [specializeRow row ctor | row <- rows
                                       , isCompatible row ctor]
  where
    isCompatible row ctor =
      case rowPatterns row of
        []               -> False
        ((SP_Wildcard  ):_) -> True
        ((SP_Variable _):_) -> True
        ((SP_Ctor c   _):_) -> c == ctor

    specializeRow (ClauseRow orig []       a) ctor = ClauseRow orig [] a
    specializeRow (ClauseRow orig (p:rest) a) ctor =
      case p of
        SP_Variable _ -> ClauseRow orig (wilds ++ rest) a
          where wilds = List.replicate (ctorArity ctor) (SP_Wildcard)
        SP_Wildcard   -> ClauseRow orig (wilds ++ rest) a
          where wilds = List.replicate (ctorArity ctor) (SP_Wildcard)
        SP_Ctor c pats | c == ctor -> ClauseRow orig (pats ++ rest) a
        SP_Ctor c pats -> error $ "specializeRow with unequal ctor?!? "
                             ++ show c ++ " // " ++ show ctor

defaultMatrix (ClauseMatrix rows) =
  ClauseMatrix (concat [defaultRow row | row <- rows])
  where
    defaultRow row =
      case row of
        ClauseRow orig []                     a -> [ClauseRow orig []   a]
        ClauseRow orig ((SP_Wildcard  ):rest) a -> [ClauseRow orig rest a]
        ClauseRow orig ((SP_Variable _):rest) a -> [ClauseRow orig rest a]
        ClauseRow orig ((SP_Ctor c   _):rest) a -> [] -- No row...
column (ClauseMatrix rows) i = map (rowIndex i) rows

rowIndex i (ClauseRow _ row _) = row !! i

swapListElements j k elts =
  [case n of
    i | i == j -> elts !! k
      | i == k -> elts !! j
      | otherwise -> e
  | (e, n) <- List.zip elts [0..]]

swapOcc i occs = swapListElements i 0 occs
swapRow i (ClauseRow orig pats a) = ClauseRow orig pats' a
  where pats' = swapListElements i 0 pats

swapCol :: Show a => Int -> ClauseMatrix a -> ClauseMatrix a
swapCol i (ClauseMatrix rows) = ClauseMatrix (map (swapRow i) rows)

-- better :: (Set CtorId) -> (Map DataTypeName (Set CtorId)) -> Bool
isSignature :: (Set CtorId) -> (Map DataTypeName DataTypeSig) -> Bool
isSignature ctorSet allSigs =
  case Set.toList (Set.map ctorTypeName ctorSet) of
    ["Int32"] -> False
    ["()"] -> True
    ["Bool"] -> Set.size ctorSet == 2
    [typename] ->
      case Map.lookup typename allSigs of
       (Just (DataTypeSig map)) -> Set.size ctorSet == Map.size map
       Nothing ->
        error $ "isSignature: Unknown type name " ++ typename ++ "! ctorSet = " ++ show ctorSet
    otherwise ->
      error $ "Error in PatternMatch.isSignature: "
           ++ "Multiple type names in ctor set: " ++ show ctorSet


