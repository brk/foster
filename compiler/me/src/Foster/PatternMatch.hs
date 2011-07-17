-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt fCFe or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.PatternMatch where

import qualified Data.List as List
import qualified Data.Set  as Set
import Data.Set(Set)

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
data CtorId     = CtorId     String Int deriving (Show, Eq)
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

instance Ord CtorId where
  compare a b = compare (show a) (show b)

compilePatterns :: Show a => [(Pattern, a)] -> [Set CtorId] -> DecisionTree a
compilePatterns bs allSigs =
 cc [[]] (ClauseMatrix $ map compilePatternRow bs) allSigs
 where
  compilePatternRow (p, a) = ClauseRow (compilePattern p)
                                       [compilePattern p] a
  compilePattern p = case p of
    (P_Wildcard _  ) -> SP_Wildcard
    (P_Variable _ v) -> SP_Variable v
    (P_Bool     _ b) -> SP_Ctor (boolCtor b)  []
    (P_Int      _ i) -> SP_Ctor (int32Ctor i) []
    (P_Tuple _ pats) -> SP_Ctor (tupleCtor pats) (map compilePattern pats)
  boolCtor False = CtorId "Bool" 0
  boolCtor True  = CtorId "Bool" 1

  tupleCtor pats = CtorId "()" (Prelude.length pats)

  int32Ctor li = CtorId "Int32" (if litIntMinBits li <= 32
                                  then fromInteger $ litIntValue li
                                  else error "cannot cram >32 bits into Int32!")

computeBindings :: (Occurrence, SPattern) -> [(Ident, Occurrence)]
computeBindings (occ, SP_Variable i) = [(i, occ)]
computeBindings (occ, SP_Wildcard  ) = []
computeBindings (occ, SP_Ctor (CtorId "()" _) pats) =
  let occs = expand occ (Prelude.length pats) in
  concat $ map computeBindings (zip occs pats)
computeBindings (occ, SP_Ctor (CtorId c _) pats)
        | c == "Int32" || c == "Bool" = []
computeBindings (occ, SP_Ctor c pats) =
  error $ "computeBindings " ++ show c ++ " ;; " ++ show pats

-- "Compilation is defined by cases as follows."
cc :: Show a => [Occurrence] -> ClauseMatrix a -> [Set CtorId] -> DecisionTree a

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
      let caselist = [ (c, cc (expand o1 (arityOf c) ++ orest)
                              (specialize c cm) allSigs)
                     | c <- Set.toList hctors] in
      if isSignature hctors allSigs
        then DT_Switch o1 (noDefault caselist)
        else let ad = cc orest (defaultMatrix cm) allSigs in
             DT_Switch o1 (caselist `withDefault` ad)
    else
      let o' = swapOcc i occs in
      let m' = swapCol i cm   in
      DT_Swap i $ cc o' m' allSigs

allGuaranteedMatch pats = List.all trivialMatch pats
anyGuaranteedMatch pats = List.any trivialMatch pats

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
          where wilds = List.replicate (arityOf ctor) (SP_Wildcard)
        SP_Wildcard   -> ClauseRow orig (wilds ++ rest) a
          where wilds = List.replicate (arityOf ctor) (SP_Wildcard)
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

arityOf (CtorId "List" 0) = 0
arityOf (CtorId "List" 1) = 2
arityOf (CtorId "()"   n) = n
arityOf (CtorId "Int32" _) = 0
arityOf c                 = error $ "arityOf " ++ show c

isSignature ctorSet allSigs =
  let typeNames = Set.map (\(CtorId n _) -> n) ctorSet in
  case Set.toList typeNames of
    ["Int32"] -> False
    ["()"] -> True
    ["List"] ->
      ctorSet == Set.fromList [CtorId "List" 0, CtorId "List" 1]
    ["Bool"] ->
      ctorSet == Set.fromList [CtorId "Bool" 0, CtorId "Bool" 1]
    [typename] ->
      error $ "isSignature: Unknown type name! ctorSet = " ++ show ctorSet
    otherwise ->
      error $ "isSignature: Multiple type names in ctor set!"


