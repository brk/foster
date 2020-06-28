module Foster.BaseUtils where

import Data.Sequence(Seq)
import qualified Data.Sequence as Seq

import Data.Map(Map)
import qualified Data.Map as Map(lookup)

data MapSeqLookup a =
    MSL_Missing
  | MSL_Empty
  | MSL_Lone a
  | MSL_Many (Seq a)

mapSeqLookup :: Ord k => k -> Map k (Seq a) -> MapSeqLookup a
mapSeqLookup k m =
  case Map.lookup k m of
    Nothing -> MSL_Missing
    Just s ->
      case Seq.viewl s of
        Seq.EmptyL -> MSL_Empty
        x Seq.:< xs | Seq.null xs -> MSL_Lone x
        _ -> MSL_Many s

seqAssocLookup :: Eq k => k -> Seq (k, v) -> Maybe v
seqAssocLookup k s =
    case Seq.viewl s of
    Seq.EmptyL -> Nothing
    (x, v) Seq.:< xs ->
        if k == x then Just v else seqAssocLookup k xs