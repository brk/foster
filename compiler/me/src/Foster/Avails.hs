-----------------------------------------------------------------------------
-- Copyright (c) 2013 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Avails where

import qualified Data.Set as Set(union, insert, delete, size, intersection,
                                 difference, singleton, empty, toList, map,
                                 null)
import qualified Data.Map as Map(insertWith, unionWith, empty, toList,
                                 size, lookup, fromList)
import Data.Set(Set)
import Data.Map(Map)

data AvailSet elts = UniverseMinus (Set elts) | Avail (Set elts)
        deriving Show

delAvails       (UniverseMinus elts) es = UniverseMinus (Set.union es elts)
delAvails       (Avail         elts) es = Avail (availFrom elts (UniverseMinus es))

addAvail        (UniverseMinus elts) e  = UniverseMinus (Set.delete e elts)
addAvail        (Avail         elts) e  = Avail         (Set.insert e elts)

availFrom    es (UniverseMinus elts)    = Set.difference   es elts
availFrom    es (Avail         elts)    = Set.intersection es elts

lessAvail    es (UniverseMinus elts)    = Set.intersection es elts
lessAvail    es (Avail         elts)    = Set.difference   es elts

availIn e a = not $ Set.null $ availFrom (Set.singleton e) a

intersectAvails (UniverseMinus e1) (UniverseMinus e2) = UniverseMinus (Set.union e1 e2)
intersectAvails (Avail es) a = Avail (availFrom es a)
intersectAvails a (Avail es) = Avail (availFrom es a)

availSmaller    (UniverseMinus e1) (UniverseMinus e2) = Set.size e2 < Set.size e1
availSmaller    (Avail e1)         (Avail e2)         = Set.size e1 < Set.size e2
availSmaller    (Avail _ )         (UniverseMinus s) | null (Set.toList s) = True
availSmaller _ _ = error $ "GCRoots.hs: Can't compare sizes of Avail and UniverseMinus..."
--availSmaller a u = error $ "Can't compare sizes of " ++ show a ++ " and " ++ show u



data AvailMap key val = AvailMap (AvailSet key)
                                 (Map      key (Set val)) deriving Show
emptyAvailMap = AvailMap (Avail         Set.empty) Map.empty
botAvailMap   = AvailMap (UniverseMinus Set.empty) Map.empty
-- Both of these maps are empty, but they have different properties.
-- The bottom map is the identity for joins, and emptyAvailMap is top.

intersectAvailMap (AvailMap oa om) (AvailMap na nm) =
  let
       ja = na `intersectAvails` oa
       jm = Map.unionWith Set.intersection om nm
  in (AvailMap ja jm,  availSmaller ja oa || Map.size jm /= Map.size om)

insertAvailMap key val (AvailMap a m) =
                 (AvailMap (a `addAvail` key)
                             (Map.insertWith Set.union key (Set.singleton val) m))

lookupAvailMap key (AvailMap a m) =
  if availIn key a
   then case fmap Set.toList (Map.lookup key m) of
               Nothing -> []
               Just vs -> vs
   else []

concretizeAvail fk (Avail s)         = Avail (Set.map fk s)
concretizeAvail fk (UniverseMinus s) = UniverseMinus (Set.map fk s)
concretizeAvailMap fk fv (AvailMap a m) =
  (concretizeAvail fk a
  ,   Map.fromList [(fk k, fv v) | (k, v) <- Map.toList m
                                 , availIn k a])

--instance Show (AvailSet LLVar) where
--  show (UniverseMinus elts) = "(UniverseMinus " ++ show (map tidIdent $ Set.toList elts) ++ ")"
--  show (Avail         elts) = "(Avail "         ++ show (map tidIdent $ Set.toList elts) ++ ")"
--
--ptidIdent (x,y) = (tidIdent x, tidIdent y)
--instance Show (AvailSet (LLVar, LLVar)) where
--  show (UniverseMinus elts) = "(UniverseMinus " ++ show (map ptidIdent $ Set.toList elts) ++ ")"
--  show (Avail         elts) = "(Avail "         ++ show (map ptidIdent $ Set.toList elts) ++ ")"
--

