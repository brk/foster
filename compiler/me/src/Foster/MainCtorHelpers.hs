-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MainCtorHelpers where

import Data.Map(Map)
import qualified Data.Map as Map(fromList, unionsWith, singleton)
import qualified Data.Text as T

import Foster.Base
import Foster.TypeAST

getDataTypes :: [DataType TypeAST] -> Map DataTypeName [DataType TypeAST]
getDataTypes datatypes = Map.unionsWith (++) $ map single datatypes
  where
    single dt = Map.singleton (dataTypeName dt) [dt]

getCtorInfo :: [DataType TypeAST] -> Map CtorName [CtorInfo TypeAST]
getCtorInfo datatypes = Map.unionsWith (++) $ map getCtorInfoList datatypes
  where
    getCtorInfoList :: DataType TypeAST -> Map CtorName [CtorInfo TypeAST]
    getCtorInfoList (DataType name _tyformals ctors) =
          Map.fromList $ map (buildCtorInfo name) ctors

    buildCtorInfo :: DataTypeName -> DataCtor TypeAST
                  -> (CtorName, [CtorInfo TypeAST])
    buildCtorInfo name ctor =
      case ctorIdFor name ctor of (n, c) -> (n, [CtorInfo c ctor])

-----------------------------------------------------------------------

ctorIdFor :: (Show t) => String -> DataCtor t -> (CtorName, CtorId)
ctorIdFor name ctor = (ctorNameOf ctor, ctorId name ctor)
  where
    ctorNameOf (DataCtor ctorName _n _) = ctorName
    ctorId nm (DataCtor ctorName n types) =
      CtorId nm (T.unpack ctorName) (Prelude.length types) n

-----------------------------------------------------------------------

dataTypeSigs :: Show t => [DataType t] -> Map DataTypeName DataTypeSig
dataTypeSigs datatypes = Map.fromList $ map ctorIdSet datatypes
 where
  ctorIdSet :: Show t => DataType t -> (DataTypeName, DataTypeSig)
  ctorIdSet (DataType name _tyformals ctors) =
      (name, DataTypeSig (Map.fromList $ map (ctorIdFor name) ctors))
