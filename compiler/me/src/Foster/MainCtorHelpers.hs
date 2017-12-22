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

withDataTypeCtors :: DataType ty -> (CtorId -> DataCtor ty -> Int -> res) -> [res]
withDataTypeCtors dtype f =
  [f (ctorId (typeFormalName $ dataTypeName dtype) ctor) ctor n
   | (ctor, n) <- zip (dataTypeCtors dtype) [0..]]

getDataTypes :: [DataType t] -> Map DataTypeName [DataType t]
getDataTypes datatypes = Map.unionsWith (++) $ map single datatypes
  where
    single dt = Map.singleton (typeFormalName $ dataTypeName dt) [dt]

getCtorInfo :: [DataType t] -> Map CtorName [CtorInfo t]
getCtorInfo datatypes = Map.unionsWith (++) $ map getCtorInfoList datatypes
  where
    getCtorInfoList :: DataType t -> Map CtorName [CtorInfo t]
    getCtorInfoList (DataType formal _tyformals ctors _isForeign _range) =
          Map.fromList $ map (buildCtorInfo (typeFormalName formal)) ctors

    buildCtorInfo :: DataTypeName -> DataCtor t
                  -> (CtorName, [CtorInfo t])
    buildCtorInfo name ctor =
      case ctorIdFor name ctor of (n, c) -> (n, [CtorInfo c ctor])

getCtorInfo' :: [EffectDecl t] -> Map CtorName [(CtorId, EffectCtor t)]
getCtorInfo' effdecls = Map.unionsWith (++) $ map getEffCtorInfoList effdecls
  where
    getEffCtorInfoList :: EffectDecl t -> Map CtorName [(CtorId, EffectCtor t)]
    getEffCtorInfoList (EffectDecl formal _tyformals ctors _range) =
          Map.fromList $ map (buildEffCtorInfo (typeFormalName formal)) ctors

    buildEffCtorInfo :: DataTypeName -> EffectCtor t
                     -> (CtorName, [(CtorId, EffectCtor t)])
    buildEffCtorInfo name ector =
      case ctorIdFor name (effectCtorAsData ector) of
          (n, c) -> (n, [(c, ector)])

-----------------------------------------------------------------------

ctorIdFor :: String -> DataCtor t -> (CtorName, CtorId)
ctorIdFor tynm ctor = (dataCtorName ctor, ctorId tynm ctor)

ctorId   tynm (DataCtor ctorName _tyformals types _repr _range) =
  CtorId tynm (T.unpack ctorName) (Prelude.length types)

-----------------------------------------------------------------------

dataTypeSigs :: Show t => [DataType t] -> Map DataTypeName DataTypeSig
dataTypeSigs datatypes = Map.fromList $ map ctorIdSet datatypes
 where
  ctorIdSet :: Show t => DataType t -> (DataTypeName, DataTypeSig)
  ctorIdSet (DataType formal _tyformals ctors _isForeign _range) =
      (typeFormalName formal,
       DataTypeSig (Map.fromList $ map (ctorIdFor (typeFormalName formal)) ctors))

