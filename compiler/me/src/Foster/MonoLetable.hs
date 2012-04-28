-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt fMoe or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MonoLetable (MonoLetable(..)) where

import Foster.Base(LiteralInt, CtorId, AllocInfo, AllocMemRegion)
import Foster.MonoType(MoVar, MoPrim, MonoType)
import Foster.PatternMatch(Occurrence)

import qualified Data.Text as T

data MonoLetable =
          MoText        T.Text
        | MoBool        Bool
        | MoInt         MonoType LiteralInt
        | MoTuple       [MoVar]
        | MoOccurrence  MoVar Occurrence
        | MoCallPrim    MonoType MoPrim [MoVar]
        | MoCall        MonoType MoVar  [MoVar]
        | MoAppCtor     MonoType CtorId [MoVar]
        -- Stack/heap slot allocation
        | MoAllocate    (AllocInfo MonoType)
        -- Mutable ref cells
        | MoAlloc       MoVar AllocMemRegion
        | MoDeref       MoVar
        | MoStore       MoVar MoVar
        -- Array operations
        | MoAllocArray  MonoType MoVar
        | MoArrayRead   MonoType MoVar  MoVar
        | MoArrayPoke            MoVar  MoVar  MoVar
        deriving (Show)
