-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MonoType where

import Foster.Base

data MonoType =
           PrimInt       IntSizeBits
         | TyConApp      DataTypeName [MonoType]
         | TupleType     [MonoType]
         | FnType        { monoFnTypeDomain :: MonoType
                         , monoFnTypeRange  :: MonoType
                         , monoFnTypeCallConv :: CallConv
                         , monoFnTypeProcOrFunc :: ProcOrFunc }
         | CoroType      MonoType MonoType
         | ArrayType     MonoType
         | PtrType       MonoType
         deriving (Show)

type MoVar = TypedId MonoType
type MoPrim = FosterPrim MonoType

