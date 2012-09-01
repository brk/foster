-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MonoType where

import Foster.Base

data MonoType =
           PrimInt       IntSizeBits
         | PrimFloat64
         | TyConApp      DataTypeName [MonoType]
         | TupleType     [MonoType]
         | StructType    [MonoType]
         | FnType        { monoFnTypeDomain :: [MonoType]
                         , monoFnTypeRange  :: MonoType
                         , monoFnTypeCallConv :: CallConv
                         , monoFnTypeProcOrFunc :: ProcOrFunc }
         | CoroType      MonoType MonoType
         | ArrayType     MonoType
         | PtrType       MonoType
         | PtrTypeUnknown
         deriving (Show)

extractFnType ft@(FnType {}) = ft
extractFnType (PtrType (StructType (ft@(FnType s t cc FT_Proc):_))) = FnType s t cc FT_Func

extractFnType other = error $ "Unable to extract fn type from " ++ show other

boolMonoType = PrimInt I1

type MoVar = TypedId MonoType
type MoPrim = FosterPrim MonoType

data MoExternDecl = MoExternDecl String MonoType deriving (Show)
