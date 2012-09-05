-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeLL where

import Foster.Base

data TypeLL =
           LLPrimInt       IntSizeBits
         | LLPrimFloat64
         | LLTyConApp      DataTypeName [TypeLL]
         | LLStructType    [TypeLL]
         | LLProcType      { llProcTypeDomain   :: [TypeLL]
                           , llProcTypeRange    :: TypeLL
                           , llProcTypeCallConv :: CallConv
                           }
         | LLCoroType      TypeLL TypeLL
         | LLArrayType     TypeLL
         | LLPtrType       TypeLL
         | LLPtrTypeUnknown
         deriving (Show)

llBoolType = LLPrimInt I1

type LLVar = TypedId TypeLL
type LLPrim = FosterPrim TypeLL

data LLExternDecl = LLExternDecl String TypeLL deriving (Show)

extractCallConv (LLProcType _ _ cc) = cc
extractCallConv (LLPtrType (LLStructType ((LLProcType _ _ cc):_))) = cc
