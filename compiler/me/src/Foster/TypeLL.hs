{-# LANGUAGE Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeLL where

import Foster.Base

import qualified Data.Text as T

data TypeLL =
           LLPrimInt       IntSizeBits
         | LLNamedType     T.Text
         | LLStructType    [TypeLL]
         | LLProcType      { llProcTypeDomain   :: [TypeLL]
                           , llProcTypeRange    :: TypeLL
                           , llProcTypeCallConv :: CallConv
                           }
         | LLCoroType      TypeLL TypeLL
         | LLArrayType     TypeLL
         | LLPtrType       TypeLL
         | LLPtrTypeUnknown
         deriving (Eq, Show, Ord)

llBoolType = LLPrimInt I1

type LLVar = TypedId TypeLL
type LLPrim = FosterPrim TypeLL

data LLExternDecl = LLExternDecl T.Text TypeLL IsForeignDecl deriving (Show)

extractCallConv (LLProcType _ _ cc) = cc
extractCallConv (LLPtrType (LLStructType ((LLProcType _ _ cc):_))) = cc
extractCallConv (LLPtrTypeUnknown) = FastCC
extractCallConv other = error $ "TypeLL.hs: cannot extract calling convention from " ++ show other

