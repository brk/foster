-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Letable (Letable(..)) where

import Foster.Base(LiteralInt, LiteralFloat, CtorId, ArrayIndex,
                   AllocMemRegion, Occurrence)
import Foster.TypeIL(AIVar, ILPrim, TypeIL)

import qualified Data.Text as T

-- The reason we have both ILAllocate and ILAlloc is that
-- LLCodegen performs auto-loads from stack slots, which
-- means that a derived ILAlloc can't return a stack slot value!

data Letable =
          ILBool        Bool
        | ILText        T.Text
        | ILInt         TypeIL LiteralInt
        | ILFloat       TypeIL LiteralFloat
        | ILTuple       [AIVar]
        -- Struct member lookup
        | ILOccurrence  AIVar (Occurrence TypeIL)
        -- Varieties of applications
        | ILCallPrim    TypeIL ILPrim [AIVar]
        | ILCall        TypeIL AIVar  [AIVar]
        | ILAppCtor     TypeIL CtorId [AIVar]
        -- -- Stack/heap slot allocation
        -- | ILAllocate    (AllocInfo TypeIL)
        -- Mutable ref cells
        | ILAlloc       AIVar AllocMemRegion
        | ILDeref       AIVar
        | ILStore       AIVar AIVar
        -- Array operations
        | ILAllocArray  TypeIL AIVar
        | ILArrayRead   TypeIL (ArrayIndex AIVar)
        | ILArrayPoke          (ArrayIndex AIVar)  AIVar
        | ILTyApp       TypeIL AIVar TypeIL
        deriving (Show)
