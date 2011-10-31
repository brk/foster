-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Letable (Letable(..)) where

import Foster.Base(LiteralInt, CtorId)
import Foster.TypeIL(AIVar, ILPrim, ILAllocInfo, TypeIL)

-- The reason we have both ILAllocate and ILAlloc is that
-- LLCodegen performs auto-loads from stack slots, which
-- means that a derived ILAlloc can't return a stack slot value!

data Letable =
          ILBool        Bool
        | ILInt         TypeIL LiteralInt
        | ILTuple       [AIVar]

        | ILCallPrim    TypeIL ILPrim [AIVar]
        | ILCall        TypeIL AIVar  [AIVar]
        | ILAppCtor     TypeIL CtorId [AIVar]
        -- Stack/heap slot allocation
        | ILAllocate    ILAllocInfo
        -- Mutable ref cells
        | ILAlloc       AIVar
        | ILDeref       AIVar
        | ILStore       AIVar AIVar
        -- Array operations
        | ILAllocArray  TypeIL AIVar
        | ILArrayRead   TypeIL AIVar  AIVar
        | ILArrayPoke          AIVar  AIVar  AIVar
        | ILTyApp       TypeIL AIVar TypeIL
        deriving (Show)