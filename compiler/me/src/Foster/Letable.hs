module Foster.Letable where

import Foster.Base
import Foster.TypeIL

-- The reason we have both CFAllocate and CFAlloc is that
-- LLCodegen performs auto-loads from stack slots, which
-- means that a derived ILAlloc can't return a stack slot value!

data Letable =
          CFBool        Bool
        | CFInt         TypeIL LiteralInt
        | CFTuple       [AIVar]

        | CFCallPrim    TypeIL ILPrim [AIVar]
        | CFCall        TypeIL AIVar  [AIVar]
        | CFAppCtor     TypeIL CtorId [AIVar]
        -- Stack/heap slot allocation
        | CFAllocate    ILAllocInfo
        -- Mutable ref cells
        | CFAlloc       AIVar
        | CFDeref       AIVar
        | CFStore       AIVar AIVar
        -- Array operations
        | CFAllocArray  TypeIL AIVar
        | CFArrayRead   TypeIL AIVar  AIVar
        | CFArrayPoke          AIVar  AIVar  AIVar
        | CFTyApp       TypeIL AIVar TypeIL
        deriving (Show)

