module Foster.Letable where

import Foster.Base
import Foster.TypeIL

-- The reason we have both CFAllocate and CFAlloc is that
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

