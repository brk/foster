-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MonoType where

import Text.PrettyPrint.ANSI.Leijen

import Foster.Base
import Foster.KNUtil

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
         | RefinedType   (TypedId MonoType) KNMono [Ident]
         deriving (Show, Eq)

instance Eq KNMono where e1 == e2 = show e1 == show e2

instance IntSizedBits MonoType where
        intSizeBitsOf (PrimInt isb) = isb
        intSizeBitsOf (RefinedType v _ _) = intSizeBitsOf (tidType v)
        intSizeBitsOf _ = error $ "Unable to compute IntSizedBits for non-PrimInt type"

extractFnType (FnType _ _ cc pf) = (cc, pf)
extractFnType (PtrType (StructType ((FnType _ _ cc FT_Proc):_))) = (cc, FT_Func)

extractFnType other = error $ "Unable to extract fn type from " ++ show other

boolMonoType = PrimInt I1

type MoVar = TypedId MonoType
type MoPrim = FosterPrim MonoType

data MoExternDecl = MoExternDecl String MonoType deriving (Show)

instance Pretty MonoType where
  pretty t = case t of
          PrimInt        isb          -> pretty isb
          PrimFloat64                 -> text "Float64"
          TyConApp       dt ts        -> text "(" <> pretty dt <+> tupled (map pretty ts) <> text "]"
          TupleType      ts           -> tupled (map pretty ts)
          StructType     ts           -> text "#" <> tupled (map pretty ts)
          FnType         ts r _cc _pf -> text "{" <+> hsep [pretty t <+> text "=>" | t <- ts]
                                                  <+> pretty r <+> text "}"
          CoroType      _s _r         -> text "Coro..."
          ArrayType      t            -> text "Array" <+> pretty t
          PtrType        t            -> text "Ref" <+> pretty t
          PtrTypeUnknown              -> text "?"
          RefinedType v e args        -> parens (text "%" <+> pretty v <+> text ":" <+> pretty e <+> text "/" <+> pretty args)

type FnMono   = Fn RecStatus KNMono MonoType
type KNMono     = KNExpr' RecStatus MonoType

renderKNM :: (ModuleIL (KNMono) MonoType) -> String
renderKNM m = show (pretty m)

renderKNFM :: FnMono -> String
renderKNFM m = show (pretty m)

