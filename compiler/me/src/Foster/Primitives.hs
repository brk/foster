-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Primitives where

import Foster.Base
import Foster.Kind
import Foster.ParsedType

import qualified Data.Text as T

primitiveDataTypesP :: [DataType TypeP]
primitiveDataTypesP = [
  (let tf = [] in
   DataType (TypeFormal "Text" KindPointerSized) tf
        [DataCtor (T.pack "TextFragment") tf -- CR_Default 0
            [ArrayTypeP (PrimIntP I8)
            ,PrimIntP I32]
            (MissingSourceRange "Text.TextFragment")
        ,DataCtor (T.pack "TextConcat"  ) tf -- CR_Default 1
            [TyConAppP "Text" []
            ,TyConAppP "Text" []
            ,PrimIntP I32]
            (MissingSourceRange "Text.TextConcat")]
        (MissingSourceRange "Text")),

  (let tf = [TypeFormal "o" KindAnySizeType,
             TypeFormal "i" KindAnySizeType] in
   DataType (TypeFormal "Coro" KindPointerSized) tf
        []
        (MissingSourceRange "Coro"))
  ]

