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

typ nm = TyAppP (TyConP nm) []

primitiveDataTypesP :: [DataType TypeP]
primitiveDataTypesP = [
  (let tf = [] in
   DataType (TypeFormal "Text" (MissingSourceRange "Text") KindPointerSized) tf
        [DataCtor (T.pack "TextFragment") tf
            [TyAppP (TyConP "Array") [typ "Int8"]
            , typ "Int32"]
            (Just (CR_Default 0))
            (MissingSourceRange "Text.TextFragment")
        ,DataCtor (T.pack "TextConcat"  ) tf
            [typ "Text"
            ,typ "Text"
            ,typ "Int32"]
            (Just (CR_Default 1))
            (MissingSourceRange "Text.TextConcat")]
        (MissingSourceRange "Text")),

  (let tf = [TypeFormal "o"    (MissingSourceRange "Coro.o") KindAnySizeType,
             TypeFormal "i"    (MissingSourceRange "Coro.i") KindAnySizeType] in
   DataType (TypeFormal "Coro" (MissingSourceRange "Coro")   KindPointerSized) tf
        []
        (MissingSourceRange "Coro"))
  ]

