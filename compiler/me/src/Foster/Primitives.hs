-----------------------------------------------------------------------------
-- Copyright (c) 2012 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Primitives where

import Foster.Base
import Foster.ParsedType

import qualified Data.Text as T

primitiveDataTypesP :: [DataType TypeP]
primitiveDataTypesP = [
  (DataType "Text" [] $
        [DataCtor (T.pack "TextFragment") 0 [ArrayTypeP (PrimIntP I8)
                                            ,PrimIntP I32]
        ,DataCtor (T.pack "TextConcat"  ) 1 [TyConAppP "Text" []
                                            ,TyConAppP "Text" []
                                            ,PrimIntP I32]])
  ]

