-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Output where

import Text.PrettyPrint.ANSI.Leijen
import System.IO(stdout)

-- Either, with better names for the cases...
data OutputOr expr
    = OK      expr
    | Errors [Doc]

putDocLn d = do putDocP d ; putDocP line

-- Re-implement putDoc because the defaults behind it aren't what
-- we want (it doesn't help that the documentation about it lies...).
putDocP doc = displayIO stdout (renderPretty 0.8 80 doc)

outLn s = text s <> line

