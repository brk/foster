-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Output where

import Text.PrettyPrint.ANSI.Leijen

-- Either, with better names for the cases...
data OutputOr expr
    = OK      expr
    | Errors [Doc]

putDocLn d = do putDoc d ; putDoc line

outLn s = text s <> line

