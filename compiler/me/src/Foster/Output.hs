-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Output where

import Prettyprinter
import Prettyprinter.Render.Terminal (renderIO, AnsiStyle)
import Prettyprinter.Render.String (renderString)

import System.IO (stdout)

-- Either, with better names for the cases...
data OutputOr expr
    = OK      expr
    | Errors [Doc AnsiStyle]

putDocLn :: Doc AnsiStyle -> IO ()
putDocLn d = do putDocP d ; putDocP line

putDocP :: Doc AnsiStyle -> IO ()
putDocP doc = renderIO stdout (layoutPretty defaultLayoutOptions doc)

outLn :: String -> Doc AnsiStyle
outLn s = pretty s <> line

strDocRaw :: Doc AnsiStyle -> String
strDocRaw doc = renderString $ layoutPretty (LayoutOptions Unbounded) doc