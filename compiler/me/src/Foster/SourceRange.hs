
{-# LANGUAGE GADTs , StandaloneDeriving, BangPatterns, Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2020 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.SourceRange where

import Data.List as List(replicate)
import Data.Sequence as Seq(Seq, length, index, (><))
import qualified Data.Text as T

import Data.Text.Prettyprint.Doc
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Render.Terminal (AnsiStyle)

data SourceLines = SourceLines !(Seq T.Text)

-- Note: sourceRangeLines is *all* lines, not just those in the range.
data SourceRange = SourceRange { sourceRangeStartLine :: {-# UNPACK #-} !Int
                               , sourceRangeStartCol  :: {-# UNPACK #-} !Int
                               , sourceRangeEndLine   :: {-# UNPACK #-} !Int
                               , sourceRangeEndCol    :: {-# UNPACK #-} !Int
                               , sourceRangeLines :: !SourceLines
                               , sourceRangeFile  :: !(Maybe String)
                               }
                  | MissingSourceRange !String

instance Eq SourceRange where
  (MissingSourceRange s1) == (MissingSourceRange s2) = s1 == s2
  (SourceRange a b c d _ f1) == (SourceRange w x y z _ f2) = (a, b, c, d, f1) == (w, x, y, z, f2)
  _ == _ = False

class SourceRanged a
  where rangeOf :: a -> SourceRange

-- Used in ProtobufFE and Typecheck.hs.
rangeSpanOf :: SourceRanged a => SourceRange -> [a] -> SourceRange
rangeSpanOf defaultRange ranged =
    let ranges = map rangeOf ranged in
    rangeUnions defaultRange ranges

rangeUnions defaultRange allRanges = rsp defaultRange [r | r@(SourceRange _ _ _ _ _ _) <- allRanges]
  where rsp defaultRange [] = defaultRange
        rsp __ ranges@(b:_) = SourceRange (sourceRangeStartLine b)
                                          (sourceRangeStartCol  b)
                                          (sourceRangeEndLine $ last ranges)
                                          (sourceRangeEndCol  $ last ranges)
                                          (sourceRangeLines b)
                                          (sourceRangeFile  b)

appendSourceLines (SourceLines s1) (SourceLines s2) = SourceLines (s1 >< s2)

-- For (temporary) compatibility with ansi-wl-pprint
text :: String -> Doc AnsiStyle
text s = pretty s

sourceLineDoc :: SourceLines -> Int -> Doc AnsiStyle
sourceLineDoc (SourceLines seq) n = pretty $ sourceLineTxt (SourceLines seq) n

sourceLineStr :: SourceLines -> Int -> String
sourceLineStr (SourceLines seq) n =
    if n < 0 || Seq.length seq <= n
        then "<no line " ++ show n ++ " of "
                         ++ (show $ Seq.length seq) ++ ">"
        else (T.unpack $ Seq.index seq n)

sourceLineTxt :: SourceLines -> Int -> T.Text
sourceLineTxt (SourceLines seq) n =
    if n < 0 || Seq.length seq <= n
        then T.pack $ "<no line " ++ show n ++ " of "
                         ++ (show $ Seq.length seq) ++ ">"
        else Seq.index seq n

sourceLineNumbered :: SourceLines -> Int -> Doc AnsiStyle
sourceLineNumbered (SourceLines seq) n =
    fill 8 (pretty (n + 1) <> text ":") <> text (T.unpack $ Seq.index seq n)

lineNumberPadding = fill 8 PP.emptyDoc

prettyWithLineNumbers :: SourceRange -> Doc AnsiStyle
prettyWithLineNumbers (MissingSourceRange s) = text $ "<missing range: " ++ s ++ ">"
prettyWithLineNumbers (SourceRange bline bcol eline ecol lines _filepath) =
        line <> showSourceLinesNumbered bline bcol eline ecol lines <> line

showSourceRangeStr = show . showSourceRangeDoc

showSourceRangeDoc :: SourceRange -> Doc AnsiStyle
showSourceRangeDoc (MissingSourceRange s) = text "<missing range: " <> text s <> text ">"
showSourceRangeDoc (SourceRange bline bcol eline ecol lines _filepath) =
         line <> showSourceLinesDoc bline bcol eline ecol lines <> line

prettySourceRangeInfo :: SourceRange -> Doc AnsiStyle
prettySourceRangeInfo (MissingSourceRange s) = text $ "<missing range: " ++ s ++ ">"
prettySourceRangeInfo (SourceRange bline bcol _eline _ecol _lines mb_filepath) =
  let path = case mb_filepath of Nothing -> "<missing source file path>"
                                 Just fp -> fp in
  text path <> text ":" <> pretty (bline + 1) <> text ":" <> pretty bcol

highlightFirstLineDoc :: SourceRange -> Doc AnsiStyle
highlightFirstLineDoc (MissingSourceRange s) = text $ "<missing range: " ++ s ++ ">"
highlightFirstLineDoc (SourceRange bline bcol eline ecol lines _filepath) =
    line <> highlightLineDoc bline bcol fcol lines <> line
      where fcol  = if bline == eline then ecol else T.length lineb
            lineb = sourceLineTxt lines bline

highlightFirstLineStr :: SourceRange -> String
highlightFirstLineStr (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
highlightFirstLineStr (SourceRange bline bcol eline ecol lines _filepath) =
    "\n" ++ highlightLineStr bline bcol fcol lines ++ "\n"
      where fcol  = if lineb == linee then ecol else Prelude.length lineb
            lineb = sourceLineStr lines bline
            linee = sourceLineStr lines eline

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
highlightLineStr line bcol ecol lines = show $ highlightLineDoc line bcol ecol lines

highlightLineDoc line bcol ecol lines =
    vcat [pretty $ sourceLineTxt lines line, highlightLineRangeDoc bcol ecol]

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
showSourceLinesDoc bline bcol eline ecol lines =
    if bline == eline
        then vsep [sourceLineDoc lines bline, highlightLineRangeDoc bcol ecol]
        else vsep [sourceLineDoc lines n | n <- [bline..eline]]

showSourceLinesNumbered bline bcol eline ecol lines =
    if bline == eline
        then vsep [sourceLineNumbered lines bline
                  ,lineNumberPadding <> highlightLineRangeDoc bcol ecol]
        else vsep [sourceLineNumbered lines n | n <- [bline..eline]]

-- Generates a string of spaces and twiddles which underlines
-- a given range of characters.
highlightLineRangeStr :: Int -> Int -> String
highlightLineRangeStr bcol ecol =
    let len = ecol - bcol in
    if len <= 0
        then ""
        else (List.replicate bcol ' ') ++ (List.replicate len '~')

highlightLineRangeDoc :: Int -> Int -> Doc AnsiStyle
highlightLineRangeDoc bcol ecol =
    let len = ecol - bcol in
    if len <= 0
        then PP.emptyDoc
        else text (List.replicate bcol ' ') <> text (List.replicate len '~')

reprSourceRange (MissingSourceRange s) = text "(MissingSourceRange " <> text s <> text ")"
reprSourceRange (SourceRange bline bcol eline ecol _lines _filepath) =
  parens (text "SourceRange" <+> pretty bline <+> pretty bcol <+> pretty eline
                             <+> pretty ecol <+> pretty _filepath)