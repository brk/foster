-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.TypecheckInt(typecheckInt, typecheckRat, sanityCheck) where

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T
import Data.Char(toLower)
import Data.Maybe(fromJust)
import qualified Data.List as List(elemIndex, reverse)
import qualified Data.Attoparsec.Text as Atto
import Data.Double.Conversion.Text

import Foster.Base
import Foster.Context
import Foster.AnnExpr
import Foster.TypeTC

typecheckInt :: ExprAnnot -> String -> Expected TypeTC -> Tc (AnnExpr RhoTC)
typecheckInt annot originalText expTy = do
    let goodBases = [2, 8, 10, 16]
    let maxBits = 64
    let (negated, clean, base) = extractCleanBase originalText
    sanityCheck (base `Prelude.elem` goodBases)
                ("Integer base must be one of " ++ show goodBases
                                    ++ "; was " ++ show base)
    sanityCheck (onlyValidDigitsIn clean base)
                ("Cleaned integer must contain only valid digits for base " ++ show base ++ ": " ++ clean)
    let int = precheckedLiteralInt originalText negated clean base
    let activeBits = litIntMinBits int
    sanityCheck (activeBits <= maxBits)
                ("Integer literals are currently limited to " ++ show maxBits ++ " bits, but "
                                  ++ clean ++ " requires " ++ show activeBits ++
                                  "\n" ++ highlightFirstLine (rangeOf annot))

    -- No need to unify with Infer here because tcRho does it for us.
    ty <- case expTy of
             Infer _ -> newTcUnificationVarTau $ "int-lit"
             Check t -> return t

    return (AnnLiteral annot ty (LitInt int))
 where
        onlyValidDigitsIn :: String -> Int -> Bool
        onlyValidDigitsIn str lim =
            let validIndex mi = Just True == fmap (< lim) mi in
            Prelude.all validIndex (map indexOf str)

        indexOf x = (toLower x) `List.elemIndex` "0123456789abcdef"

        -- Precondition: the provided string must be parseable in the given radix
        precheckedLiteralInt :: String -> Bool -> String -> Int -> LiteralInt
        precheckedLiteralInt originalText negated clean base =
            let nat = parseRadixRev (fromIntegral base) (List.reverse clean) in
            let integerValue = (if negated then -1 else 1) * nat in
            mkLiteralIntWithTextAndBase integerValue originalText base

        -- Precondition: string contains only valid hex digits.
        parseRadixRev :: Integer -> String -> Integer
        parseRadixRev _ ""     = 0
        parseRadixRev r (c:cs) = (fromIntegral $ fromJust (indexOf c))
                               + (r * parseRadixRev r cs)

-- Given "raw" integer text like "-0x123`456",
-- return (True, "123456", 16)
extractCleanBase :: String -> (Bool, String, Int)
extractCleanBase raw = do
  case getNeg raw of
    (neg, clean) ->
       case clean of
         ('0':'b':rest) -> (neg, rest , 2)
         ('0':'x':rest) -> (neg, rest , 16)
         _              -> (neg, clean, 10)
  where
    stripTicksAndPlus = Prelude.filter (\c -> c /= '`' && c /= '+')

    getNeg ('-':first) = (True,  stripTicksAndPlus first)
    getNeg ('+':first) = (False, stripTicksAndPlus first)
    getNeg (    first) = (False, stripTicksAndPlus first)

typecheckRat :: ExprAnnot -> String -> Maybe TypeTC -> Tc (AnnExpr RhoTC)
typecheckRat annot originalText _expTyTODO = do
  -- TODO: be more discriminating about float vs rational numbers?
  let (negated, cleanWithoutSign, _) = extractCleanBase originalText
  let clean = if negated then '-':cleanWithoutSign else cleanWithoutSign

  case Atto.parseOnly Atto.rational $ T.pack clean of
    Left err -> tcFails [text "Failed to parse rational:" <+> text clean
                        ,highlightFirstLineDoc (rangeOf annot)
                        ,text "Error was:"
                        ,indent 8 (text err) ]
    Right val -> do
      tcMaybeWarnMisleadingRat (rangeOf annot) clean val
      return (AnnLiteral annot (TyAppTC (TyConTC "Float64") [])
                         (LitFloat $ LiteralFloat val originalText))

tcMaybeWarnMisleadingRat range cleanText val = do
  -- It's possible that the literal given is "misleading",
  -- in the sense that it is neither the shortest string to
  -- uniquely identify a given floating point value, nor is
  -- it the most precise short-ish string.
  let isExpNot = isExponentialNotation cleanText
  let shortest = T.unpack $ toShortest val
  let canonicalS = addPointZeroIfNeeded shortest
  let canonicalP = T.unpack $
            if isExpNot
              then toExponential   (-1) val
              else toFixed shortestPrec val
                where Just shortestPrec =
                        List.elemIndex '.' (reverse canonicalS)

  let differingS = differingDigits cleanText canonicalS
  let differingP = differingDigits cleanText canonicalP
  let sameLength = length cleanText == length canonicalP

  case (differingS, differingP) of
    (0, _) -> return ()
    (_, 0) -> return ()
    _ | sameLength && isExpNot -> return ()
    _ -> do
      let alt = if canonicalS == canonicalP
                 then []
                 else [text "                 or, alternatively:   " <> text canonicalS]
      let description =
                if sameLength
                  then "is actually the floating point number "
                  else "could be written more compactly as    "

      tcWarn $ [text "the provided rational constant"
               ,highlightFirstLineDoc range
               ,text description <> text canonicalP
               ] ++ alt

isExponentialNotation s = loop s False
  where loop ('.':s) _ = loop s True
        loop ('e':_) True = True
        loop ('E':_) True = True
        loop (_:s) seenDot = loop s seenDot
        loop [] _ = False

addPointZeroIfNeeded s = if '.' `elem` s then s else s ++ ".0"

differingDigits s1 s2 = loop s1 s2 0
  where loop [] [] n = n
        loop (_:s1) [] n = loop s1 [] (n + 1)
        loop [] (_:s2) n = loop [] s2 (n + 1)
        loop (x:s1) (y:s2) n =
          if x == y then loop s1 s2 n
                    else loop s1 s2 (n + 1)
