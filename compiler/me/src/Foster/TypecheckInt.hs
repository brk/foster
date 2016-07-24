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
    (negated, clean, base) <- extractCleanBase originalText
    sanityCheck (base `Prelude.elem` goodBases)
                ("Integer base must be one of " ++ show goodBases
                                    ++ "; was " ++ show base)
    sanityCheck (onlyValidDigitsIn clean base)
                ("Cleaned integer must contain only valid digits for base " ++ show base ++ ": " ++ clean)
    let int = precheckedLiteralInt originalText negated clean base
    let activeBits = litIntMinBits int
    sanityCheck (activeBits <= maxBits)
                ("Integers currently limited to " ++ show maxBits ++ " bits, "
                                  ++ clean ++ " requires " ++ show activeBits)

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

        -- Given "raw" integer text like "-123`456_10",
        -- return (True, "123456", 10)
        extractCleanBase :: String -> Tc (Bool, String, Int)
        extractCleanBase raw = do
            let getNeg ('-':first, base) = (True,  first, base)
                getNeg (    first, base) = (False, first, base)

                noticks = Prelude.filter (/= '`') raw

            case splitString "_" noticks of
                [first, base] -> return $ getNeg (first, read base)
                [first]       -> return $ getNeg (first, 10)
                _otherwise    -> tcFails
                   [text "Unable to parse integer literal" <+> text raw]

        splitString :: String -> String -> [String]
        splitString needle haystack =
            map T.unpack $ T.splitOn (T.pack needle) (T.pack haystack)

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

typecheckRat :: ExprAnnot -> String -> Maybe TypeTC -> Tc (AnnExpr RhoTC)
typecheckRat annot originalText _expTyTODO = do
  -- TODO: be more discriminating about float vs rational numbers?

  case Atto.parseOnly Atto.rational $ T.pack originalText of
    Left err -> tcFails [text "Failed to parse rational:" <+> text originalText
                        ,text "Error was:"
                        ,indent 8 (text err) ]
    Right val -> do
      -- It's possible that the literal given is "misleading",
      -- in the sense that it is neither the shortest string to
      -- uniquely identify a given floating point value, nor is
      -- it the most precise short-ish string.
      let shortest = T.unpack $ toShortest val
      let canonicalS = addPointZeroIfNeeded shortest
      let Just shortestPrec = List.elemIndex '.' (reverse canonicalS)
      let canonicalP = T.unpack $ toFixed shortestPrec val
      let differingS = differingDigits originalText canonicalS
      let differingP = differingDigits originalText canonicalP

      case (differingS, differingP) of
        (0, _) -> return ()
        (_, 0) -> return ()
        _ -> tcWarnMisleadingRat (rangeOf annot) canonicalS canonicalP

      return (AnnLiteral annot (TyAppTC (TyConTC "Float64") [])
                         (LitFloat $ LiteralFloat val originalText))

tcWarnMisleadingRat range canonicalS canonicalP = do
  let alt = if canonicalS == canonicalP
             then []
             else [text "                 or, alternatively:   " <> text canonicalS]
  tcWarn $ [text "the provided rational constant"
           ,highlightFirstLineDoc range
           ,text "is actually the floating point number " <> text canonicalP
           ] ++ alt

addPointZeroIfNeeded s = if '.' `elem` s then s else s ++ ".0"

differingDigits s1 s2 = loop s1 s2 0
  where loop [] [] n = n
        loop (_:s1) [] n = loop s1 [] (n + 1)
        loop [] (_:s2) n = loop [] s2 (n + 1)
        loop (x:s1) (y:s2) n =
          if x == y then loop s1 s2 n
                    else loop s1 s2 (n + 1)
