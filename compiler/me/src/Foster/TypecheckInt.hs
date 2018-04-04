-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.TypecheckInt(typecheckInt, typecheckRat,
      tryParseInt, ParseIntResult(..), sanityCheck) where

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T
import Data.Char(toLower)
import Data.Maybe(fromJust)
import qualified Data.List as List(elemIndex, reverse, break)
import qualified Data.Attoparsec.Text as Atto
import Data.Double.Conversion.Text

import Foster.Base
import Foster.Context
import Foster.AnnExpr
import Foster.TypeTC
import Foster.Infer(tcUnifyTypes)

data PIR_FailureCase = PIR_InvalidDigit
                     | PIR_NeedsTooManyBits

data ParseIntResult = PIR_Success LiteralInt
                    | PIR_Failure PIR_FailureCase String

tryParseInt :: SourceRange -> String -> ParseIntResult
tryParseInt rng originalText =
    let maxBits = 64 in
    let (negated, (clean {-without sign-}, expt, _cleanWithExpt), base) = extractCleanBase originalText in
    case () of
      _ | not (onlyValidDigitsIn clean base) -> PIR_Failure PIR_InvalidDigit $
                ("Cleaned integer must contain only valid digits for base " ++ show base ++ ": " ++ clean)
      _ ->
        let int = precheckedLiteralInt originalText negated clean expt base in
        let activeBits = litIntMinBits int in
        if  activeBits <= maxBits
          then PIR_Success int
          else PIR_Failure PIR_NeedsTooManyBits $
                ("Integer literals are currently limited to " ++ show maxBits ++ " bits, but "
                                  ++ clean ++ " requires " ++ show activeBits ++
                                  "\n" ++ highlightFirstLine rng)
 where
        onlyValidDigitsIn :: String -> Int -> Bool
        onlyValidDigitsIn str lim =
            let validIndex mi = Just True == fmap (< lim) mi in
            Prelude.all validIndex (map indexOf str)

        indexOf x = (toLower x) `List.elemIndex` "0123456789abcdef"

        -- Precondition: the provided string must be parseable in the given radix
        precheckedLiteralInt :: String -> Bool -> String -> Int -> Int -> LiteralInt
        precheckedLiteralInt originalText negated clean expt base =
            let nat0 = parseRadixRev (fromIntegral base) (List.reverse clean)
                nat  = if expt < 0 then error "tryParseInt can't handle negative exponent!"
                         else  nat0 * (10 ^ expt)
                integerValue = (if negated then -1 else 1) * nat in
            mkLiteralIntWithTextAndBase integerValue originalText base

        -- Precondition: string contains only valid hex digits.
        parseRadixRev :: Integer -> String -> Integer
        parseRadixRev _ ""     = 0
        parseRadixRev r (c:cs) = (fromIntegral $ fromJust (indexOf c))
                               + (r * parseRadixRev r cs)

applyExpt val0 expt = if expt >= 0 then val0 * (10 ^ expt)
                                   else val0 / (10 ^ (-expt))

-- Given "raw" integer text like "-0x123`456",
-- return (True, "123456", 16)
extractCleanBase :: String -> (Bool, (String, Int, String), Int)
extractCleanBase raw = do
  case getNeg raw of
    (neg, clean) ->
       case clean of
         ('0':'b':rest) -> (neg,  (rest, 0, rest) , 2)
         ('0':'x':rest) -> (neg,  (rest, 0, rest) , 16)
         _              -> (neg, parseIntExp clean, 10)
  where
    stripTicksAndPlus = Prelude.filter (\c -> c /= '`' && c /= '+')

    getNeg ('-':first) = (True,  stripTicksAndPlus first)
    getNeg ('+':first) = (False, stripTicksAndPlus first)
    getNeg (    first) = (False, stripTicksAndPlus first)

    parseIntExp clean =
      case List.break (\c -> c `elem` ['e', 'E']) clean of
        (_,       [])         -> (clean,   0, clean)
        (beforeE, (_:afterE)) -> (beforeE, evalNeg $ getNeg afterE, clean)

    evalNeg :: (Bool, String) -> Int
    evalNeg (n, digits) = (if n then -1 else 1) * (read digits)

typecheckInt :: ExprAnnot -> String -> Expected TypeTC -> Tc (AnnExpr RhoTC)
typecheckInt annot originalText expTy = do
  case tryParseInt (rangeOf annot) originalText of
    PIR_Failure _ msg -> tcFails [red (text msg)]
    PIR_Success int -> do
      -- No need to unify with Infer here because tcRho does it for us.
      ty <- case expTy of
               Infer _ -> newTcUnificationVarTau $ "int-lit"
               Check t -> return t

      return (AnnLiteral annot ty (LitInt int))

exptTooLargeForType expt (TyAppTC (TyConTC "Float32") []) = expt >= 39
exptTooLargeForType expt _ty = expt >= 309

typecheckRat :: ExprAnnot -> String -> Maybe TypeTC -> Tc (AnnExpr RhoTC)
typecheckRat annot originalText expTy = do
  -- TODO: be more discriminating about float vs rational numbers?
  let (negated, (cleanWithoutSign, expt, cleanEWithoutSign), base) = extractCleanBase originalText
  let clean  = if negated then '-':cleanWithoutSign else cleanWithoutSign
  let cleanE = if negated then '-':cleanEWithoutSign else cleanEWithoutSign
  let float64 = TyAppTC (TyConTC "Float64") []
  ty <- case expTy of
            Nothing -> return $ float64
            Just t@(TyAppTC (TyConTC f) []) | f `elem` ["Float32", "Float64"]
                   -> return t
            Just t@(MetaTyVarTC _) -> do tcUnifyTypes t float64 ; return float64
            Just t -> tcFails [text "Unable to give rational number",
                               highlightFirstLineDoc (rangeOf annot),
                               text "the type" <+> pretty t]
  case base of
    2  -> error $ "binary float literals not yet implemented"
    16 -> error $ "hex floating point literals not yet implemented"
    10 ->
      if exptTooLargeForType expt ty then
         tcFails [text "Exponent too large", highlightFirstLineDoc (rangeOf annot)]
       else
        case Atto.parseOnly Atto.double $ T.pack clean of
          Left err -> tcFails [text "Failed to parse rational portion" <+> parens (text clean)
                              ,highlightFirstLineDoc (rangeOf annot)
                              ,text "Error was:"
                              ,indent 8 (text err) ]
          Right val0 -> do
            let val = applyExpt val0 expt
            tcMaybeWarnMisleadingRat (rangeOf annot) cleanE val
            return (AnnLiteral annot ty (LitFloat $ LiteralFloat val originalText))
    _ -> error $ "Unexpected rational literal base " ++ show base

tcMaybeWarnMisleadingRat range cleanText val = do
  -- It's possible that the literal given is "misleading",
  -- in the sense that it is neither the shortest string to
  -- uniquely identify a given floating point value, nor is
  -- it the most precise short-ish string.
  let isExpNot = isExponentialNotation cleanText
  let shortest = T.unpack $ toShortest val
  let canonicalS = addPointZeroIfNeeded shortest
  let canonicalE = T.unpack $ toExponential   (-1) val
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
      let alt1 = if canonicalS == canonicalP
                  then []
                  else [text "                   or, alternatively: " <> text canonicalS]
      let alt2 = if (length canonicalE + 5) > length canonicalP
                  then []
                  else [text "         or, in exponential notation: " <> text canonicalE]
      let description =
                if length cleanText <= length canonicalP
                  then "is actually the floating point number "
                  else "could be written more compactly as    "

      tcWarn $ [text "the provided rational constant"
               ,highlightFirstLineDoc range
               ,text description <> text canonicalP
               ] ++ alt1 ++ alt2

isExponentialNotation s = loop s
  where loop ('e':_) = True
        loop ('E':_) = True
        loop (_:s) = loop s
        loop [] = False

addPointZeroIfNeeded s = if '.' `elem` s then s else s ++ ".0"

differingDigits s1 s2 = loop s1 s2 0
  where loop [] [] n = n
        loop (_:s1) [] n = loop s1 [] (n + 1)
        loop [] (_:s2) n = loop [] s2 (n + 1)
        loop (x:s1) (y:s2) n =
          if x == y then loop s1 s2 n
                    else loop s1 s2 (n + 1)
