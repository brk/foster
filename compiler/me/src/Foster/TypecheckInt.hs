-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.TypecheckInt(typecheckInt, typecheckRat,
      tryParseInt, sanityCheck) where

import Data.Text.Prettyprint.Doc
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
import Foster.SourceRange(SourceRange, highlightFirstLineStr, highlightFirstLineDoc, rangeOf)

tryParseInt :: SourceRange -> T.Text -> Either String LiteralInt
tryParseInt rng originalText =
    let originalString = T.unpack originalText
        (negated, (clean {-without sign-}, expt, _cleanWithExpt), base) = extractCleanBase originalString in
    case () of
      _ | not (onlyValidDigitsIn clean base) -> Left $
                ("Cleaned integer must contain only valid digits for base " ++ show base ++ ": " ++ clean
                 ++ "\n" ++ highlightFirstLineStr rng)
      _ -> Right $ precheckedLiteralInt originalText negated clean expt base
 where
        onlyValidDigitsIn :: String -> Int -> Bool
        onlyValidDigitsIn str lim =
            let validIndex mi = Just True == fmap (< lim) mi in
            Prelude.all validIndex (map indexOf str)

        indexOf x = (toLower x) `List.elemIndex` "0123456789abcdef"

        -- Precondition: the provided string must be parseable in the given radix
        precheckedLiteralInt :: T.Text -> Bool -> String -> Int -> Int -> LiteralInt
        precheckedLiteralInt originalText negated clean expt base =
            let nat0 = parseRadixRev (fromIntegral base) (List.reverse clean)
                nat  = if expt < 0 then error "tryParseInt can't handle negative exponent!"
                         else  nat0 * (10 ^ expt)
                integerValue = (if negated then -1 else 1) * nat in
            mkLiteralIntWithText integerValue originalText

        -- Precondition: string contains only valid hex digits.
        parseRadixRev :: Integer -> String -> Integer
        parseRadixRev _ ""     = 0
        parseRadixRev r (c:cs) = (fromIntegral $ fromJust (indexOf c))
                               + (r * parseRadixRev r cs)

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

typecheckInt :: ExprAnnot -> T.Text -> Expected TypeTC -> Tc (AnnExpr RhoTC)
typecheckInt annot originalText expTy = do
  case tryParseInt (rangeOf annot) originalText of
    Left  msg -> tcFails [red (string msg)]
    Right int -> do
      -- No need to unify with Infer here because tcRho does it for us.
      ty <- case expTy of
               Infer _ -> newTcUnificationVarTau $ "int-lit"
               Check t -> return t

      return (AnnLiteral annot ty (LitInt int))

exptTooLargeForType expt (TyAppTC (TyConTC "Float32") []) = expt >= 39
exptTooLargeForType expt _ty = expt >= 309

typecheckRat :: ExprAnnot -> T.Text -> Maybe TypeTC -> Tc (AnnExpr RhoTC)
typecheckRat annot originalText expTy = do
  -- TODO: be more discriminating about float vs rational numbers?
  let originalString = T.unpack originalText 
      (negated, (cleanWithoutSignStr, expt, cleanEWithoutSignStr), base) = extractCleanBase originalString
      cleanWithoutSign  = T.pack cleanWithoutSignStr
      cleanEWithoutSign = T.pack cleanEWithoutSignStr
      cleanWithSign  = if negated then "-" `T.append` cleanWithoutSign  else cleanWithoutSign
      cleanEWithSign = if negated then "-" `T.append` cleanEWithoutSign else cleanEWithoutSign
      float64 = TyAppTC (TyConTC "Float64") []
  ty <- case expTy of
            Nothing -> return $ float64
            Just t@(TyAppTC (TyConTC f) []) | f `elem` ["Float32", "Float64"]
                   -> return t
            Just t@(MetaTyVarTC m) -> do tcAddConstraint (TcC_IsFloat m) (rangeOf annot)
                                         return t
            Just t -> tcFails [text "Unable to give rational number",
                               highlightFirstLineDoc (rangeOf annot),
                               text "the type" <+> prettyT t]
  case base of
    2  -> error $ "binary float literals not yet implemented"
    16 ->
      if exptTooLargeForType expt ty then
        tcFails [text "Exponent too large", highlightFirstLineDoc (rangeOf annot)]
      else do
       case Atto.parseOnly (hexDoubleParser <* Atto.endOfInput) $ cleanWithoutSign of
         Left err -> tcFails [text "Failed to parse hex float literal " <+> parens (text cleanWithSign)
                             ,highlightFirstLineDoc (rangeOf annot)
                             ,text "Error was:"
                             ,indent 8 (string err) ]
         Right (part1,part2,mantissaText,denom,part3) -> do
           if denom > (16.0 ** 14)
             then
               tcFails [text "Oversized mantissa in hex float literal; had"
                        <+> pretty (T.length mantissaText) <+> text "hex digits"
                        <+> text "but a 64-bit mantissa can only fit 14 hex digits (52 bits)."
                        ,highlightFirstLineDoc (rangeOf annot)]
             else do
               let pos = (fromInteger part1 +
                           (fromInteger part2 / denom)) * (encodeFloat 2 (part3 - 1))
                   val = if negated then -1.0 * pos else pos
               return (AnnLiteral annot ty (LitFloat $ LiteralFloat val originalText))
    10 ->
      if exptTooLargeForType expt ty then
         tcFails [text "Exponent too large", highlightFirstLineDoc (rangeOf annot)]
       else
        -- We rely on Attoparsec to reconstruct the proper Double value here
        -- because the straightforward DIY approach of just parsing the clean part
        -- and multiplying by ``10 ** expt`` does not produce bit-precise results.
        -- For example, ``3e50 == (3.0 * (10 ** 50))`` is ``False``!
        -- Also, we negate separately because Atto.double returns 0.0 for "-0.0".
        case Atto.parseOnly Atto.double $ T.pack (T.unpack cleanWithoutSign ++ "e" ++ show expt) of
          Left err -> tcFails [text "Failed to parse rational " <+> parens (text cleanWithSign <> text "e" <> pretty expt)
                              ,highlightFirstLineDoc (rangeOf annot)
                              ,text "Error was:"
                              ,indent 8 (string err) ]
          Right pos -> do
            let val = if negated then -1.0 * pos else pos
            tcMaybeWarnMisleadingRat (rangeOf annot) cleanEWithSign val
            return (AnnLiteral annot ty (LitFloat $ LiteralFloat val originalText))
    _ -> error $ "Unexpected rational literal base " ++ show base

hexDoubleParser :: Atto.Parser (Integer, Integer, T.Text, Double, Int)
hexDoubleParser = do
  part1 <- Atto.hexadecimal
  (t, part2) <- Atto.option (T.pack "", 0)
                  (Atto.char '.' *> Atto.match Atto.hexadecimal)
  part3 <- (Atto.asciiCI (T.pack "p") *> Atto.signed Atto.decimal)
  return (part1, part2, t, 16.0 ** (fromIntegral $ T.length t), part3)

tcMaybeWarnMisleadingRat :: SourceRange -> T.Text -> Double -> Tc ()
tcMaybeWarnMisleadingRat range cleanText val = do
  -- It's possible that the literal given is "misleading",
  -- in the sense that it is neither the shortest string to
  -- uniquely identify a given floating point value, nor is
  -- it the most precise short-ish string.
  let isExpNot = isExponentialNotation (T.unpack cleanText)
  let shortest = T.unpack $ toShortest val
  let canonicalS = T.pack $ addPointZeroIfNeeded shortest
  let canonicalE = toExponential   (-1) val
  let canonicalP =
            if isExpNot
              then toExponential   (-1) val
              else toFixed shortestPrec val
                where Just shortestPrec =
                        T.findIndex (== '.') (T.reverse canonicalS)

  let differingS = differingDigitsT cleanText canonicalS
  let differingP = differingDigitsT cleanText canonicalP
  let sameLength = T.length cleanText == T.length canonicalP

  case (differingS, differingP) of
    (0, _) -> return ()
    (_, 0) -> return ()
    _ | sameLength && isExpNot -> return ()
    _ -> do
      let alt1 = if canonicalS == canonicalP
                  then []
                  else [text "                   or, alternatively: " <> text canonicalS]
      let alt2 = if (T.length canonicalE + 5) > T.length canonicalP
                  then []
                  else [text "         or, in exponential notation: " <> text canonicalE]
      let description =
                if T.length cleanText <= T.length canonicalP
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

differingDigitsT t1 t2 = differingDigits (T.unpack t1) (T.unpack t2)
differingDigits s1 s2 = loop s1 s2 0
  where loop [] [] n = n
        loop (_:s1) [] n = loop s1 [] (n + 1)
        loop [] (_:s2) n = loop [] s2 (n + 1)
        loop (x:s1) (y:s2) n =
          if x == y then loop s1 s2 n
                    else loop s1 s2 (n + 1)
