-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.TypecheckInt(typecheckInt, typecheckRat, sanityCheck) where

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T
import qualified Data.Bits as Bits(shiftR)
import Data.Char(toLower)
import Data.Maybe(fromJust)
import qualified Data.List as List(length, elemIndex, reverse)

import Foster.Base
import Foster.Context
import Foster.AnnExpr
import Foster.TypeAST

typecheckInt :: ExprAnnot -> String -> Expected TypeAST -> Tc (AnnExpr Rho)
typecheckInt annot originalText expTy = do
    let goodBases = [2, 8, 10, 16]
    let maxBits = 64
    (negated, clean, base) <- extractCleanBase originalText
    sanityCheck (base `Prelude.elem` goodBases)
                ("Integer base must be one of " ++ show goodBases
                                    ++ "; was " ++ show base)
    sanityCheck (onlyValidDigitsIn clean base)
                ("Cleaned integer must contain only hex digits: " ++ clean)
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
            let activeBits =
                 if integerValue == -2147483648 then 32 -- handle edge cases directly
                   else if integerValue == -9223372036854775808 then 64
                     else List.length (bitStringOf nat)
                                                 + (if negated then 1 else 0) in
            LiteralInt integerValue activeBits originalText base

        -- Precondition: string contains only valid hex digits.
        parseRadixRev :: Integer -> String -> Integer
        parseRadixRev _ ""     = 0
        parseRadixRev r (c:cs) = (fromIntegral $ fromJust (indexOf c))
                               + (r * parseRadixRev r cs)

        -- | Example: bitStringOf 21 == "10101"
        bitStringOf = List.reverse . reverseBitStringOf where
            reverseBitStringOf n
                | n <  0    = error "bitStringOf: non-negative number!"
                | n <= 1    = show n
                | otherwise = lowBitOf n ++ reverseBitStringOf (Bits.shiftR n 1)
                        where lowBitOf n = if even n then "1" else "0"

typecheckRat :: ExprAnnot -> String -> Maybe TypeAST -> Tc (AnnExpr Rho)
typecheckRat annot originalText _expTyTODO = do
  --tcLift $ putStrLn $ "typecheckRat: " ++ originalText ++ " :?: " ++ show _expTyTODO
  -- TODO: be more discriminating about float vs rational numbers?
  let val = (read originalText) :: Double
  return (AnnLiteral annot PrimFloat64AST (LitFloat $ LiteralFloat val originalText))

