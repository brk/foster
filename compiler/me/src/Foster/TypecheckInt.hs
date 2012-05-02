-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------
module Foster.TypecheckInt(typecheckInt, typecheckRat, sanityCheck) where

import System.Console.ANSI(Color(Red))
import qualified Data.Text as T
import qualified Data.Bits as Bits(shiftR)
import Data.Char(toLower)
import Data.Maybe(fromJust)
import qualified Data.List as List(length, elemIndex, reverse)

import Foster.Base
import Foster.Context
import Foster.AnnExpr
import Foster.TypeAST
import Foster.Output(outCSLn, outLn)

sanityCheck :: Bool -> String -> Tc ()
sanityCheck cond msg = if cond then return () else tcFails [outCSLn Red msg]

typecheckInt :: SourceRange -> String -> Maybe TypeAST -> Tc (AnnExpr Rho)
typecheckInt rng originalText _expTyTODO = do
    let goodBases = [2, 8, 10, 16]
    let maxBits = 32
    (clean, base) <- extractCleanBase originalText
    sanityCheck (base `Prelude.elem` goodBases)
                ("Integer base must be one of " ++ show goodBases
                                    ++ "; was " ++ show base)
    sanityCheck (onlyValidDigitsIn clean base)
                ("Cleaned integer must contain only hex digits: " ++ clean)
    let int = precheckedLiteralInt originalText maxBits clean base
    let activeBits = litIntMinBits int
    sanityCheck (activeBits <= maxBits)
                ("Integers currently limited to " ++ show maxBits ++ " bits, "
                                  ++ clean ++ " requires " ++ show activeBits)
    return (AnnInt rng (PrimIntAST $ sizeOfBits maxBits) int)
 where
        onlyValidDigitsIn :: String -> Int -> Bool
        onlyValidDigitsIn str lim =
            let validIndex mi = Just True == fmap (< lim) mi in
            Prelude.all validIndex (map indexOf str)

        indexOf x = (toLower x) `List.elemIndex` "0123456789abcdef"

        -- Given "raw" integer text like "123`456_10",
        -- return ("123456", 10)
        extractCleanBase :: String -> Tc (String, Int)
        extractCleanBase text = do
            let noticks = Prelude.filter (/= '`') text
            case splitString "_" noticks of
                [first, base] -> return (first, read base)
                [first]       -> return (first, 10)
                _otherwise    -> tcFails
                   [outLn $ "Unable to parse integer literal " ++ text]

        splitString :: String -> String -> [String]
        splitString needle haystack =
            map T.unpack $ T.splitOn (T.pack needle) (T.pack haystack)

        -- Precondition: the provided string must be parseable in the given radix
        precheckedLiteralInt :: String -> Int -> String -> Int -> LiteralInt
        precheckedLiteralInt originalText _maxBits clean base =
            let integerValue = parseRadixRev (fromIntegral base) (List.reverse clean) in
            let activeBits = List.length (bitStringOf integerValue) in
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

        sizeOfBits :: Int -> IntSizeBits
        sizeOfBits 32 = I32
        sizeOfBits n = error $ "TypecheckInt.hs:sizeOfBits: Only support i32 for now, not " ++ show n

typecheckRat :: SourceRange -> String -> Maybe TypeAST -> Tc (AnnExpr Rho)
typecheckRat rng originalText _expTyTODO = do
  --tcLift $ putStrLn $ "typecheckRat: " ++ originalText ++ " :?: " ++ show _expTyTODO
  -- TODO: be more discriminating about float vs rational numbers?
  let val = (read originalText) :: Double
  return (AnnFloat rng PrimFloat64 (LiteralFloat val originalText))

