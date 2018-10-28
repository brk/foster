{-# LANGUAGE BangPatterns #-}

module Main where

import Csiphash
import qualified Data.ByteString as BS
import Data.Bits(xor)

import Numeric(showHex)

import System.Environment(getArgs)

index_or []     _ d = d
index_or (v:_)  0 _ = v
index_or (_:xs) n d = index_or xs (n - 1) d

main = do
  args <- getArgs

  let
    srclen = read $ index_or args 0 "1"
    rounds = read $ index_or args 1 "10000"

    bytes = BS.pack [fromIntegral (i `mod` 255) | i <- [0..srclen]]
    key   = BS.pack $ map fromIntegral [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14 ,15 ]

    go !round !res =
     if round == rounds
      then return res
      else siphash24_IO bytes key res >>= go (round + 1)

  res <- go 0 0

  putStrLn $ showHex res ""

