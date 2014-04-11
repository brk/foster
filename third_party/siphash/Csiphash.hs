{-# LANGUAGE BangPatterns #-}

module Csiphash(siphash24_IO) where

import qualified Data.ByteString as BS
import Data.ByteString(ByteString)
import Data.Bits
import Data.Word

{-
 - Port of csiphash.c, via Foster...
 -
 - Unfortunately, the performance is atrocious (~40x the C code)
 - because Word64 is boxed, so the program ends up allocating and GC'ing
 - roughly 1 GB per 100k iterations.
 -
 - GHC provides an unboxed Word64# type, but its operations are all
 - implemented as external C calls (!)...
 -}

mergeInt32 :: Word32 -> Word32 -> Word64
mergeInt32 hi lo = ((fromIntegral hi) `shiftL` 32) .|. fromIntegral lo

octet4ToWord32 :: Word8 -> Word8 -> Word8 -> Word8 -> Word32
octet4ToWord32 hi m1 m2 lo =
  (((fromIntegral hi) `shiftL` 24)  .|.
   ((fromIntegral m1) `shiftL` 16)) .|.
  (((fromIntegral m2) `shiftL` 8)   .|.
    (fromIntegral lo))

readInt64FromArrayInt8 :: ByteString -> Int -> Word64
readInt64FromArrayInt8 arr i =
  let a = BS.index arr (i + 0) in
  let b = BS.index arr (i + 1) in
  let c = BS.index arr (i + 2) in
  let d = BS.index arr (i + 3) in
  let e = BS.index arr (i + 4) in
  let f = BS.index arr (i + 5) in
  let g = BS.index arr (i + 6) in
  let h = BS.index arr (i + 7) in
  mergeInt32 (octet4ToWord32 h g f e)
             (octet4ToWord32 d c b a)

read_rem len_rem offset bytes =
  let r = fromIntegral len_rem in
  let idx n = if n < r then BS.index bytes (offset + n) else 0 in
  let a = idx 0 in
  let b = idx 1 in
  let c = idx 2 in
  let d = idx 3 in
  let e = idx 4 in
  let f = idx 5 in
  let g = idx 6 in
  let h = idx 7 in
  mergeInt32 (octet4ToWord32 h g f e)
             (octet4ToWord32 d c b a)

bitlshr_64 :: Word64 -> Word64 -> Word64
bitlshr_64 a b = shiftR a (fromIntegral b)

rot :: Word64 -> Word64 -> Word64
rot !x !b = (shiftL x (fromIntegral b)) .|. (bitlshr_64 x (64 - b))

rot_xor a b c = rot a b `xor` c

half_round a0 b c0 d s t k =
  let
    a = a0 + b
    c = c0 + d
  in
  k (rot a 32) (rot_xor b s a) c (rot_xor d t c)

double_round v0 v1 v2 v3 k =
  half_round v0 v1 v2 v3 13 16 $ \ a0 b0 c0 d0 ->
  half_round c0 b0 a0 d0 17 21 $ \ c1 b1 a1 d1 ->
  half_round a1 b1 c1 d1 13 16 $ \ a2 b2 c2 d2 ->
  half_round c2 b2 a2 d2 17 21 $ \ c3 b3 a3 d3 ->
  k a3 b3 c3 d3

-- This is really a pure function, but GHC will CSE it too aggressively
-- if we admit that, so we pretend it needs IO for the benchmarking to work.
siphash24 :: ByteString -> ByteString -> IO Word64
siphash24 bytes key = do
  return $ go_sh (BS.length bytes) 0 v0 v1 v2 v3
    where
      k0 = readInt64FromArrayInt8 key 0
      k1 = readInt64FromArrayInt8 key 8
      b0 = BS.length bytes `shiftL` 56

      v0 = k0 `xor` 0x736f6d6570736575
      v1 = k1 `xor` 0x646f72616e646f6d
      v2 = k0 `xor` 0x6c7967656e657261
      v3 = k1 `xor` 0x7465646279746573

      go_sh len_rem offset v0 v1 v2 v3 =
        if len_rem >= 8 then
          let mi = readInt64FromArrayInt8 bytes offset in
          double_round v0 v1 v2 (v3 `xor` mi) $ \ v0 v1 v2 v3 ->
            let lenrem = len_rem - 8 in
            go_sh lenrem (offset + 8) (v0 `xor` mi) v1 v2 v3
        else
          let b = fromIntegral b0 .|. read_rem len_rem offset bytes in
          double_round v0           v1  v2  (v3 `xor` b) $ \ v0 v1 v2 v3 ->
          double_round (v0 `xor` b) v1 (v2 `xor` 255) v3 $ \ v0 v1 v2 v3 ->
          double_round v0           v1  v2            v3 $ \ v0 v1 v2 v3 ->
            xor v0 v1 `xor` xor v2 v3

siphash24_IO bytes key res = do
  sip <- siphash24 bytes key
  return $ res `xor` sip
