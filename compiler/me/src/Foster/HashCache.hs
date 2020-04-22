{-# LANGUAGE Strict #-}

module Foster.HashCache (HashCache, getHashCache,
    hashCacheInsert, hashCacheQuery, hashCachePersist)

where

import Data.Set(Set)
import qualified Data.Set as Set(member, empty, insert, toList, fromList, size)
import Data.IORef(newIORef, readIORef, modifyIORef', IORef)

import Codec.CBOR.Encoding
import Codec.CBOR.Write
import Codec.CBOR.Term
import Codec.CBOR.Read (deserialiseFromBytes)

import System.Directory (doesFileExist)

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as L(readFile)

data HashCache = HashCache {
      hcInitialSize :: Int
    , hcCurrent :: IORef (Set Integer)
    , hcPath :: FilePath
}

type CBOR = Term

cb_int :: CBOR -> Integer
cb_int cbor = case cbor of
    TInt     int     -> fromIntegral int
    TInteger integer -> integer
    TSimple  word8   -> fromIntegral word8
    _ -> error $ "cb_int had unexpected input: " ++ show cbor


getHashCache :: FilePath -> IO HashCache
getHashCache path = do
    exists <- doesFileExist path
    if exists
        then do
            bytes <- L.readFile path
            case deserialiseFromBytes decodeTerm bytes of
                Left failure -> error $ show failure
                Right (_bs, TList terms) -> do
                    let ints = map cb_int terms
                        s    = Set.fromList ints
                        sz   = Set.size s
                    ref <- newIORef s
                    return $ HashCache sz ref path
                Right _ -> error $ "getHashCache had unexpected CBOR term!"
        else do
            ref <- newIORef Set.empty
            return $ HashCache 0 ref path

hashCacheInsert :: HashCache -> Integer -> IO ()
hashCacheInsert hc v = do
    modifyIORef' (hcCurrent hc) (\s -> Set.insert v s)

hashCacheQuery :: HashCache -> Integer -> IO Bool
hashCacheQuery hc v = do
    s <- readIORef (hcCurrent hc)
    return $ Set.member v s

hashCachePersist :: HashCache -> IO ()
hashCachePersist hc = do
    s <- readIORef (hcCurrent hc)
    -- Note: caches only grow, so this suffices to detect changes.
    if Set.size s == (hcInitialSize hc)
      then
            -- Nothing to do!
            return ()
      else do
            let l = Set.toList s
            let enc = encoded l (fromIntegral $ Set.size s)
            let bs  = toStrictByteString enc
            BS.writeFile (hcPath hc) bs

encoded l sz = do
    encodeListLen sz <> mconcat (map encodeInteger l)