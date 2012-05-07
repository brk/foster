module Foster.ProtobufUtils
where
import qualified Text.ProtocolBuffers.Header as P'
import qualified Data.Text as T
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.Encoding as E
import Data.ByteString.Lazy.UTF8 as UTF8
import Text.ProtocolBuffers.Basic(toUtf8)

-- String conversions
pUtf8ToText :: P'.Utf8 -> T.Text
pUtf8ToText p = (L.toStrict . E.decodeUtf8 . P'.utf8) p

textToPUtf8 :: T.Text -> P'.Utf8
textToPUtf8 t = case (toUtf8 . E.encodeUtf8 . L.fromStrict) t of
                  Right u  -> u
                  Left int -> error $ "Encoding string " ++ T.unpack t
                                      ++ " to UTF8 failed: " ++ show int

u8fromString :: String -> P'.Utf8
u8fromString s = P'.Utf8 (UTF8.fromString s)

intToInt32 :: Int -> P'.Int32
intToInt32 i = fromInteger $ toInteger i

