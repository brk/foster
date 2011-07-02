module Foster.ProtobufUtils
where
import qualified Text.ProtocolBuffers.Header as P'
import qualified Data.Text as T
import Data.ByteString.Lazy.UTF8 as UTF8
import Text.ProtocolBuffers.Basic(uToString)
-- uToString :: P'.Utf8 -> String

-- String conversions

pUtf8ToText :: P'.Utf8 -> T.Text
pUtf8ToText p = T.pack (uToString p)

textToPUtf8 :: T.Text -> P'.Utf8
textToPUtf8 t = u8fromString $ T.unpack t

u8fromString :: String -> P'.Utf8
u8fromString s = P'.Utf8 (UTF8.fromString s)

intToInt32 :: Int -> P'.Int32
intToInt32 i = fromInteger $ toInteger i
