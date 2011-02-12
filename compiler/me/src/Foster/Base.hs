module Foster.Base where

import System.Console.ANSI
import Control.Monad

import Data.Sequence as Seq
import Data.Maybe(fromJust)
import Data.List(replicate, intersperse)
import qualified Data.Text as T

data OutputData = OutputData { outputDataSGRs :: [SGR]
                             , outputDataString :: String }
type Output = [OutputData]

instance Eq OutputData where
    (OutputData _ sa) == (OutputData _ sb) = sa == sb

out :: String -> Output
out s = [(OutputData ([] :: [SGR]) s)]

outLn s = out (s ++ "\n")

outCS :: Color -> String -> Output
outCS c s = [OutputData [SetColor Foreground Dull c] s]

outCSLn c s = outCS c (s ++ "\n")

outToString :: Output -> String
outToString o = concat $ map outputDataString o

runOutput :: Output -> IO ()
runOutput outs = do
    forM_ outs $ (\(OutputData sgrs str) -> do
                _ <- setSGR sgrs
                putStr str
                setSGR []
            )

type Uniq = Int

data Literal = LitInt LiteralInt

data LiteralInt = LiteralInt { litIntMinBits :: Integer
                             , litIntText    :: String
                             , litIntClean   :: String
                             , litIntBase    :: Int
                             } deriving (Show)

data Ident = Ident { identPrefix :: String
                   , identNum    :: Uniq }

instance Ord Ident where
    compare a b = compare (show a) (show b)

instance Eq Ident where
    i@(Ident _ _) == j@(Ident _ _) = (show i) == (show j)

instance Show Ident where
    show i = (identPrefix i) ++ "!" ++ (show $ identNum i)

irrelevantIdentNum = (-12345) :: Int




joinWith :: String -> [String] -> String
joinWith s [] = ""
joinWith s ss = foldr1 (++) (intersperse s ss)


data ESourceLocation = ESourceLocation { sourceLocationLine :: Int
                                       , sourceLocationCol  :: Int
                                       } deriving (Eq, Show)

data ESourceRange = ESourceRange { sourceRangeBegin :: ESourceLocation
                                 , sourceRangeEnd   :: ESourceLocation
                                 , sourceRangeLines :: SourceLines
                                 , sourceRangeFile  :: Maybe String
                                 }
                  | EMissingSourceRange String

instance Show ESourceRange where
    show = showSourceRange

showSourceRange :: ESourceRange -> String
showSourceRange (EMissingSourceRange s) = "<missing range: " ++ s ++ ">"
showSourceRange (ESourceRange begin end lines filepath) = "\n" ++ showSourceLines begin end lines ++ "\n"

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
showSourceLines (ESourceLocation bline bcol) (ESourceLocation eline ecol) lines =
    if bline == eline
        then joinWith "\n" [fromJust $ sourceLine lines bline, highlightLineRange bcol ecol]
        else joinWith "\n" [fromJust $ sourceLine lines n | n <- [bline..eline]]

-- Generates a string of spaces and twiddles which underlines
-- a given range of characters.
highlightLineRange :: Int -> Int -> String
highlightLineRange bcol ecol =
    let len = ecol - bcol in
    if len <= 0
        then ""
        else (Data.List.replicate bcol ' ') ++ (Data.List.replicate len '~')

data SourceLines = SourceLines (Seq T.Text)

sourceLine :: SourceLines -> Int -> Maybe String
sourceLine (SourceLines seq) n =
    if n < 0 || Seq.length seq < n
        then Nothing
        else Just (T.unpack $ Seq.index seq n)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
