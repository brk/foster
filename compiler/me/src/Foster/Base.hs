module Foster.Base where

import System.Console.ANSI
import Control.Monad

import Data.Set as Set(fromList, toList, difference)
import Data.Sequence as Seq
import Data.Maybe(fromJust)
import Data.List as List
import qualified Data.Text as T

import Data.Char(toLower)
import Data.Bits(shiftR)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

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

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data LiteralInt = LiteralInt { litIntValue   :: Integer
                             , litIntMinBits :: Int
                             , litIntText    :: String
                             , litIntBase    :: Int
                             } deriving (Show)

getLiteralInt :: Int -> Int -> LiteralInt
getLiteralInt bits i = precheckedLiteralInt (show i) bits (show i) 10

-- Precondition: the provided string must be parseable in the given radix
precheckedLiteralInt :: String -> Int -> String -> Int -> LiteralInt
precheckedLiteralInt originalText maxBits clean base =
    let integerValue = parseRadixRev (fromIntegral base) (List.reverse clean) in
    let activeBits = List.length (bitStringOf integerValue) in
    LiteralInt integerValue activeBits originalText base

indexOf x = (toLower x) `List.elemIndex` "0123456789abcdef"

onlyValidDigitsIn :: String -> Int -> Bool
onlyValidDigitsIn str lim =
    let validIndex mi = Just True == fmap (< lim) mi in
    Prelude.all validIndex (map indexOf str)

-- Precondition: string contains only valid hex digits.
parseRadixRev :: Integer -> String -> Integer
parseRadixRev r ""     = 0
parseRadixRev r (c:cs) = (r * parseRadixRev r cs) + (fromIntegral $ fromJust (indexOf c))

lowBitOf n = if even n then "1" else "0"

bitStringOf n | n <= 1     = show n
              | otherwise = bitStringOf (shiftR n 1) ++ lowBitOf n

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data Ident = Ident { identPrefix :: String
                   , identNum    :: Uniq }

instance Ord Ident where
    compare a b = compare (show a) (show b)

instance Eq Ident where
    i@(Ident _ _) == j@(Ident _ _) = (show i) == (show j)

instance Show Ident where
    show i = (identPrefix i) ++ "!" ++ (show $ identNum i)

irrelevantIdentNum = (-12345) :: Int

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data ModuleAST fnCtor ty = ModuleAST {
          moduleASTfunctions   :: [fnCtor]
        , moduleASTdecls       :: [(String, ty)]
        , moduleASTsourceLines :: SourceLines
     }

butnot :: Ord a => [a] -> [a] -> [a]
butnot bs zs =
    let sbs = Set.fromList bs in
    let szs = Set.fromList zs in
    Set.toList (Set.difference sbs szs)

joinWith :: String -> [String] -> String
joinWith s [] = ""
joinWith s ss = foldr1 (++) (intersperse s ss)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

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

highlightFirstLine :: ESourceRange -> String
highlightFirstLine (EMissingSourceRange s) = "<missing range: " ++ s ++ ">"
highlightFirstLine (ESourceRange (ESourceLocation bline bcol)
                                 (ESourceLocation _     ecol) lines filepath) =
    "\n" ++ highlightLine bline bcol ecol lines ++ "\n"

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
highlightLine line bcol ecol lines =
    joinWith "\n" [sourceLine lines line, highlightLineRange bcol ecol]

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
showSourceLines (ESourceLocation bline bcol) (ESourceLocation eline ecol) lines =
    if bline == eline
        then joinWith "\n" [sourceLine lines bline, highlightLineRange bcol ecol]
        else joinWith "\n" [sourceLine lines n | n <- [bline..eline]]

-- Generates a string of spaces and twiddles which underlines
-- a given range of characters.
highlightLineRange :: Int -> Int -> String
highlightLineRange bcol ecol =
    let len = ecol - bcol in
    if len <= 0
        then ""
        else (List.replicate bcol ' ') ++ (List.replicate len '~')

data SourceLines = SourceLines (Seq T.Text)

sourceLine :: SourceLines -> Int -> String
sourceLine (SourceLines seq) n =
    if n < 0 || Seq.length seq <= n
        then "<no line " ++ show n ++ " of "
                         ++ (show $ Seq.length seq) ++ ">"
        else (T.unpack $ Seq.index seq n)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||


class Structured a where
    textOf     :: a -> Int -> Output
    childrenOf :: a -> [a]

-- Builds trees like this:
-- AnnSeq        :: i32
-- ├─AnnCall       :: i32
-- │ ├─AnnVar       expect_i32 :: ((i32) -> i32)
-- │ └─AnnTuple
-- │   └─AnnInt       999999 :: i32

showStructure :: (Structured a) => a -> Output
showStructure e = showStructureP e (out "") False where
    showStructureP e prefix isLast =
        let children = childrenOf e in
        let thisIndent = prefix ++ out (if isLast then "└─" else "├─") in
        let nextIndent = prefix ++ out (if isLast then "  " else "│ ") in
        let padding = max 6 (60 - Prelude.length thisIndent) in
        -- [ (child, index, numchildren) ]
        let childpairs = Prelude.zip3 children [1..]
                               (Prelude.repeat (Prelude.length children)) in
        let childlines = map (\(c, n, l) ->
                                showStructureP c nextIndent (n == l))
                             childpairs in
        (thisIndent :: Output) ++ (textOf e padding) ++ (out "\n") ++ (Prelude.foldl (++) (out "") childlines)

-----------------------------------------------------------------------
