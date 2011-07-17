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

-- Either, with better names for the cases...
data OutputOr expr
    = OK      expr
    | Errors [Output]
    deriving (Eq)

data CompilesResult expr = CompilesResult (OutputOr expr)
instance (SourceRanged expr) => Show (CompilesResult expr) where
  show (CompilesResult (OK e))     = show (rangeOf e)
  show (CompilesResult (Errors _)) = "<...invalid term...>"

type Uniq = Int

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data CallConv = CCC | FastCC deriving (Eq, Show)
briefCC CCC = "ccc"
briefCC FastCC = ""

data ProcOrFunc = FT_Proc | FT_Func deriving (Show)

data VarNamespace = VarProc | VarLocal deriving (Show)

data TyVar = BoundTyVar String -- bound by a ForAll, that is
           | SkolemTyVar String Uniq deriving (Eq)

class Expr a where
    freeVars   :: a -> [String]

class AExpr a where
    freeIdents   :: a -> [Ident]

patBindingFreeIds :: AExpr e => (Pattern, e) -> [Ident]
patBindingFreeIds (pat, expr) =
  freeIdents expr `butnot` patBoundIds pat
  where patBoundIds :: Pattern -> [Ident]
        patBoundIds pat =
          case pat of
            P_Wildcard _rng      -> []
            P_Variable _rng id   -> [id]
            P_Bool     _rng _    -> []
            P_Int      _rng _    -> []
            P_Tuple    _rng pats -> concatMap patBoundIds pats

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- EPattern variable bindings can have type annotations
-- for typechecking.
data Pattern =
          P_Wildcard      ESourceRange
        | P_Variable      ESourceRange Ident
        | P_Bool          ESourceRange Bool
        | P_Int           ESourceRange LiteralInt
        | P_Tuple         ESourceRange [Pattern]
        deriving (Show)

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

identPrefix (GlobalSymbol name) = name
identPrefix (Ident name _)      = name

data Ident = Ident        String Uniq
           | GlobalSymbol String

instance Ord Ident where
    compare a b = compare (show a) (show b)

instance Eq Ident where
    i == j      =    (show i) == (show j)

instance Show Ident where
    show (Ident name number) = name ++ "!" ++ show number
    show (GlobalSymbol name) = name

data TypedId ty = TypedId { tidType :: ty, tidIdent :: Ident }

instance (Show ty) => Show (TypedId ty)
  where show (TypedId ty id) = show id ++ " :: " ++ show ty

data Show ty => FosterPrim ty
               = ILNamedPrim (TypedId ty)
               | ILPrimOp { ilPrimOpName :: String
                          , ilPrimOpSize :: Int }
               | ILCoroPrim  CoroPrim ty ty
            deriving (Show)

data CoroPrim = CoroCreate | CoroInvoke | CoroYield
            deriving (Show)

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

-- Note: sourceRangeLines is *all* lines, not just those in the range.
data ESourceRange = ESourceRange { sourceRangeBegin :: ESourceLocation
                                 , sourceRangeEnd   :: ESourceLocation
                                 , sourceRangeLines :: SourceLines
                                 , sourceRangeFile  :: Maybe String
                                 }
                  | EMissingSourceRange String

instance Show ESourceRange where
    show = showSourceRange

class SourceRanged a
  where rangeOf :: a -> ESourceRange

rangeSpanOf :: SourceRanged a => ESourceRange -> [a] -> ESourceRange
rangeSpanOf defaultRange allRanges =
    let ranges = map rangeOf allRanges in
    rsp defaultRange [r | r@(ESourceRange _ _ _ _) <- ranges]
  where rsp defaultRange [] = defaultRange
        rsp _ (b:srs) = ESourceRange (sourceRangeBegin b)
                                     (sourceRangeEnd $ last srs)
                                     (sourceRangeLines b)
                                     (sourceRangeFile  b)


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
