{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Base where

import System.Console.ANSI
import Control.Monad

import Data.IORef
import Data.Set as Set(fromList, toList, difference)
import Data.Sequence as Seq
import Data.Map as Map(Map)
import Data.List as List
import qualified Data.Text as T

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
outToString o = concatMap outputDataString o

-- Conceptually, for each string, we apply its graphics commands,
-- print the string, and then reset the SGR mode. But resetting
-- turns out to be expensive, so we track our state and only do
-- the apply/resets when we actually need to.
runOutput :: Output -> IO ()
runOutput outs = do
    stateRef <- newIORef OutputStateUnknown
    let forciblyRunOutput sgrs str = do
          _ <- setSGR sgrs
          putStr str
          case sgrs of -- no need to reset if we already reset!
                [] -> return ()
                _  -> setSGR [] -- [] means reset, not do nothing.
          writeIORef stateRef OutputStateClean
    forM_ outs $ (\(OutputData sgrs str) -> do
        state <- readIORef stateRef
        case state of -- if we're clean and not modifying, we can just putStr.
          OutputStateUnknown -> forciblyRunOutput sgrs str
          OutputStateClean ->
                    case sgrs of [] -> putStr str
                                 _  -> forciblyRunOutput sgrs str
      )
data OutputState = OutputStateUnknown | OutputStateClean

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
            P_Wildcard _rng         -> []
            P_Variable _rng id      -> [id]
            P_Bool     _rng _       -> []
            P_Int      _rng _       -> []
            P_Ctor     _rng pats nm -> concatMap patBoundIds pats
            P_Tuple    _rng pats    -> concatMap patBoundIds pats

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data Pattern =
          P_Wildcard      SourceRange
        | P_Variable      SourceRange Ident
        | P_Ctor          SourceRange [Pattern] CtorId
        | P_Bool          SourceRange Bool
        | P_Int           SourceRange LiteralInt
        | P_Tuple         SourceRange [Pattern]

instance Show Pattern where
  show (P_Wildcard _)           = "P_Wildcard"
  show (P_Variable _ id)        = "P_Variable " ++ show id
  show (P_Ctor     _ pats ctor) = "P_Ctor     " ++ show ctor
  show (P_Bool     _ b)         = "P_Bool     " ++ show b
  show (P_Int      _ i)         = "P_Int      " ++ show (litIntText i)
  show (P_Tuple    _ pats)      = "P_Tuple    " ++ show pats

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data (Show ty) => DataType ty = DataType String [DataCtor ty] deriving Show
data (Show ty) => DataCtor ty = DataCtor String Int [ty]      deriving Show

dataTypeName  (DataType name _)  = name
dataTypeCtors (DataType _ ctors) = ctors

-- CtorIds are created before typechecking.
data CtorId     = CtorId   { ctorTypeName :: String
                           , ctorCtorName :: String
                           , ctorArity    :: Int
                           , ctorSmallInt :: Int
                           } deriving (Show, Eq)

instance Ord CtorId where
  compare a b = compare (show a) (show b)

type CtorName = String
type DataTypeName = String

data DataTypeSig = DataTypeSig (Map CtorName CtorId) deriving Show
type DataTypeSigs = Map DataTypeName DataTypeSig

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data ModuleAST fnCtor ty = ModuleAST {
          moduleASTfunctions   :: [fnCtor]
        , moduleASTdecls       :: [(String, ty)]
        , moduleASTdataTypes   :: [DataType ty]
        , moduleASTsourceLines :: SourceLines
     }

data Fn expr ty = Fn { fnVar   :: TypedId ty
                     , fnVars  :: [TypedId ty]
                     , fnBody  :: expr
                     , fnRange :: SourceRange
                     , fnFreeVars :: [TypedId ty]
                     } deriving (Show)

data ModuleIL expr ty = ModuleIL {
          moduleILfunctions   :: [Fn expr ty]
        , moduleILdecls       :: [(String, ty)]
        , moduleILdataTypes   :: [DataType ty]
        , moduleILsourceLines :: SourceLines
     }

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data ESourceLocation = ESourceLocation { sourceLocationLine :: Int
                                       , sourceLocationCol  :: Int
                                       } deriving (Eq, Show)

-- Note: sourceRangeLines is *all* lines, not just those in the range.
data SourceRange = SourceRange { sourceRangeBegin :: ESourceLocation
                               , sourceRangeEnd   :: ESourceLocation
                               , sourceRangeLines :: SourceLines
                               , sourceRangeFile  :: Maybe String
                               }
                  | MissingSourceRange String

instance Show SourceRange where
    show = showSourceRange

class SourceRanged a
  where rangeOf :: a -> SourceRange

-- Used in ProtobufFE and Typecheck.hs.
rangeSpanOf :: SourceRanged a => SourceRange -> [a] -> SourceRange
rangeSpanOf defaultRange allRanges =
    let ranges = map rangeOf allRanges in
    rsp defaultRange [r | r@(SourceRange _ _ _ _) <- ranges]
  where rsp defaultRange [] = defaultRange
        rsp _ (b:srs) = SourceRange (sourceRangeBegin b)
                                     (sourceRangeEnd $ last srs)
                                     (sourceRangeLines b)
                                     (sourceRangeFile  b)

showSourceRange :: SourceRange -> String
showSourceRange (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
showSourceRange (SourceRange begin end lines filepath) = "\n" ++ showSourceLines begin end lines ++ "\n"

highlightFirstLine :: SourceRange -> String
highlightFirstLine (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
highlightFirstLine (SourceRange (ESourceLocation bline bcol)
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
showStructure e = showStructureP e (out "") False
  where
    showStructureP :: Structured b => b -> Output -> Bool -> Output
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
        (thisIndent :: Output) ++ (textOf e padding) ++ (out "\n")
                               ++ (Prelude.foldl (++) (out "") childlines)

-----------------------------------------------------------------------

-- | Does what it says on the tin: monadically combines a map and a fold,
-- | threading state through.
mapFoldM :: (Monad m) => [a] -> b ->
                         (a  -> b -> m ([c], b))
                                  -> m ([c], b)
mapFoldM []     b  f = return ([], b)
mapFoldM (x:xs) b1 f = do
    (cs1, b2) <- f x b1
    (cs2, b3) <- mapFoldM xs b2 f
    return (cs1 ++ cs2, b3)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

butnot :: Ord a => [a] -> [a] -> [a]
butnot bs zs =
    let sbs = Set.fromList bs in
    let szs = Set.fromList zs in
    Set.toList (Set.difference sbs szs)

joinWith :: String -> [String] -> String
joinWith s [] = ""
joinWith s ss = foldr1 (++) (intersperse s ss)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data LiteralInt = LiteralInt { litIntValue   :: Integer
                             , litIntMinBits :: Int
                             , litIntText    :: String
                             , litIntBase    :: Int
                             } deriving (Show)

-- | Example: bitStringOf 21 == "10101"
bitStringOf n | n <= 1     = show n
              | otherwise = bitStringOf (shiftR n 1) ++ lowBitOf n
                     where lowBitOf n = if even n then "1" else "0"

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
