{-# LANGUAGE GADTs , StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Base where

import Foster.Kind
import Foster.Output

import Data.IORef(IORef)
import Data.Set as Set(Set, fromList, toList, difference, insert, empty, member)
import Data.Sequence as Seq(Seq, length, index, (><))
import Data.Map as Map(Map)
import Data.List as List(replicate, intersperse)

import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Text as T

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

class Expr a where
    freeVars   :: a -> [T.Text]

class AExpr a where
    freeIdents   :: a -> [Ident]

class TExpr a t where
    freeTypedIds   :: a -> [TypedId t]

class TypedWith a t where
    typeOf :: a -> t

class IntSized t where
    intSizeOf :: t -> Int

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

data CompilesResult expr = CompilesResult (OutputOr expr)
type Uniq = Int
data CallConv = CCC | FastCC deriving (Eq, Show)
type LogInt = Int
data IntSizeBits = I1 | I8 | I32 | I64
                 | IWord LogInt -- Word 3 means 8x larger; -2 is 4x smaller.
                 deriving (Eq, Show)

data ProcOrFunc   = FT_Proc | FT_Func  deriving Show
data VarNamespace = VarProc | VarLocal deriving Show
data TailQ = YesTail | NotTail deriving Show
data MayGC = GCUnknown String | MayGC | WillNotGC deriving (Eq, Show)

data SafetyGuarantee = SG_Static | SG_Dynamic               deriving (Show)
data ArrayIndex expr = ArrayIndex expr expr SourceRange
                                            SafetyGuarantee deriving (Show)

-- In contrast to meta type variables, the IORef for inferred types
-- can contain a sigma, not just a tau. See Typecheck.hs for details.
data Expected t = Infer (IORef t) | Check t

data TyVar = BoundTyVar  String -- bound by a ForAll, that is
           | SkolemTyVar String Uniq Kind

instance Pretty TyVar where
  pretty (BoundTyVar name) = text "'" <> text name
  pretty (SkolemTyVar name uniq _kind) = text "$" <> text name <> text ":" <> pretty uniq

data MTVQ = MTVSigma | MTVTau deriving (Eq)
data MetaTyVar t = Meta { mtvConstraint :: MTVQ
                        , mtvDesc       :: String
                        , mtvUniq       :: Uniq
                        , mtvRef        :: IORef (Maybe t)
                        }

childrenOfArrayIndex (ArrayIndex a b _ _) = [a, b]

briefCC CCC = "ccc"
briefCC FastCC = ""

boolGC  WillNotGC    = False
boolGC  MayGC        = True
boolGC (GCUnknown _) = True

-- |||||||||||||||||||||||||| Patterns ||||||||||||||||||||||||||{{{

data E_VarAST ty = VarAST { evarMaybeType :: Maybe ty
                          , evarName      :: T.Text }

data EPattern ty =
          EP_Wildcard     SourceRange
        | EP_Variable     SourceRange (E_VarAST ty)
        | EP_Ctor         SourceRange [EPattern ty] T.Text
        | EP_Bool         SourceRange Bool
        | EP_Int          SourceRange String
        | EP_Tuple        SourceRange [EPattern ty]

data Pattern ty =
          P_Wildcard      SourceRange ty
        | P_Variable      SourceRange (TypedId ty)
        | P_Ctor          SourceRange ty [Pattern ty] (CtorInfo ty)
        | P_Bool          SourceRange ty Bool
        | P_Int           SourceRange ty LiteralInt
        | P_Tuple         SourceRange ty [Pattern ty]

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||| Data Types |||||||||||||||||||||||||||||||{{{
data DataType ty = DataType {
    dataTypeName      :: DataTypeName
  , dataTypeTyFormals :: [TypeFormalAST]
  , dataTypeCtors     :: [DataCtor ty]
  }

data DataCtor ty = DataCtor { dataCtorName  :: CtorName
                            , dataCtorSmall :: Int
                            , dataCtorDTTyF :: [TypeFormalAST]
                            , dataCtorTypes :: [ty]
                            }

-- CtorIds are created before typechecking.
data CtorId     = CtorId   { ctorTypeName :: DataTypeName
                           , ctorCtorName :: String
                           , ctorArity    :: Int
                           , ctorSmallInt :: Int
                           } deriving (Show, Eq)

data CtorInfo ty = CtorInfo { ctorInfoId :: CtorId
                            , ctorInfoDc :: DataCtor ty
                            } deriving Show -- for Typecheck

type CtorName     = T.Text
type DataTypeName = String

data DataTypeSig   = DataTypeSig (Map CtorName CtorId)

-- Occurrences are generated in pattern matching (and pushed through to LLVM).
-- A pair (n, c) in an occurrence means "field n of the struct type for ctor c".
type FieldOfCtor ty = (Int, CtorInfo ty)
type Occurrence ty = [FieldOfCtor ty]
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||| Literals |||||||||||||||||||||||||||||||||{{{
data Literal = LitInt   LiteralInt
             | LitFloat LiteralFloat
             | LitText  T.Text
             | LitBool  Bool

data LiteralInt = LiteralInt { litIntValue   :: Integer
                             , litIntMinBits :: Int
                             , litIntText    :: String
                             , litIntBase    :: Int
                             }

data LiteralFloat = LiteralFloat { litFloatValue   :: Double
                                 , litFloatText    :: String
                                 }

instance Pretty Literal where
  pretty (LitInt int) = red     $ text (litIntText int)
  pretty (LitFloat f) = dullred $ text (litFloatText f)
  pretty (LitText  t) =  dquotes (text $ T.unpack t)
  pretty (LitBool  b) =           text (if b then "True" else "False")

data WholeProgramAST fnCtor ty = WholeProgramAST {
          programASTmodules    :: [ModuleAST fnCtor ty]
     }

data ModuleAST fnCtor ty = ModuleAST {
          moduleASThash        :: String
        , moduleASTfunctions   :: [fnCtor ty]
        , moduleASTdecls       :: [(String, ty)]
        , moduleASTdataTypes   :: [DataType ty]
        , moduleASTsourceLines :: SourceLines
        , moduleASTprimTypes   :: [DataType ty]
     }

data Fn expr ty = Fn { fnVar   :: TypedId ty
                     , fnVars  :: [TypedId ty]
                     , fnBody  :: expr
                     , fnIsRec :: Maybe Bool
                     , fnAnnot :: ExprAnnot
                     } deriving Show -- For KNExpr and KSmallstep

fnType :: Fn e t -> t
fnType fn = tidType $ fnVar fn

fnIdent fn = tidIdent $ fnVar fn

data ModuleIL expr ty = ModuleIL {
          moduleILbody        :: expr
        , moduleILdecls       :: [(String, ty)]
        , moduleILdataTypes   :: [DataType ty]
        , moduleILprimTypes   :: [DataType ty]
        , moduleILsourceLines :: SourceLines
     }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||| Source Ranges ||||||||||||||||||||||||{{{

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

beforeRangeStart _ (MissingSourceRange _) = False
        -- error "cannot compare source location to missing source range!"
beforeRangeStart loc (SourceRange begin _ _ _) =
         sourceLocationLine loc <  sourceLocationLine begin
     || (sourceLocationLine loc == sourceLocationLine begin
     &&  sourceLocationCol  loc <  sourceLocationCol  begin)

beforeRangeEnd _ (MissingSourceRange _) = False
        -- error "cannot compare source location to missing source range!"
beforeRangeEnd loc (SourceRange _ end _ _) =
         sourceLocationLine loc <  sourceLocationLine end
     || (sourceLocationLine loc == sourceLocationLine end
     &&  sourceLocationCol  loc <  sourceLocationCol  end)

class SourceRanged a
  where rangeOf :: a -> SourceRange

-- Used in ProtobufFE and Typecheck.hs.
rangeSpanOf :: SourceRanged a => SourceRange -> [a] -> SourceRange
rangeSpanOf defaultRange allRanges =
    let ranges = map rangeOf allRanges in
    rsp defaultRange [r | r@(SourceRange _ _ _ _) <- ranges]
  where rsp defaultRange [] = defaultRange
        rsp __ ranges@(b:_) = SourceRange (sourceRangeBegin b)
                                          (sourceRangeEnd $ last ranges)
                                          (sourceRangeLines b)
                                          (sourceRangeFile  b)

showSourceRange :: SourceRange -> String
showSourceRange (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
showSourceRange (SourceRange begin end lines _filepath) =
         "\n" ++ showSourceLines begin end lines ++ "\n"

highlightFirstLine :: SourceRange -> String
highlightFirstLine (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
highlightFirstLine (SourceRange (ESourceLocation bline bcol)
                                (ESourceLocation eline ecol) lines _filepath) =
    "\n" ++ highlightLine bline bcol fcol lines ++ "\n"
      where fcol  = if lineb == linee then ecol else Prelude.length lineb
            lineb = sourceLine lines bline
            linee = sourceLine lines eline

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

appendSourceLines (SourceLines s1) (SourceLines s2) = SourceLines (s1 >< s2)

sourceLine :: SourceLines -> Int -> String
sourceLine (SourceLines seq) n =
    if n < 0 || Seq.length seq <= n
        then "<no line " ++ show n ++ " of "
                         ++ (show $ Seq.length seq) ++ ">"
        else (T.unpack $ Seq.index seq n)

data Formatting = Comment    {-SourceRange-} String
                | BlankLine
                | NonHidden
                deriving Show

data ExprAnnot = ExprAnnot
                        [Formatting] -- preceding comments and/or blank lines.
                        SourceRange  -- range of bare expr not incl. formatting.
                        [Formatting] -- trailing comments and/or blank lines.

annotRange :: ExprAnnot -> SourceRange
annotRange (ExprAnnot _ rng _) = rng

instance Show ExprAnnot where show (ExprAnnot _ rng _) = show rng

data AllocationSource = AllocationSource String SourceRange deriving Show


data Comments = C { leading :: [Formatting], trailing :: [Formatting] } deriving Show
annotComments (ExprAnnot l _ t) = C l t

showComments (C [] []) = ""
showComments other     = " ... " ++ show other


-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||| Structured Things ||||||||||||||||||||||{{{

class Structured a where
    textOf     :: a -> Int -> Doc
    childrenOf :: a -> [a]

-- Builds trees like this:
-- AnnSeq        :: i32
-- ├─AnnCall       :: i32
-- │ ├─AnnVar       expect_i32 :: ((i32) -> i32)
-- │ └─AnnTuple
-- │   └─AnnInt       999999 :: i32

showStructure :: (Structured a) => a -> Doc
showStructure e = showStructureP e "" False
  where
    showStructureP :: Structured b => b -> String -> Bool -> Doc
    showStructureP e prefix isLast =
        let children = childrenOf e in
        let thisIndent = prefix ++ (if isLast then "└─" else "├─") in
        let nextIndent = prefix ++ (if isLast then "  " else "│ ") in
        let padding = max 6 (60 - Prelude.length thisIndent) in
        -- [ (child, index, numchildren) ]
        let childpairs = Prelude.zip3 children [1..]
                               (Prelude.repeat (Prelude.length children)) in
        let childlines = map (\(c, n, l) ->
                                showStructureP c nextIndent (n == l))
                             childpairs in
        text thisIndent <> textOf e padding <> line
                                     <> (Prelude.foldl (<>) PP.empty childlines)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||||| Utilities ||||||||||||||||||||||||||{{{

-- | Does what it says on the tin: monadically combines a map and a fold,
-- | threading state through.
mapFoldM :: (Monad m) => [a] -> b ->
                         (a  -> b -> m ([c], b))
                                  -> m ([c], b)
mapFoldM []     b  _ = return ([], b)
mapFoldM (x:xs) b1 f = do
    (cs1, b2) <- f x b1
    (cs2, b3) <- mapFoldM xs b2 f
    return (cs1 ++ cs2, b3)

-- | A monadic left scan; used for accumulating intermediate optimized versions.
scanlM :: Monad m => (a -> b -> m a) -> a -> [b] -> m [a]
scanlM f z ls = do zs <- case ls of []   -> do return []
                                    x:xs -> do z' <- f z x
                                               scanlM f z' xs
                   return $ z : zs

mapFoldM' :: (Monad m) => [a] -> b ->
                          (a  -> b -> m ( c,  b))
                                   -> m ([c], b)
mapFoldM' []     b  _ = return ([], b)
mapFoldM' (x:xs) b1 f = do
    (c1,  b2) <- f x b1
    (cs2, b3) <- mapFoldM' xs b2 f
    return (c1 : cs2, b3)

butnot :: Ord a => [a] -> [a] -> [a]
butnot bs zs =
    let sbs = Set.fromList bs in
    let szs = Set.fromList zs in
    Set.toList (Set.difference sbs szs)

detectDuplicates :: Ord a => [a] -> [a]
detectDuplicates xs = go xs Set.empty Set.empty
  where go []    _seen dups = Set.toList dups
        go (x:xs) seen dups =
          if Set.member x seen then go xs seen (Set.insert x dups)
                               else go xs (Set.insert x seen) dups

joinWith :: String -> [String] -> String
joinWith _ [] = ""
joinWith s ss = foldr1 (++) (intersperse s ss)

prependedTo :: String -> T.Text -> T.Text
prependedTo str txt = T.pack str `T.append` txt

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||||| Idents |||||||||||||||||||||||||||{{{

identPrefix (GlobalSymbol name) = name
identPrefix (Ident name _)      = name

data Ident = Ident        T.Text Uniq
           | GlobalSymbol T.Text

data TypedId ty = TypedId { tidType :: ty, tidIdent :: Ident }

type PatternBinding expr ty = ((Pattern ty, [TypedId ty]), expr)

data FosterPrim ty = NamedPrim (TypedId ty) -- invariant: global symbol
                   | PrimOp { ilPrimOpName :: String
                            , ilPrimOpType :: ty }
                   | PrimIntTrunc IntSizeBits IntSizeBits -- from, to
                   | CoroPrim  CoroPrim ty ty

data CoroPrim = CoroCreate | CoroInvoke | CoroYield

-- TODO distinguish stable pointers from lively pointers?
--      stable-pointer-bit at compile time or runtime?
-- TODO other allocation zones? -- refcounted heap, thread-local heap,
--                                 C/malloc/free heap,
--                                 type-specific heaps, etc, etc...
data AllocMemRegion = MemRegionStack
                    | MemRegionGlobalHeap deriving Show

memRegionMayGC :: AllocMemRegion -> MayGC
memRegionMayGC MemRegionStack = WillNotGC
memRegionMayGC MemRegionGlobalHeap = MayGC

data AllocInfo t = AllocInfo { allocType      :: t
                             , allocRegion    :: AllocMemRegion
                             , allocTypeName  :: String
                             , allocCtorTag   :: Maybe Int
                             , allocArraySize :: Maybe (TypedId t)
                             , allocSite      :: String
                             , allocZeroInit  :: ZeroInit
                             }

data ZeroInit = DoZeroInit | NoZeroInit deriving Show

type MayGCConstraint = (MayGC -- at most one direct constraint
                       ,Set.Set Ident) --any # of indirect constraints
type MayGCConstraints = Map Ident MayGCConstraint

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||||| Instances ||||||||||||||||||||||||||{{{

instance IntSized IntSizeBits
 where intSizeOf = intOfSize where
                       intOfSize I1 = 1
                       intOfSize I8 = 8
                       intOfSize I32 = 32
                       intOfSize I64 = 64
                       intOfSize (IWord 0) = 32 -- TODO this is hacky =/
                       intOfSize (IWord 1) = 64

sizeOfBits :: Int -> IntSizeBits
sizeOfBits 1           = I1
sizeOfBits n | n <= 8  = I8
sizeOfBits n | n <= 32 = I32
sizeOfBits n | n <= 64 = I64
sizeOfBits n = error $ "TypecheckInt.hs:sizeOfBits: Unsupported size: " ++ show n

instance Pretty IntSizeBits    where pretty i = text (show $ intSizeOf i)
instance Pretty Ident          where pretty id = text (show id)
instance Pretty t => Pretty (TypedId t)
                               where pretty tid = pretty (tidIdent tid)
instance SourceRanged expr => Pretty (CompilesResult expr)
                               where pretty cr = text (show cr)

deriving instance (Show ty) => Show (DataType ty)
deriving instance (Show ty) => Show (DataCtor ty)

instance Ord CtorId where
  compare a b = compare (show a) (show b)

instance Ord Ident where
    compare a b = compare (show a) (show b)

instance Eq Ident where
    i == j      =    (show i) == (show j)

instance Show Ident where
    show (Ident name number) = T.unpack name ++ "!" ++ show number
    show (GlobalSymbol name) = T.unpack name

instance Eq (TypedId t) where
       (==) (TypedId _ a) (TypedId _ b) = (==) a b

instance Ord (TypedId t) where
    compare (TypedId _ a) (TypedId _ b) = compare a b

instance (Show ty) => Show (TypedId ty)
  where show (TypedId ty id) = show id ++ " :: " ++ show ty

instance Eq TyVar where
  BoundTyVar s1      == BoundTyVar s2      = s1 == s2
  SkolemTyVar _ u1 _ == SkolemTyVar _ u2 _ = u1 == u2
  _ == _ = False

instance Ord TyVar where
  BoundTyVar s1      `compare` BoundTyVar s2      = s1 `compare` s2
  SkolemTyVar _ u1 _ `compare` SkolemTyVar _ u2 _ = u1 `compare` u2
  BoundTyVar s1      `compare` SkolemTyVar s2 _ _ = s1 `compare` s2
  SkolemTyVar s1 _ _ `compare` BoundTyVar s2      = s1 `compare` s2

prettyOccurrence v occ = pretty v <> text "/" <> pretty (map fst occ)

instance Show TyVar where
    show (BoundTyVar x) = "'" ++ x
    show (SkolemTyVar x u k) = "$" ++ x ++ "." ++ show u ++ "::" ++ show k

instance Show SourceRange where
    show _ = "<...source range...>"

instance (SourceRanged expr) => Show (CompilesResult expr) where
  show (CompilesResult (OK e))     = show (rangeOf e)
  show (CompilesResult (Errors _)) = "<...invalid term...>"

instance Show (Pattern ty) where
  show (P_Wildcard _ _)            = "P_Wildcard"
  show (P_Variable _ v)            = "P_Variable " ++ show (tidIdent v)
  show (P_Ctor     _ _ _pats ctor) = "P_Ctor     " ++ show (ctorInfoId ctor)
  show (P_Bool     _ _ b)          = "P_Bool     " ++ show b
  show (P_Int      _ _ i)          = "P_Int      " ++ show (litIntText i)
  show (P_Tuple    _ _ pats)       = "P_Tuple    " ++ show pats

instance Pretty ty => Pretty (EPattern ty) where
  pretty (EP_Wildcard _)            = text "EP_Wildcard"
  pretty (EP_Variable _ v)          = text "EP_Variable " <> pretty v
  pretty (EP_Ctor     _ _pats ctor) = text "EP_Ctor     " <> text (show ctor)
  pretty (EP_Bool     _ b)          = text "EP_Bool     " <> pretty b
  pretty (EP_Int      _ str)        = text "EP_Int      " <> text str
  pretty (EP_Tuple    _ pats)       = text "EP_Tuple    " <> pretty pats

instance Pretty ty => Pretty (E_VarAST ty) where
  pretty (VarAST (Just ty) txt) = text (T.unpack txt) <+> text "::" <+> pretty ty
  pretty (VarAST Nothing   txt) = text (T.unpack txt)

instance Pretty t => Pretty (FosterPrim t) where
  pretty (NamedPrim (TypedId _ i)) = text (show i)
  pretty (PrimOp nm _ty) = text nm
  pretty (PrimIntTrunc frm to) = text ("trunc from " ++ show frm ++ " to " ++ show to)
  pretty (CoroPrim c t1 t2) = text "...coroprim..."

instance Show ty => Show (EPattern ty) where
  show (EP_Wildcard _)            = "EP_Wildcard"
  show (EP_Variable _ v)          = "EP_Variable " ++ show v
  show (EP_Ctor     _ _pats ctor) = "EP_Ctor     " ++ show ctor
  show (EP_Bool     _ b)          = "EP_Bool     " ++ show b
  show (EP_Int      _ str)        = "EP_Int      " ++ str
  show (EP_Tuple    _ pats)       = "EP_Tuple    " ++ show pats

instance TExpr body t => TExpr (Fn body t) t where
    freeTypedIds f = let bodyvars =  freeTypedIds (fnBody f) in
                     let boundvars =              (fnVars f) in
                     bodyvars `butnot` boundvars

instance TExpr (ArrayIndex (TypedId t)) t where
   freeTypedIds (ArrayIndex v1 v2 _ _) = [v1, v2]

deriving instance (Show ty) => Show (AllocInfo ty)
deriving instance (Show ty) => Show (E_VarAST ty)
deriving instance (Show ty) => Show (FosterPrim ty)
deriving instance Show CoroPrim
deriving instance Show LiteralInt
deriving instance Show LiteralFloat
deriving instance Show Literal

deriving instance Functor Pattern
deriving instance Functor TypedId
deriving instance Functor AllocInfo
deriving instance Functor FosterPrim
deriving instance Functor CtorInfo
deriving instance Functor DataCtor
deriving instance Functor DataType
deriving instance Functor ArrayIndex
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

