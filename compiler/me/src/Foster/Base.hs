{-# LANGUAGE GADTs , StandaloneDeriving, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Base where

import Prelude hiding ((<$>))

import Foster.Kind
import Foster.Output

import Data.IORef(IORef, readIORef, writeIORef)
import Data.Set as Set(Set, fromList, toList, difference, insert, empty, member,
                                      null, intersection)
import Data.Sequence as Seq(Seq, length, index, (><))
import Data.Map as Map(Map, fromListWith)
import Data.List as List(replicate, intersperse)
import qualified Data.Graph as Graph(SCC(..), stronglyConnComp)

import Text.PrettyPrint.ANSI.Leijen
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Text as T
import qualified Data.ByteString as B

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

class IntSizedBits t where
    intSizeBitsOf :: t -> IntSizeBits

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
data CompilesResult expr = CompilesResult (OutputOr expr)
type Uniq = Int
data CallConv = CCC | FastCC deriving (Eq, Show)
type LogInt = Int
data IntSizeBits = I1 | I8 | I16 | I32 | I64 | IWd | IDw -- Word/double-word
                 deriving (Eq, Show)

data ProcOrFunc   = FT_Proc | FT_Func  deriving (Show, Eq)
data RecStatus = YesRec | NotRec deriving (Eq, Ord, Show)
data VarNamespace = VarProc | VarLocal deriving Show
data TailQ = YesTail | NotTail deriving (Eq, Show)
data MayGC = GCUnknown String | MayGC | WillNotGC deriving (Eq, Show, Ord)
data SafetyGuarantee = SG_Static | SG_Dynamic | SG_Unsafe                   deriving (Show, Eq)
data ArrayIndex expr = ArrayIndex expr expr SourceRange
                                            SafetyGuarantee deriving (Show, Eq)

liftArrayIndexM f (ArrayIndex e1 e2 sr sg) = do
  e1' <- f e1 ; e2' <- f e2 ; return $ ArrayIndex e1' e2' sr sg

-- In contrast to meta type variables, the IORef for inferred types
-- can contain a sigma, not just a tau. See Typecheck.hs for details.
data Expected t = Infer (IORef t) | Check t

data TyVar = BoundTyVar  String SourceRange -- bound by a ForAll, that is
           | SkolemTyVar String Uniq Kind

data TypeFormal = TypeFormal String SourceRange Kind
typeFormalName (TypeFormal name _ _) = name

instance Eq  TypeFormal where (TypeFormal s1 _ k1) ==        (TypeFormal s2 _ k2) = (s1,k1) ==        (s2,k2)
instance Ord TypeFormal where (TypeFormal s1 _ k1) `compare` (TypeFormal s2 _ k2) = (s1,k1) `compare` (s2,k2)
instance Show TypeFormal where show (TypeFormal s _ k) = "(TypeFormal " ++ s ++ ":" ++ show k ++ ")"

convertTyFormal (TypeFormal name sr kind) = (BoundTyVar name sr, kind)

instance Kinded TypeFormal where
  kindOf (TypeFormal _ _ kind) = kind

instance Pretty TyVar where
  pretty (BoundTyVar name _) = text "'" <> text name
  pretty (SkolemTyVar name uniq _kind) = text "$" <> text name <> text ":" <> pretty uniq

data MTVQ = MTVSigma | MTVTau | MTVEffect deriving (Eq)
data MetaTyVar t = Meta { mtvConstraint :: MTVQ
                        , mtvDesc       :: String
                        , mtvUniq       :: Uniq
                        , mtvRef        :: IORef (Maybe t)
                        }

descMTVQ MTVSigma  = "S"
descMTVQ MTVTau    = "R"
descMTVQ MTVEffect = "E"

mtvIsEffect mtv = mtvConstraint mtv == MTVEffect

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
        | EP_Or           SourceRange [EPattern ty]

data PatternAtom ty =
          P_Wildcard      SourceRange ty
        | P_Variable      SourceRange (TypedId ty)
        | P_Bool          SourceRange ty Bool
        | P_Int           SourceRange ty LiteralInt

instance TypedWith (PatternAtom ty) ty where
  typeOf (P_Wildcard  _rng ty  ) = ty
  typeOf (P_Variable  _rng tid ) = tidType tid
  typeOf (P_Bool      _rng ty _) = ty
  typeOf (P_Int       _rng ty _) = ty

data Pattern ty =
          P_Atom         (PatternAtom ty)
        | P_Ctor          SourceRange ty [Pattern ty] (CtorInfo ty)
        | P_Tuple         SourceRange ty [Pattern ty]
        | P_Or            SourceRange ty [Pattern ty]

instance TypedWith (Pattern ty) ty where
 typeOf pattern = case pattern of
      P_Atom          atom -> typeOf atom
      P_Ctor  _rng ty _ _  -> ty
      P_Tuple _rng ty _    -> ty
      P_Or    _rng ty _    -> ty


data PatternRepr ty =
          PR_Atom         (PatternAtom ty)
        | PR_Ctor          SourceRange ty [PatternRepr ty] (LLCtorInfo ty)
        | PR_Tuple         SourceRange ty [PatternRepr ty]
        | PR_Or            SourceRange ty [PatternRepr ty]

instance TypedWith (PatternRepr ty) ty where
 typeOf pattern = case pattern of
      PR_Atom          atom -> typeOf atom
      PR_Ctor  _rng ty _ _  -> ty
      PR_Tuple _rng ty _    -> ty
      PR_Or    _rng ty _    -> ty

data PatternFlat ty =
          PF_Atom        (PatternAtom ty)
        | PF_Ctor         SourceRange ty [PatternAtom ty] (CtorInfo ty)
        | PF_Tuple        SourceRange ty [PatternAtom ty]

data CaseArm pat expr ty = CaseArm { caseArmPattern :: pat ty
                                   , caseArmBody    :: expr
                                   , caseArmGuard   :: Maybe expr
                                   , caseArmBindings:: [TypedId ty]
                                   , caseArmRange   :: SourceRange
                                   } deriving (Eq, Show)

caseArmExprs arm = [caseArmBody arm] ++ caseArmGuardList arm
  where
    caseArmGuardList (CaseArm _ _ Nothing  _ _) = []
    caseArmGuardList (CaseArm _ _ (Just e) _ _) = [e]

caseArmFreeIds arm =
  concatMap freeIdents (caseArmExprs arm) `butnot`
        map tidIdent  (caseArmBindings arm)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||| Data Types |||||||||||||||||||||||||||||||{{{
data DataType ty = DataType {
    dataTypeName      :: TypeFormal
  , dataTypeTyFormals :: [TypeFormal]
  , dataTypeCtors     :: [DataCtor ty]
  , dataTypeRange     :: SourceRange
  }

-- CtorIds are created before typechecking.
-- They are used to identify/disambiguate constructors.
data CtorId       = CtorId { ctorTypeName :: DataTypeName
                           , ctorCtorName :: String
                           , ctorArity    :: Int
                           } deriving (Show, Eq, Ord)

data DataCtor ty = DataCtor { dataCtorName  :: CtorName
                            , dataCtorDTTyF :: [TypeFormal]
                            , dataCtorTypes :: [ty]
                            , dataCtorRepr  :: Maybe CtorRepr
                            , dataCtorRange :: SourceRange
                            }

unDataCtorRepr :: Show ty => String -> DataCtor ty -> CtorRepr
unDataCtorRepr msg dc =
    case dataCtorRepr dc of
      Just repr -> repr
      Nothing -> error $ msg ++ "\n" ++ "Missing ctor repr for " ++ show dc

data CtorInfo ty = CtorInfo { ctorInfoId :: CtorId
                            , ctorInfoDc :: DataCtor ty
                            } deriving Show -- for Typecheck

-- We need to propagate the results of ctor analysis easily
-- to KNExpr (where we generate wrappers, which will be no-ops
-- for transparent constructors) and the backend (where we
-- will eventually implement occurrences as no-ops
-- for transparent constructors).

data LLCtorInfo ty = LLCtorInfo { ctorLLInfoId   :: CtorId
                                , ctorLLInfoRepr :: CtorRepr
                                , ctorLLInfoTys  :: [ty]
                                }
                     deriving (Show, Functor)

type CtorRep = (CtorId, CtorRepr)

type CtorName     = T.Text
type DataTypeName = String

data DataTypeSig  = DataTypeSig (Map CtorName CtorId)

-- Occurrences are generated in pattern matching (and pushed through to LLVM).
-- A pair (n, c) in an occurrence means "field n of the struct type for ctor c".
type FieldOfCtor ty = (Int, LLCtorInfo ty)
type Occurrence ty = [FieldOfCtor ty]

occType v occ = let
                   go ty [] [] = ty
                   go _ (k:offs) (tys:tyss)
                               = go (tys !! k) offs tyss
                   go ty offs tyss =
                        error $ "occType: " ++ show ty
                               ++ "; offs=" ++ show offs ++ "~~~" ++ show tyss

                   (offs, infos) = unzip occ
                in go (tidType v) offs (map ctorLLInfoTys infos)

-- Note that CtorRepr can only be created after typechecking,
-- because it depends on the result of kind (boxity) analysis.
--
data CtorRepr = CR_Default     Int -- tag via indirection through heap cell metadata
              | CR_Nullary     Int -- small integer stored in low tag bits of null pointer.
              | CR_Tagged      Int -- small integer stored in low tag bits of non-null pointer.
              | CR_Value   Integer -- no runtime indirection around given value (unboxed)
              | CR_Transparent     -- no runtime indirection around wrapped value (boxed)
              | CR_TransparentU    -- no runtime indirection around wrapped value (unboxed)
                deriving (Eq, Show, Ord)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||| Literals |||||||||||||||||||||||||||||||||{{{
data Literal = LitInt   LiteralInt
             | LitFloat LiteralFloat
             | LitText  T.Text
             | LitBool  Bool
             | LitByteArray B.ByteString
             deriving (Show, Eq)

data LiteralInt = LiteralInt { litIntValue   :: !Integer
                             , litIntMinBits :: !Int
                             , litIntText    :: !String
                             , litIntBase    :: !Int
                             } deriving (Show, Eq)

data LiteralFloat = LiteralFloat { litFloatValue   :: Double
                                 , litFloatText    :: String
                                 } deriving (Show, Eq)

powersOfTwo = [2^k | k <- [1..]]

mkLiteralIntWithTextAndBase integerValue originalText base =
  LiteralInt     integerValue activeBits originalText base
    where
        activeBits =
             if integerValue == -2147483648 then 32 -- handle edge cases directly
               else if integerValue == -9223372036854775808 then 64
                 else bitLengthOf (abs integerValue) + signOf integerValue
        bitLengthOf n = go 1 powersOfTwo where
                        go k (pow2k:pows) = if n < pow2k then k else go (k+1) pows
                        go _ [] = error "bitLengthOf invariant violated"
        signOf x = if x < 0 then 1 else 0

instance Pretty Literal where
  pretty (LitInt int) = red     $ text (litIntText int)
  pretty (LitFloat f) = dullred $ text (litFloatText f)
  pretty (LitText  t) =  dquotes (text $ T.unpack t)
  pretty (LitBool  b) =           text (if b then "True" else "False")
  pretty (LitByteArray b) = text "b" <> dquotes (text $ show b)

data WholeProgramAST expr ty = WholeProgramAST {
          programASTmodules    :: [ModuleAST expr ty]
     }

data ToplevelItem expr ty =
      ToplevelDecl (String, ty)
    | ToplevelDefn (String, expr ty)
    | ToplevelData (DataType ty)

data ModuleAST expr ty = ModuleAST {
          moduleASThash        :: String
        , moduleASTincludes    :: [ (T.Text, T.Text) ]
        , moduleASTitems       :: [ToplevelItem expr ty]
        , moduleASTsourceLines :: SourceLines
        , moduleASTprimTypes   :: [DataType ty]
     }

moduleASTdataTypes m = [dt | ToplevelData dt <- moduleASTitems m]
moduleASTdecls     m = [de | ToplevelDecl de <- moduleASTitems m]

data Fn rec expr ty
                = Fn { fnVar   :: TypedId ty
                     , fnVars  :: [TypedId ty]
                     , fnBody  :: expr
                     , fnIsRec :: rec
                     , fnAnnot :: ExprAnnot
                     } deriving Show -- For KNExpr and KSmallstep

fnType :: Fn r e t -> t
fnType fn = tidType $ fnVar fn

fnIdent fn = tidIdent $ fnVar fn

-- A function is recursive if any of the program-level identifiers
-- from the SCC it is bound in appears free in its body.
computeIsFnRec fn ids =
  if Set.null (setIntersectLists (freeIdents fn) ids) then NotRec else YesRec
         where setIntersectLists a b = Set.intersection (Set.fromList a)
                                                        (Set.fromList b)

data ModuleIL expr ty = ModuleIL {
          moduleILbody        :: expr
        , moduleILdecls       :: [(String, ty)]
        , moduleILdataTypes   :: [DataType ty]
        , moduleILprimTypes   :: [DataType ty]
        , moduleILsourceLines :: SourceLines
     }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||| Source Ranges ||||||||||||||||||||||||{{{

-- Note: sourceRangeLines is *all* lines, not just those in the range.
data SourceRange = SourceRange { sourceRangeStartLine :: !Int
                               , sourceRangeStartCol  :: !Int
                               , sourceRangeEndLine   :: !Int
                               , sourceRangeEndCol    :: !Int
                               , sourceRangeLines :: !SourceLines
                               , sourceRangeFile  :: !(Maybe String)
                               }
                  | MissingSourceRange String

instance Eq SourceRange where
  (MissingSourceRange s1) == (MissingSourceRange s2) = s1 == s2
  (SourceRange a b c d _ f1) == (SourceRange w x y z _ f2) = (a, b, c, d, f1) == (w, x, y, z, f2)
  _ == _ = False

class SourceRanged a
  where rangeOf :: a -> SourceRange

-- Used in ProtobufFE and Typecheck.hs.
rangeSpanOf :: SourceRanged a => SourceRange -> [a] -> SourceRange
rangeSpanOf defaultRange ranged =
    let ranges = map rangeOf ranged in
    rangeUnions defaultRange ranges

rangeUnions defaultRange allRanges = rsp defaultRange [r | r@(SourceRange _ _ _ _ _ _) <- allRanges]
  where rsp defaultRange [] = defaultRange
        rsp __ ranges@(b:_) = SourceRange (sourceRangeStartLine b)
                                          (sourceRangeStartCol  b)
                                          (sourceRangeEndLine $ last ranges)
                                          (sourceRangeEndCol  $ last ranges)
                                          (sourceRangeLines b)
                                          (sourceRangeFile  b)

sourceLineStart :: SourceRange -> String
sourceLineStart (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
sourceLineStart (SourceRange _ _ _ _ _lines Nothing) = "<unknown file>"
sourceLineStart (SourceRange bline bcol _ _ _lines (Just filepath)) =
    filepath ++ ":" ++ show bline ++ ":" ++ show bcol

prettyWithLineNumbers :: SourceRange -> Doc
prettyWithLineNumbers (MissingSourceRange s) = text $ "<missing range: " ++ s ++ ">"
prettyWithLineNumbers (SourceRange bline bcol eline ecol lines _filepath) =
        line <> showSourceLinesNumbered bline bcol eline ecol lines <> line

showSourceRange :: SourceRange -> String
showSourceRange (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
showSourceRange (SourceRange bline bcol eline ecol lines _filepath) =
         "\n" ++ showSourceLines bline bcol eline ecol lines ++ "\n"

prettySourceRangeInfo :: SourceRange -> Doc
prettySourceRangeInfo (MissingSourceRange s) = text $ "<missing range: " ++ s ++ ">"
prettySourceRangeInfo (SourceRange bline bcol _eline _ecol _lines mb_filepath) =
  let path = case mb_filepath of Nothing -> "<missing source file path>"
                                 Just fp -> fp in
  text path <> text ":" <> pretty (bline + 1) <> text ":" <> pretty bcol

highlightFirstLineDoc :: SourceRange -> Doc
highlightFirstLineDoc (MissingSourceRange s) = text $ "<missing range: " ++ s ++ ">"
highlightFirstLineDoc (SourceRange bline bcol eline ecol lines _filepath) =
    line <> highlightLineDoc bline bcol fcol lines <> line
      where fcol  = if bline == eline then ecol else Prelude.length lineb
            lineb = sourceLine lines bline

highlightFirstLine :: SourceRange -> String
highlightFirstLine (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
highlightFirstLine (SourceRange bline bcol eline ecol lines _filepath) =
    "\n" ++ highlightLine bline bcol fcol lines ++ "\n"
      where fcol  = if lineb == linee then ecol else Prelude.length lineb
            lineb = sourceLine lines bline
            linee = sourceLine lines eline

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
highlightLine line bcol ecol lines =
    joinWith "\n" [sourceLine lines line, highlightLineRange bcol ecol]

highlightLineDoc line bcol ecol lines =
    vcat [text $ sourceLine lines line, text $ highlightLineRange bcol ecol]

-- If a single line is specified, show it with highlighting;
-- otherwise, show the lines spanning the two locations (inclusive).
showSourceLines bline bcol eline ecol lines =
    if bline == eline
        then joinWith "\n" [sourceLine lines bline, highlightLineRange bcol ecol]
        else joinWith "\n" [sourceLine lines n | n <- [bline..eline]]

showSourceLinesNumbered bline bcol eline ecol lines =
    if bline == eline
        then vsep [sourceLineNumbered lines bline
                  ,lineNumberPadding <> text (highlightLineRange bcol ecol)]
        else vsep [sourceLineNumbered lines n | n <- [bline..eline]]

-- Generates a string of spaces and twiddles which underlines
-- a given range of characters.
highlightLineRange :: Int -> Int -> String
highlightLineRange bcol ecol =
    let len = ecol - bcol in
    if len <= 0
        then ""
        else (List.replicate bcol ' ') ++ (List.replicate len '~')

reprSourceRange (MissingSourceRange s) = text "(MissingSourceRange " <> text s <> text ")"
reprSourceRange (SourceRange bline bcol eline ecol _lines _filepath) =
  parens (text "SourceRange" <+> pretty bline <+> pretty bcol <+> pretty eline
                             <+> pretty ecol <+> pretty _filepath)

data SourceLines = SourceLines !(Seq T.Text)

appendSourceLines (SourceLines s1) (SourceLines s2) = SourceLines (s1 >< s2)

sourceLine :: SourceLines -> Int -> String
sourceLine (SourceLines seq) n =
    if n < 0 || Seq.length seq <= n
        then "<no line " ++ show n ++ " of "
                         ++ (show $ Seq.length seq) ++ ">"
        else (T.unpack $ Seq.index seq n)

sourceLineNumbered :: SourceLines -> Int -> Doc
sourceLineNumbered (SourceLines seq) n =
    fill 8 (pretty (n + 1) <> text ":") <> text (T.unpack $ Seq.index seq n)

lineNumberPadding = fill 8 PP.empty

data Formatting = Comment    {-SourceRange-} String
                | BlankLine
                deriving Show

data ExprAnnot = ExprAnnot
                        [Formatting] -- preceding comments and/or blank lines.
                        SourceRange  -- range of bare expr not incl. formatting.
                        [Formatting] -- trailing comments and/or blank lines.

annotForRange sr = ExprAnnot [] sr []

instance SourceRanged ExprAnnot where rangeOf (ExprAnnot _ rng _) = rng

instance Show ExprAnnot where show (ExprAnnot _ rng _) = show rng

data AllocationSource = AllocationSource String SourceRange deriving (Show, Eq)


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

concatMapM f vs = do vs' <- mapM f vs ; return $ concat vs'

mapMaybeM _ Nothing = return Nothing
mapMaybeM f (Just x) = f x >>= return . Just

-- | Does what it says on the tin: monadic foldl'
foldlM :: (Monad m) => (a -> b -> m a) -> a -> [b] -> m a
foldlM _ a      [] = return a
foldlM f a1 (b:bs) = do
    a2  <- f a1 b
    foldlM f a2 bs

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

(|>) :: a -> (a -> b) -> b
x |> f = f x

infixl 1 |>

removeDuplicates :: Ord a => [a] -> [a]
removeDuplicates xs = xs |> Set.fromList |> Set.toList

detectDuplicates :: Ord a => [a] -> [a]
detectDuplicates xs = go xs Set.empty Set.empty
  where go []    _seen dups = Set.toList dups
        go (x:xs) seen dups =
          if Set.member x seen then go xs seen (Set.insert x dups)
                               else go xs (Set.insert x seen) dups


newtype CDPair a b = CDPair (a, b)
instance Ord b => Ord (CDPair a b) where
  compare (CDPair (_, b1)) (CDPair (_, b2)) = compare b1 b2

instance Eq b => Eq (CDPair a b) where
  (==) (CDPair (_, b1)) (CDPair (_, b2)) = (==) b1 b2

-- Returns a list of lists-of-duplicates (in unspecified order).
-- For example, collectDuplicatesBy id [1,2,3,2,1]
--                    woudld be (equiv to) [[1,1],[2,2]]
collectDuplicatesBy :: Ord b => (a -> b) -> [a] -> [[a]]
collectDuplicatesBy f items =
  let pairs = [CDPair (a, f a) | a <- items] in
  let dupPairs = detectDuplicates pairs in
  let itemsEquivTo b = [x | CDPair (x, y) <- pairs, b == y] in
  [ itemsEquivTo b | CDPair (_, b) <- dupPairs]

joinWith :: String -> [String] -> String
joinWith _ [] = ""
joinWith s ss = foldr1 (++) (intersperse s ss)

prependedTo :: String -> T.Text -> T.Text
prependedTo str txt = T.pack str `T.append` txt

-- Re-implement strict version of modifyIORef for compatibility with
-- older implementations of the Haskell base library.
modIORef' r f = do
  v <- readIORef r
  let ! v' = f v
  writeIORef r v'

liftMaybe :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
liftMaybe _ Nothing = return Nothing
liftMaybe f (Just a) = do b <- f a ; return $ Just b

-- Like Map.fromList, but retains every value.
mapAllFromList :: Ord k => [(k, a)] -> Map k [a]
mapAllFromList pairs =
  Map.fromListWith (++) (map (\(k,a) -> (k, [a])) pairs)

data ArrayEntry e = AE_Int ExprAnnot String
                  | AE_Expr e
                  deriving Show

liftArrayEntryM :: Monad m => (a -> m b) -> ArrayEntry a -> m (ArrayEntry b)
liftArrayEntryM action ei =
  case ei of AE_Int a s -> return (AE_Int a s)
             AE_Expr e  -> action e >>= return . AE_Expr

mapRight :: (a -> b) -> [Either x a] -> [Either x b]
mapRight action lst = map (\ei -> case ei of Left x -> Left x
                                             Right a -> Right $ action a) lst

mapRightM :: Monad m => (a -> m b) -> [Either x a] -> m [Either x b]
mapRightM action lst = mapM (\ei -> case ei of Left x -> return (Left x)
                                               Right a -> action a >>= return . Right) lst

zipTogether :: [a] -> [b] -> [(Maybe a, Maybe b)]
zipTogether []     []     = []
zipTogether (x:xs) []     = (Just x, Nothing) : zipTogether xs []
zipTogether []     (y:ys) = (Nothing, Just y) : zipTogether [] ys
zipTogether (x:xs) (y:ys) = (Just x,  Just y) : zipTogether xs ys

whenNotM cond action = do b <- cond ; if b then return () else action
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||||| Idents |||||||||||||||||||||||||||{{{

identPrefix :: Ident -> T.Text
identPrefix (GlobalSymbol name) = name
identPrefix (Ident name _)      = name

data Ident = Ident        T.Text Uniq
           | GlobalSymbol T.Text

fmapIdent :: (T.Text -> T.Text) -> Ident -> Ident
fmapIdent tt (Ident t u)      = Ident        (tt t) u
fmapIdent tt (GlobalSymbol t) = GlobalSymbol (tt t)

data TypedId ty = TypedId { tidType :: ty, tidIdent :: Ident }

data FosterPrim ty = NamedPrim (TypedId ty) -- invariant: global symbol
                   | PrimOp { ilPrimOpName :: String
                            , ilPrimOpType :: ty }
                   | PrimIntTrunc IntSizeBits IntSizeBits -- from, to
                   | CoroPrim  CoroPrim ty ty
                   | PrimInlineAsm ty T.Text T.Text Bool

data CoroPrim = CoroCreate | CoroInvoke | CoroYield deriving (Show, Eq)

-- TODO distinguish stable pointers from lively pointers?
--      stable-pointer-bit at compile time or runtime?
-- TODO other allocation zones? -- refcounted heap, thread-local heap,
--                                 C/malloc/free heap,
--                                 type-specific heaps, etc, etc...
data AllocMemRegion = MemRegionStack
                    | MemRegionGlobalData
                    | MemRegionGlobalHeap deriving (Show, Eq)

memRegionMayGC :: AllocMemRegion -> MayGC
memRegionMayGC MemRegionStack = WillNotGC
memRegionMayGC MemRegionGlobalHeap = MayGC
memRegionMayGC MemRegionGlobalData = WillNotGC

data AllocInfo t = AllocInfo { allocType      :: t
                             , allocRegion    :: AllocMemRegion
                             , allocTypeName  :: String
                             , allocCtorRepr  :: Maybe CtorRepr
                             , allocArraySize :: Maybe (TypedId t)
                             , allocSite      :: String
                             , allocZeroInit  :: ZeroInit
                             }

data ZeroInit = DoZeroInit | NoZeroInit deriving (Show, Eq)

type MayGCConstraint = (MayGC -- at most one direct constraint
                       ,Set.Set Ident) --any # of indirect constraints
type MayGCConstraints = Map Ident MayGCConstraint

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- {{{ Split up a sequence of function bindings into minimal SCCs.
mkFunctionSCCs :: AExpr fn => [Ident] -> [fn] -> expr ->
                             ([Ident] -> [fn] -> expr -> expr) -> expr
mkFunctionSCCs ids fns body k =
  let idset    = Set.fromList ids
      fnids fn = Set.toList $ Set.intersection (Set.fromList (freeIdents fn))
                                               idset
      callGraphList = map (\(id, fn) -> ((fn, id), id, fnids fn)) (zip ids fns)
      theSCCs       = Graph.stronglyConnComp callGraphList
  in foldr (\scc body ->
          let mkFuns ids fns = k ids fns body in
          case scc of
                Graph.AcyclicSCC (fn, id) -> mkFuns [id] [fn]
                Graph.CyclicSCC fnids ->     mkFuns ids fns
                                              where (fns, ids) = unzip fnids
         ) body theSCCs
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||||| Instance Helpers |||||||||||||||||||{{{
caseArmFreeVars (CaseArm epat body guard _ _) =
  (freeVars body ++ freeVars guard) `butnot` epatBoundNames epat

epatBoundNames :: EPattern ty -> [T.Text]
epatBoundNames epat =
  case epat of
    EP_Wildcard {}        -> []
    EP_Variable _rng evar -> [evarName evar]
    EP_Ctor     _r pats _ -> concatMap epatBoundNames pats
    EP_Bool     {}        -> []
    EP_Int      {}        -> []
    EP_Or       _rng pats -> concatMap epatBoundNames pats |> removeDuplicates
    EP_Tuple    _rng pats -> concatMap epatBoundNames pats
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||||| Instances ||||||||||||||||||||||||||{{{
instance Expr expr => Expr (CaseArm EPattern expr ty) where
  freeVars = caseArmFreeVars

instance Expr e => Expr (Maybe e) where
  freeVars Nothing = []
  freeVars (Just e) = freeVars e

instance Expr (EPattern ty) where
  freeVars = epatBoundNames

instance AExpr body => AExpr (Fn recStatus body t) where
    freeIdents f = let bodyvars =  freeIdents (fnBody f) in
                   let boundvars =  map tidIdent (fnVars f) in
                   bodyvars `butnot` boundvars

instance IntSized IntSizeBits
 where
       intSizeOf I1 = 1
       intSizeOf I8 = 8
       intSizeOf I16 = 16
       intSizeOf I32 = 32
       intSizeOf I64 = 64
       intSizeOf IWd = 32 -- TODO this is hacky =/
       intSizeOf IDw = 64

sizeOfBits :: Int -> IntSizeBits
sizeOfBits 1           = I1
sizeOfBits n | n <= 8  = I8
sizeOfBits n | n <= 16 = I16
sizeOfBits n | n <= 32 = I32
sizeOfBits n | n <= 64 = I64
sizeOfBits n = error $ "TypecheckInt.hs:sizeOfBits: Unsupported size: " ++ show n

instance Pretty IntSizeBits    where pretty IWd = text "Word"
                                     pretty IDw = text "WordX2"
                                     pretty I1 = text "Bool"
                                     pretty i  = text ("Int" ++ show (intSizeOf i))
instance Pretty Ident          where pretty id = text (show id)
instance Pretty t => Pretty (TypedId t)
                               where pretty tid = pretty (tidIdent tid)
instance SourceRanged expr => Pretty (CompilesResult expr)
                               where pretty cr = text (show cr)

instance SourceRanged (Fn r e t) where rangeOf fn = rangeOf (fnAnnot fn)

instance SourceRanged (EPattern ty) where
  rangeOf epat =
    case  epat  of
          EP_Wildcard     rng     -> rng
          EP_Variable     rng _   -> rng
          EP_Ctor         rng _ _ -> rng
          EP_Bool         rng _ -> rng
          EP_Int          rng _ -> rng
          EP_Tuple        rng _ -> rng
          EP_Or           rng _ -> rng

deriving instance (Show ty) => Show (DataType ty)
deriving instance (Show ty) => Show (DataCtor ty)

instance Ord Ident where compare = compareIdents

-- Give a distinct name to the Ord instance so that profiles get a more informative name.
compareIdents (GlobalSymbol t1) (GlobalSymbol t2) = compare t1 t2
compareIdents (Ident t1 u1)     (Ident t2 u2)     = case compare u1 u2 of
                                                      EQ -> let rv = compare t1 t2 in
                                                            if rv == EQ then rv else
                                                                error $ "Uniq ident failure! " ++ show ((Ident t1 u1) ,  (Ident t2 u2) )
                                                      cr -> cr
compareIdents (GlobalSymbol _)  (Ident _  _ )     = LT
compareIdents (Ident _ _)       (GlobalSymbol  _) = GT

instance Eq Ident where
    (GlobalSymbol t1) == (GlobalSymbol t2) = t1 == t2
    (Ident t1 u1)     == (Ident t2 u2) = u1 == u2 && t1 == t2
    _ == _ = False

instance Show Ident where
    show (Ident name number) = T.unpack name ++ "!" ++ show number
    show (GlobalSymbol name) = T.unpack name

instance Eq (TypedId t) where
       (==) (TypedId _ a) (TypedId _ b) = (==) a b

instance Ord (TypedId t) where
    compare (TypedId _ a) (TypedId _ b) = compareIdents a b

instance (Show ty) => Show (TypedId ty)
  where show (TypedId ty id) = show id ++ " :: " ++ show ty

instance Eq TyVar where
  BoundTyVar s1 _    == BoundTyVar s2 _    = s1 == s2
  SkolemTyVar _ u1 _ == SkolemTyVar _ u2 _ = u1 == u2
  _ == _ = False

instance Ord TyVar where
  BoundTyVar s1 _    `compare` BoundTyVar s2 _    = s1 `compare` s2
  SkolemTyVar _ u1 _ `compare` SkolemTyVar _ u2 _ = u1 `compare` u2
  BoundTyVar s1 _    `compare` SkolemTyVar s2 _ _ = s1 `compare` s2
  SkolemTyVar s1 _ _ `compare` BoundTyVar s2 _    = s1 `compare` s2

prettyOccurrence v occ = pretty v <> text "/" <> pretty (map fst occ)

instance Show TyVar where
    show (BoundTyVar x _) = "'" ++ x
    show (SkolemTyVar x u k) = "$" ++ x ++ "." ++ show u ++ "::" ++ show k

instance Show SourceRange where
    show _ = "<...source range...>"

instance (SourceRanged expr) => Show (CompilesResult expr) where
  show (CompilesResult (OK e))     = show (rangeOf e)
  show (CompilesResult (Errors _)) = "<...invalid term...>"

instance Show (PatternAtom ty) where
  show (P_Wildcard _ _)            = "P_Wildcard"
  show (P_Variable _ v)            = "P_Variable " ++ show (tidIdent v)
  show (P_Bool     _ _ b)          = "P_Bool     " ++ show b
  show (P_Int      _ _ i)          = "P_Int      " ++ show (litIntText i)

instance Show (Pattern ty) where
  show (P_Atom atom) = show atom
  show (P_Ctor     _ _ _pats ctor) = "P_Ctor     " ++ show (ctorInfoId ctor)
  show (P_Tuple    _ _ pats)       = "P_Tuple    " ++ show pats
  show (P_Or       _ _ pats)       = "P_Or       " ++ show pats

instance Show (PatternFlat ty) where
  show (PF_Atom atom) = show atom
  show (PF_Ctor     _ _ _pats ctor) = "PF_Ctor     " ++ show (ctorInfoId ctor)
  show (PF_Tuple    _ _ pats)       = "PF_Tuple    " ++ show pats

instance Show (PatternRepr ty) where
  show (PR_Atom atom) = show atom
  show (PR_Ctor     _ _ _pats ctor) = "PR_Ctor     " ++ show (ctorLLInfoId ctor)
  show (PR_Tuple    _ _ pats)       = "PR_Tuple    " ++ show pats
  show (PR_Or       _ _ pats)       = "PR_Or       " ++ show pats

instance Pretty t => Pretty (Pattern t) where
  pretty p =
    case p of
        P_Atom          atom              -> pretty atom
        P_Ctor          _rng _ty pats cid -> parens (text "$" <> text (ctorCtorName $ ctorInfoId cid) <+> (hsep $ map pretty pats))
        P_Tuple         _rng _ty pats     -> parens (hsep $ punctuate comma (map pretty pats))
        P_Or            _rng _ty pats     -> parens (hsep $ punctuate (text " or ") (map pretty pats))

instance Pretty t => Pretty (PatternAtom t) where
  pretty p =
    case p of
        P_Wildcard      _rng _ty          -> text "_"
        P_Variable      _rng tid          -> text (show . tidIdent $ tid)
        P_Bool          _rng _ty b        -> text $ if b then "True" else "False"
        P_Int           _rng _ty li       -> text (litIntText li)

instance Pretty t => Pretty (PatternRepr t) where
  pretty p =
    case p of
        PR_Atom          atom              -> pretty atom
        PR_Ctor          _rng _ty pats cid -> parens (text "$" <> text (ctorCtorName $ ctorLLInfoId cid) <+> (hsep $ map pretty pats))
        PR_Tuple         _rng _ty pats     -> parens (hsep $ punctuate comma (map pretty pats))
        PR_Or            _rng _ty pats     -> parens (hsep $ punctuate (text " or ") (map pretty pats))

instance Show ty => Show (EPattern ty) where
  show (EP_Wildcard _)            = "EP_Wildcard"
  show (EP_Variable _ v)          = "EP_Variable " ++ show v
  show (EP_Ctor     _ _pats ctor) = "EP_Ctor     " ++ show ctor
  show (EP_Bool     _ b)          = "EP_Bool     " ++ show b
  show (EP_Int      _ str)        = "EP_Int      " ++ str
  show (EP_Tuple    _ pats)       = "EP_Tuple    " ++ show pats
  show (EP_Or       _ pats)       = "EP_Or       " ++ show pats

instance Pretty ty => Pretty (EPattern ty) where
  pretty (EP_Wildcard _)            = text "_"
  pretty (EP_Variable _ v)          = pretty v
  pretty (EP_Ctor     _ pats ctor)  = text "$" <> text (T.unpack ctor) <+> hsep (map pretty pats)
  pretty (EP_Bool     _ b)          = pretty b
  pretty (EP_Int      _ str)        = text str
  pretty (EP_Tuple    _ pats)       = tupled $ map pretty pats
  pretty (EP_Or       _ pats)       = parens (hsep $ punctuate (text " or ") (map pretty pats))

instance Pretty ty => Pretty (E_VarAST ty) where
  pretty (VarAST (Just ty) txt) = text (T.unpack txt) <+> text "::" <+> pretty ty
  pretty (VarAST Nothing   txt) = text (T.unpack txt)

instance Pretty t => Pretty (FosterPrim t) where
  pretty (NamedPrim (TypedId _ i)) = text (show i)
  pretty (PrimOp nm _ty) = text nm
  pretty (PrimIntTrunc frm to) = text ("trunc from " ++ show frm ++ " to " ++ show to)
  pretty (CoroPrim c t1 t2) = pretty c <> text ":[" <> pretty t1
                                       <> text "," <+> pretty t2
                                       <> text "]"
  pretty (PrimInlineAsm _ cnt _cns _haseffects) = text "inline-asm" <+> text (show cnt)

instance Pretty CoroPrim where
  pretty CoroCreate = text "CoroCreate"
  pretty CoroInvoke = text "CoroInvoke"
  pretty CoroYield  = text "CoroYield"

instance Pretty CtorId where
  pretty (CtorId tynm ctnm sm) = pretty tynm <> text "." <> pretty ctnm <> parens (pretty sm)

instance Pretty CtorRepr where
  pretty (CR_Default int) = text "#" <> pretty int
  pretty (CR_Tagged  int) = text "#" <> pretty int
  pretty (CR_Transparent)  = text "#" <> text "~"
  pretty (CR_TransparentU) = text "#{}"
  pretty (CR_Nullary int) = text "##" <> pretty int <> text "~"
  pretty (CR_Value   int) = text "##" <> pretty int

instance TExpr body t => TExpr (Fn rec body t) t where
    freeTypedIds f = let bodyvars =  freeTypedIds (fnBody f) in
                     let boundvars =              (fnVars f) in
                     bodyvars `butnot` boundvars

instance Pretty Kind where
  pretty KindAnySizeType  = text "Type"
  pretty KindPointerSized = text "Boxed"
  pretty KindEffect       = text "Effect"

instance Pretty TypeFormal where
  pretty (TypeFormal name _sr kind) =
    text name <+> text ":" <+> pretty kind

instance Pretty t => Pretty (DataType t) where
  pretty dt =
    text "type case" <+> pretty (dataTypeName dt) <+>
         hsep (map (parens . pretty) (dataTypeTyFormals dt))
     <$> indent 2 (vsep (map prettyDataTypeCtor (dataTypeCtors dt)))
     <$> text ";"
     <$> text ""

prettyDataTypeCtor dc =
  text "of" <+> text "$" <> text (T.unpack $ dataCtorName dc)
                        <+> hsep (map pretty (dataCtorTypes dc))
                        <+> text "// repr:" <+> text (show (dataCtorRepr dc))

prettyCase :: (Pretty expr, Pretty (pat ty)) => expr -> [CaseArm pat expr ty] -> Doc
prettyCase scrutinee arms =
            kwd "case" <+> pretty scrutinee
            <$> indent 2 (vcat [ kwd "of" <+>
                                        (hsep $ [{- fill 20 -} (pretty epat)]
                                            ++  prettyGuard guard
                                            ++ [text "->" <+> pretty body])
                              | (CaseArm epat body guard _ _) <- arms
                              ])
            <$> end
  where
    prettyGuard Nothing  = []
    prettyGuard (Just e) = [text "if" <+> pretty e]
    kwd  s = dullblue  (text s)
    lkwd s = dullwhite (text s)
    end    = lkwd "end"

instance TExpr (ArrayIndex (TypedId t)) t where
   freeTypedIds (ArrayIndex v1 v2 _ _) = [v1, v2]

deriving instance (Show ty) => Show (AllocInfo ty)
deriving instance (Eq ty)   => Eq   (AllocInfo ty)
deriving instance (Show ty) => Show (FosterPrim ty)
deriving instance (Eq ty)   => Eq   (FosterPrim ty)
deriving instance (Show ty) => Show (E_VarAST ty)
deriving instance (Eq ty)   => Eq   (DataCtor ty)

instance Eq (CtorInfo t) where
  a == b = (ctorInfoId a) == (ctorInfoId b)

instance Ord (LLCtorInfo ty) where
  compare = compareLLCtorInfo

compareLLCtorInfo (LLCtorInfo c1 r1 _) (LLCtorInfo c2 r2 _) = compare (c1, r1) (c2, r2)

instance Eq  (LLCtorInfo ty) where
  c1 == c2 = compare c1 c2 == EQ

instance Eq Doc where d1 == d2 = pretty d1 == pretty d2

deriving instance (Eq ty) => Eq (PatternAtom ty)
deriving instance (Eq ty) => Eq (CompilesResult ty)
deriving instance (Eq ty) => Eq (OutputOr ty)
deriving instance (Eq ty) => Eq (Pattern ty)
deriving instance (Eq ty, Eq expr) => Eq (Fn () expr ty)
deriving instance Eq ExprAnnot
deriving instance Eq Formatting

deriving instance Functor PatternAtom
deriving instance Functor PatternRepr
deriving instance Functor PatternFlat
deriving instance Functor Pattern
deriving instance Functor TypedId
deriving instance Functor AllocInfo
deriving instance Functor FosterPrim
deriving instance Functor CtorInfo
deriving instance Functor DataCtor
deriving instance Functor DataType
deriving instance Functor ArrayIndex
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

