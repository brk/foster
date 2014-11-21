{-# LANGUAGE GADTs , StandaloneDeriving, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Base where

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
data IntSizeBits = I1 | I8 | I32 | I64
                 | IWord LogInt -- Word 3 means 8x larger; -2 is 4x smaller.
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

data TyVar = BoundTyVar  String -- bound by a ForAll, that is
           | SkolemTyVar String Uniq Kind

convertTyFormal (TypeFormal name kind) = (BoundTyVar name, kind)

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

typeFormalName (TypeFormal name _) = name

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

instance TypedWith (Pattern ty) ty where
 typeOf pattern = case pattern of
      P_Atom          atom -> typeOf atom
      P_Ctor  _rng ty _ _  -> ty
      P_Tuple _rng ty _    -> ty


data PatternRepr ty =
          PR_Atom         (PatternAtom ty)
        | PR_Ctor          SourceRange ty [PatternRepr ty] (LLCtorInfo ty)
        | PR_Tuple         SourceRange ty [PatternRepr ty]

instance TypedWith (PatternRepr ty) ty where
 typeOf pattern = case pattern of
      PR_Atom          atom -> typeOf atom
      PR_Ctor  _rng ty _ _  -> ty
      PR_Tuple _rng ty _    -> ty

data PatternFlat ty =
          PF_Atom        (PatternAtom ty)
        | PF_Ctor         SourceRange ty [PatternAtom ty] (CtorInfo ty)
        | PF_Tuple        SourceRange ty [PatternAtom ty]

data CaseArm pat expr ty = CaseArm { caseArmPattern :: pat ty
                                   , caseArmBody    :: expr
                                   , caseArmGuard   :: Maybe expr
                                   , caseArmBindings:: [TypedId ty]
                                   , caseArmRange   :: SourceRange
                                   } deriving Show

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
                            , dataCtorRange :: SourceRange
                            }

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
        signOf x = if x < 0 then 1 else 0

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

instance Eq SourceRange where
  (MissingSourceRange s1) == (MissingSourceRange s2) = s1 == s2
  (SourceRange b1 e1 _ f1) == (SourceRange b2 e2 _ f2) = (b1, e1, f1) == (b2, e2, f2)
  _ == _ = False

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

sourceLineStart :: SourceRange -> String
sourceLineStart (MissingSourceRange s) = "<missing range: " ++ s ++ ">"
sourceLineStart (SourceRange _begin _end _lines Nothing) = "<unknown file>"
sourceLineStart (SourceRange begin _end _lines (Just filepath)) =
    filepath ++ ":" ++ show (sourceLocationLine begin)

prettyWithLineNumbers :: SourceRange -> Doc
prettyWithLineNumbers (MissingSourceRange s) = text $ "<missing range: " ++ s ++ ">"
prettyWithLineNumbers (SourceRange begin end lines _filepath) =
        line <> showSourceLinesNumbered begin end lines <> line

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

showSourceLinesNumbered (ESourceLocation bline bcol) (ESourceLocation eline ecol) lines =
    if bline == eline
        then vsep [sourceLineNumbered lines bline, text $ highlightLineRange bcol ecol]
        else vsep [sourceLineNumbered lines n | n <- [bline..eline]]


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

sourceLineNumbered :: SourceLines -> Int -> Doc
sourceLineNumbered (SourceLines seq) n =
    pretty (n + 1) <> text ":" <> text "    " <> text (T.unpack $ Seq.index seq n)

data Formatting = Comment    {-SourceRange-} String
                | BlankLine
                | NonHidden
                deriving Show

data ExprAnnot = ExprAnnot
                        [Formatting] -- preceding comments and/or blank lines.
                        SourceRange  -- range of bare expr not incl. formatting.
                        [Formatting] -- trailing comments and/or blank lines.

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

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||||| Idents |||||||||||||||||||||||||||{{{

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
                    | MemRegionGlobalHeap deriving (Show, Eq)

memRegionMayGC :: AllocMemRegion -> MayGC
memRegionMayGC MemRegionStack = WillNotGC
memRegionMayGC MemRegionGlobalHeap = MayGC

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
-- ||||||||||||||||||||||||| Instances ||||||||||||||||||||||||||{{{

instance AExpr body => AExpr (Fn recStatus body t) where
    freeIdents f = let bodyvars =  freeIdents (fnBody f) in
                   let boundvars =  map tidIdent (fnVars f) in
                   bodyvars `butnot` boundvars

instance IntSized IntSizeBits
 where intSizeOf = intOfSize where
                       intOfSize I1 = 1
                       intOfSize I8 = 8
                       intOfSize I32 = 32
                       intOfSize I64 = 64
                       intOfSize (IWord 0) = 32 -- TODO this is hacky =/
                       intOfSize (IWord 1) = 64
                       intOfSize (IWord w) = error $ "unsupported IWord key " ++ show w

sizeOfBits :: Int -> IntSizeBits
sizeOfBits 1           = I1
sizeOfBits n | n <= 8  = I8
sizeOfBits n | n <= 32 = I32
sizeOfBits n | n <= 64 = I64
sizeOfBits n = error $ "TypecheckInt.hs:sizeOfBits: Unsupported size: " ++ show n

instance Pretty IntSizeBits    where pretty (IWord 0) = text "Word"
                                     pretty (IWord 1) = text "WordX2"
                                     pretty I1 = text "Bool"
                                     pretty i  = text ("Int" ++ show (intSizeOf i))
instance Pretty Ident          where pretty id = text (show id)
instance Pretty t => Pretty (TypedId t)
                               where pretty tid = pretty (tidIdent tid)
instance SourceRanged expr => Pretty (CompilesResult expr)
                               where pretty cr = text (show cr)

instance SourceRanged (Fn r e t) where rangeOf fn = rangeOf (fnAnnot fn)

deriving instance (Show ty) => Show (DataType ty)
deriving instance (Show ty) => Show (DataCtor ty)

instance Ord Ident where
    compare (GlobalSymbol t1) (GlobalSymbol t2) = compare t1 t2
    compare (Ident t1 u1)     (Ident t2 u2)     = case compare u1 u2 of
                                                    EQ -> compare t1 t2
                                                    cr -> cr
    compare (GlobalSymbol _)  (Ident _  _ )     = LT
    compare (Ident _ _)       (GlobalSymbol  _) = GT

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

instance Show (PatternAtom ty) where
  show (P_Wildcard _ _)            = "P_Wildcard"
  show (P_Variable _ v)            = "P_Variable " ++ show (tidIdent v)
  show (P_Bool     _ _ b)          = "P_Bool     " ++ show b
  show (P_Int      _ _ i)          = "P_Int      " ++ show (litIntText i)

instance Show (Pattern ty) where
  show (P_Atom atom) = show atom
  show (P_Ctor     _ _ _pats ctor) = "P_Ctor     " ++ show (ctorInfoId ctor)
  show (P_Tuple    _ _ pats)       = "P_Tuple    " ++ show pats

instance Show (PatternFlat ty) where
  show (PF_Atom atom) = show atom
  show (PF_Ctor     _ _ _pats ctor) = "PF_Ctor     " ++ show (ctorInfoId ctor)
  show (PF_Tuple    _ _ pats)       = "PF_Tuple    " ++ show pats

instance Show (PatternRepr ty) where
  show (PR_Atom atom) = show atom
  show (PR_Ctor     _ _ _pats ctor) = "PR_Ctor     " ++ show (ctorLLInfoId ctor)
  show (PR_Tuple    _ _ pats)       = "PR_Tuple    " ++ show pats

instance Pretty t => Pretty (Pattern t) where
  pretty p =
    case p of
        P_Atom          atom              -> pretty atom
        P_Ctor          _rng _ty pats cid -> parens (text "$" <> text (ctorCtorName $ ctorInfoId cid) <+> (hsep $ map pretty pats))
        P_Tuple         _rng _ty pats     -> parens (hsep $ punctuate comma (map pretty pats))

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
  pretty (CoroPrim c t1 t2) = pretty c <> text ":[" <> pretty t1
                                       <> text "," <+> pretty t2
                                       <> text "]"
  pretty (PrimInlineAsm _ cnt _cns _haseffects) = text "inline-asm" <+> text (show cnt)

instance Pretty CoroPrim where
  pretty CoroCreate = text "CoroCreate"
  pretty CoroInvoke = text "CoroInvoke"
  pretty CoroYield  = text "CoroYield"

instance Show ty => Show (EPattern ty) where
  show (EP_Wildcard _)            = "EP_Wildcard"
  show (EP_Variable _ v)          = "EP_Variable " ++ show v
  show (EP_Ctor     _ _pats ctor) = "EP_Ctor     " ++ show ctor
  show (EP_Bool     _ b)          = "EP_Bool     " ++ show b
  show (EP_Int      _ str)        = "EP_Int      " ++ str
  show (EP_Tuple    _ pats)       = "EP_Tuple    " ++ show pats

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
  compare (LLCtorInfo c1 r1 _) (LLCtorInfo c2 r2 _) = compare (c1, r1) (c2, r2)
instance Eq  (LLCtorInfo ty) where
  c1 == c2 = compare c1 c2 == EQ

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

