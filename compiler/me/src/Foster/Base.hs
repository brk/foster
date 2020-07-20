{-# LANGUAGE GADTs , StandaloneDeriving, BangPatterns, Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Base where

import Prelude hiding ((<$>))

import Foster.Kind
import Foster.Output
import Foster.SourceRange(SourceLines, SourceRange, SourceRanged, rangeOf)

import Data.IORef(IORef, readIORef, writeIORef)
import qualified Data.Set as Set(empty)
import Data.Set as Set(fromList, toList, difference, insert, member,
                        null, intersection)
import Data.List as List(intercalate)
import Data.Map as Map(Map, fromListWith)
import Data.Set as Set(Set, unions)
import Data.Sequence as Seq(Seq)
import qualified Data.Graph as Graph(SCC(..), stronglyConnComp)

import qualified Data.Foldable as Foldable(toList)

import qualified Data.Text.Prettyprint.Doc as PP(emptyDoc, list)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal

import qualified Data.Text as T(Text, pack, unpack, append, length)
import qualified Data.Text.Lazy as TL
import qualified Data.ByteString as B(ByteString)

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

class Expr a where
    freeVars   :: a -> [T.Text]

class AExpr a where
    freeIdents   :: a -> Set Ident

class TExpr a t where
    freeTypedIds   :: a -> [TypedId t]

class TypedWith a t where
    typeOf :: a -> t

class IntSized t where
    intSizeOf :: t -> Int

class IntSizedBits t where
    intSizeBitsOf :: t -> IntSizeBits

class PrettyT t where
    prettyT :: t -> Doc AnsiStyle

-- |||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
data CompilesResult expr = CompilesResult (OutputOr expr)
type Uniq = Int
data CallConv = CCC | FastCC deriving (Eq, Show, Ord)
type LogInt = Int
data IntSizeBits = I1 | I8 | I16 | I32 | I64 | IWd | IDw -- Word/double-word
                 deriving (Eq, Show, Ord)
data CallAnnot = CA_None
               | CA_DoInline
               | CA_NoInline deriving (Eq, Show, Ord)
data ProcOrFunc   = FT_Proc | FT_Func  deriving (Show, Eq)
data RecStatus = YesRec | NotRec deriving (Eq, Ord, Show)
data TailQ = YesTail | NotTail deriving (Eq, Show)
data SafetyGuarantee = SG_Static | SG_Dynamic | SG_Unsafe   deriving (Show, Eq)
data ArrayIndex expr = ArrayIndex expr expr SourceRange
                                            SafetyGuarantee deriving (Show, Eq)

liftArrayIndexM f (ArrayIndex e1 e2 sr sg) = do
  e1' <- f e1 ; e2' <- f e2 ; return $ ArrayIndex e1' e2' sr sg

-- In contrast to meta type variables, the IORef for inferred types
-- can contain a sigma, not just a tau. See Typecheck.hs for details.
data Expected t = Infer (IORef t) | Check t

data TyVar = BoundTyVar  T.Text SourceRange -- bound by a ForAll, that is
           | SkolemTyVar T.Text Uniq Kind

data TypeFormal = TypeFormal T.Text SourceRange Kind
typeFormalName (TypeFormal name _ _) = name

instance Eq  TypeFormal where (TypeFormal s1 _ k1) ==        (TypeFormal s2 _ k2) = (s1,k1) ==        (s2,k2)
instance Ord TypeFormal where (TypeFormal s1 _ k1) `compare` (TypeFormal s2 _ k2) = (s1,k1) `compare` (s2,k2)
instance Show TypeFormal where show (TypeFormal s _ k) = "(TypeFormal " ++ T.unpack s ++ ":" ++ show k ++ ")"

convertTyFormal (TypeFormal name sr kind) = (BoundTyVar name sr, kind)

instance Kinded TypeFormal where
  kindOf (TypeFormal _ _ kind) = kind

instance Pretty TyVar where
  pretty = prettyDecorated

prettySrc (BoundTyVar name _) = text name
prettySrc (SkolemTyVar name uniq _kind) = text "$" <> text name <> text ":" <> pretty uniq

prettyDecorated (BoundTyVar name _) = text "'" <> text name
prettyDecorated (SkolemTyVar name uniq _kind) = text "$" <> text name <> text ":" <> pretty uniq

instance PrettyT t => PrettyT (MetaTyVar t) where
  prettyT m = parens $ text (mtvDesc m) <> text "~" <> string (show (mtvUniq m))

instance PrettyT t => Show (MetaTyVar t) where
  show m = show (prettyT m)

type Level = Int
data TVar t = Unbound Level | BoundTo t

data MTVQ = MTVSigma | MTVTau | MTVEffect deriving (Eq)
data MetaTyVar t = Meta { mtvConstraint :: MTVQ
                        , mtvDesc       :: T.Text
                        , mtvUniq       :: Uniq
                        , mtvRef        :: IORef (TVar t)
                        }

descMTVQ :: MTVQ -> String
descMTVQ MTVSigma  = "S"
descMTVQ MTVTau    = "R"
descMTVQ MTVEffect = "E"

mtvIsEffect mtv = mtvConstraint mtv == MTVEffect

childrenOfArrayIndex (ArrayIndex a b _ _) = [a, b]

briefCC CCC = "ccc"
briefCC FastCC = ""

-- |||||||||||||||||||||||||| Patterns ||||||||||||||||||||||||||{{{

data E_VarAST ty = VarAST { evarMaybeType :: Maybe ty
                          , evarName      :: T.Text }

data EPattern ty =
          EP_Wildcard     SourceRange
        | EP_Variable     SourceRange (E_VarAST ty)
        | EP_Ctor         SourceRange [EPattern ty] T.Text
        | EP_Bool         SourceRange Bool
        | EP_Int          SourceRange T.Text
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
                                   , caseArmBindings:: Seq (TypedId ty)
                                   , caseArmRange   :: SourceRange
                                   } deriving (Eq, Show)

caseArmExprs :: CaseArm pat expr ty -> [expr]
caseArmExprs arm = [caseArmBody arm] ++ caseArmGuardList arm
  where
    caseArmGuardList (CaseArm _ _ Nothing  _ _) = []
    caseArmGuardList (CaseArm _ _ (Just e) _ _) = [e]

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- |||||||||||||||||||||||| Effects |||||||||||||||||||||||||||||{{{
data EffectDecl ty = EffectDecl {
    effectDeclName      :: TypeFormal
  , effectDeclTyFormals :: [TypeFormal]
  , effectDeclCtors     :: [EffectCtor ty]
  , effectDeclRange     :: SourceRange
  }
  
data EffectCtor ty = EffectCtor {
    effectCtorAsData :: DataCtor ty
  , effectCtorOutput :: ty
}
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||| Data Types |||||||||||||||||||||||||||||||{{{
data DataType ty = DataType {
    dataTypeName      :: TypeFormal
  , dataTypeTyFormals :: [TypeFormal]
  , dataTypeCtors     :: [DataCtor ty]
  , dataTypeIsForeign :: Bool
  , dataTypeRange     :: SourceRange
  }

-- CtorIds are created before typechecking.
-- They are used to identify/disambiguate constructors.
data CtorId       = CtorId { ctorTypeName :: DataTypeName
                           , ctorCtorName :: T.Text
                           , ctorArity    :: Int
                           } deriving (Show, Eq, Ord)

data DataCtor ty = DataCtor { dataCtorName  :: CtorName
                            , dataCtorDTTyF :: [TypeFormal]
                            , dataCtorTypes :: [ty]
                            , dataCtorRepr  :: Maybe CtorRepr
                            , dataCtorLone  :: Bool
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
                                , ctorLLInfoLone :: Bool -- Only one ctor?
                                }
                     deriving (Show, Functor)

type CtorRep = (CtorId, CtorRepr)

type CtorName     = T.Text
type DataTypeName = T.Text

data DataTypeSig  = DataTypeSig (Map CtorName CtorId)

-- Occurrences are generated in pattern matching (and pushed through to LLVM).
-- A pair (n, c) in an occurrence means "field n of the struct type for ctor c".
type FieldOfCtor ty = (Int, LLCtorInfo ty)
type Occurrence ty = [FieldOfCtor ty]

occType :: PrettyT t => TypedId t -> Occurrence t -> t
occType v occ = let
                   go ty [] [] = ty
                   go _ (k:offs) (tys:tyss)
                               = go (tys !! k) offs tyss
                   go ty offs tyss =
                        error $ show $
                          text "occType: " <> prettyT ty
                               <> text "; offs=" <> prettyT offs
                               <> text "~~~" <> prettyT tyss

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
data Literal = LitInt   !LiteralInt
             | LitFloat !LiteralFloat
             | LitText  !T.Text
             | LitBool  !Bool
             | LitByteArray !B.ByteString
             deriving (Show, Eq)

data LiteralInt = LiteralInt { litIntValue   :: !Integer
                             , litIntMinBits :: !Int
                             , litIntText    :: !T.Text
                             } deriving (Show, Eq)

data LiteralFloat = LiteralFloat { litFloatValue   :: !Double
                                 , litFloatText    :: !T.Text
                                 } deriving (Show, Eq)

powersOfTwo = [2^k | k <- [1..]]

mkLiteralIntWithText integerValue originalText =
  LiteralInt         integerValue activeBits originalText
    where
        activeBits =
             if integerValue == -2147483648 then 32 -- handle edge cases directly
               else if integerValue == -9223372036854775808 then 64
                 else bitLengthOf (abs integerValue) + signOf integerValue
        bitLengthOf n = go 1 powersOfTwo where
                        go k (pow2k:pows) = if n < pow2k then k else go (k+1) pows
                        go _ [] = error "bitLengthOf invariant violated"
        signOf x = if x < 0 then 1 else 0

instance PrettyT Literal where
  prettyT (LitInt int) = red     $ text (litIntText int)
  prettyT (LitFloat f) = dullred $ text (litFloatText f)
  prettyT (LitText  t) =  dquotes (text t)
  prettyT (LitBool  b) =           text (if b then "True" else "False")
  prettyT (LitByteArray b) = text "b" <> dquotes (text $ T.pack $ show b)

data WholeProgramAST expr ty = WholeProgramAST {
          programASTmodules    :: [ModuleAST expr ty]
     }

data IsForeignDecl = NotForeign | IsForeign T.Text deriving Show
data ToplevelItem expr ty =
      ToplevelDecl (T.Text, ty, IsForeignDecl)
    | ToplevelDefn (T.Text, expr ty)
    | ToplevelData (DataType ty)
    | ToplevelEffect (EffectDecl ty)

data ModuleAST expr ty = ModuleAST {
          moduleASThash        :: String
        , moduleASTincludes    :: [ (T.Text, T.Text) ]
        , moduleASTitems       :: [ToplevelItem expr ty]
        , moduleASTsourceLines :: SourceLines
        , moduleASTprimTypes   :: [DataType ty]
     }

moduleASTdataTypes m = [dt | ToplevelData dt <- moduleASTitems m]
moduleASTdecls     m = [de | ToplevelDecl de <- moduleASTitems m]
moduleASTeffects   m = [ef | ToplevelEffect ef <- moduleASTitems m]

instance (Summarizable (expr ty), Summarizable ty) => Summarizable (ToplevelItem expr ty) where
  textOf item _width =
      case item of
          ToplevelDecl (nm, _ty, _isForeign) -> text "Decl: " <> text nm
          ToplevelDefn (nm, _expr) -> text "Defn: " <> text nm
          ToplevelData dt -> text "Data: " <> text (typeFormalName $ dataTypeName dt)
          ToplevelEffect _ -> text "Effect..."

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
computeIsFnRec' fnFreeIds ids =
  if Set.null (Set.intersection fnFreeIds (Set.fromList ids)) then NotRec else YesRec

data ModuleIL expr ty = ModuleIL {
          moduleILbody        :: expr
        , moduleILdecls       :: [(T.Text, ty, IsForeignDecl)]
        , moduleILdataTypes   :: [DataType ty]
        , moduleILprimTypes   :: [DataType ty]
        , moduleILeffectDecls :: [EffectDecl ty]
        , moduleILsourceLines :: SourceLines
     }

data ToplevelBinding ty = TopBindArray Ident ty [Literal]
                        | TopBindLiteral Ident ty Literal
                        | TopBindTuple   Ident ty [Ident]
                        | TopBindAppCtor Ident ty (CtorId, CtorRepr) [Ident]

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||| Source Ranges ||||||||||||||||||||||||{{{

data Formatting = Comment    {-SourceRange-} T.Text
                | BlankLine
                deriving Show

data ExprAnnot = ExprAnnot
                        [Formatting] -- preceding comments and/or blank lines.
                        SourceRange  -- range of bare expr not incl. formatting.
                        [Formatting] -- trailing comments and/or blank lines.

annotForRange sr = ExprAnnot [] sr []

instance SourceRanged ExprAnnot where rangeOf (ExprAnnot _ rng _) = rng

instance Show ExprAnnot where show (ExprAnnot _ rng _) = show rng

data AllocationSource = AllocationSource T.Text SourceRange deriving (Show, Eq)

instance SourceRanged AllocationSource where rangeOf (AllocationSource _ sr) = sr

data Comments = C { leading :: [Formatting], trailing :: [Formatting] } deriving Show
annotComments (ExprAnnot l _ t) = C l t

showComments (C [] []) = ""
showComments other     = " ... " ++ show other


-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||| Structured Things ||||||||||||||||||||||{{{

class Structured a where
    childrenOf :: a -> [a]

class Summarizable a where
    textOf     :: a -> Int -> Doc AnsiStyle

-- Builds trees like this:
-- AnnSeq        :: i32
-- ├─AnnCall       :: i32
-- │ ├─AnnVar       expect_i32 :: ((i32) -> i32)
-- │ └─AnnTuple
-- │   └─AnnInt       999999 :: i32

showStructure :: (Summarizable a, Structured a) => a -> Doc AnsiStyle
showStructure e = showStructureP e "" False
  where
    showStructureP :: (Summarizable b, Structured b) => b -> T.Text -> Bool -> Doc AnsiStyle
    showStructureP e prefix isLast =
        let children = childrenOf e in
        let thisIndent = prefix `T.append` (if isLast then "└─" else "├─") in
        let nextIndent = prefix `T.append` (if isLast then "  " else "│ ") in
        let padding = max 6 (60 - T.length thisIndent) in
        -- [ (child, index, numchildren) ]
        let childpairs = Prelude.zip3 children [1..]
                               (Prelude.repeat (Prelude.length children)) in
        let childlines = map (\(c, n, l) ->
                                showStructureP c nextIndent (n == l))
                             childpairs in
        text thisIndent <> textOf e padding <> line
                                     <> (Prelude.foldl (<>) PP.emptyDoc childlines)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- ||||||||||||||||||||||||| Utilities ||||||||||||||||||||||||||{{{

concatMapM f vs = do vs' <- mapM f vs ; return $ concat vs'

mapMaybeM :: (Monad m) => (a -> m b) -> Maybe a -> m (Maybe b)
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

combinedFreeIdents :: AExpr a => [a] -> Set Ident
combinedFreeIdents xs = Set.unions $ map freeIdents xs

caseArmFreeIds arm =
   combinedFreeIdents (caseArmExprs arm) `sans`
        map tidIdent  (caseArmBindings arm |> Foldable.toList)

sans :: Ord a => Set a -> [a] -> Set a
sans base toremove = Set.difference base $ Set.fromList toremove

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
joinWith s ss = intercalate s ss

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

data ArrayEntry e = AE_Int ExprAnnot T.Text
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
identPrefix (GlobalSymbol name _) = name
identPrefix (Ident name _)        = name

data Ident = Ident        !T.Text {-# UNPACK #-} !Uniq
           | GlobalSymbol !T.Text !MaybeRename

data MaybeRename = NoRename | RenameTo T.Text deriving Show

fmapIdent :: (T.Text -> T.Text) -> Ident -> Ident
fmapIdent tt (Ident t u)          = Ident        (tt t) u
fmapIdent tt (GlobalSymbol t alt) = GlobalSymbol (tt t) alt

data TypedId ty = TypedId { tidType :: ty, tidIdent :: Ident }


prettyIdent (Ident name number)   = text name <> text "!" <> pretty number
prettyIdent (GlobalSymbol name (RenameTo alt)) = text name <> "~>" <> text alt
prettyIdent (GlobalSymbol name _) = text "G:" <> text name

prettyId (TypedId _ i) = prettyIdent i
prettyTypedId (TypedId t i) = prettyIdent i <> text " :: " <> prettyT t

-- Handler expressions pre-allocate the ids that will be bound for the `resume` functions
-- during typechecking; they must be kept around to be used during handler compilation.
type ResumeIds = (Ident, Ident)

-- * NamedPrim refers to global (function) symbols provided by the runtime (or interpreter)
--   rather than via the compiler. Example: prim_print_bytes_stdout.
-- * PrimOp mostly identifes simple operations open-coded by the compiler.
--   Examples: fixnum comparisons and bitwise operations.
--   PrimOps are passed through to the back end, for consumption by CodegenPass::emitPrimitiveOperation().
-- * PrimOpInt exists because the LLVM backend needs the target type but SMT checking
--   needs the source type, and PrimOp only provides one type slot.
-- * FieldLookup "foo" corresponds to the syntax   .foo
-- * PrimInlineAsm correponds to prim inline-asm; it's special cased to allow static tracking
--   of the assembly text and constraints.
-- * LookupEffectHandler is a purely-internal primitive.
data FosterPrim ty = NamedPrim (TypedId ty) -- invariant: global symbol
                   | PrimOp { ilPrimOpName :: T.Text
                            , ilPrimOpType :: ty }
                   | PrimOpInt T.Text IntSizeBits IntSizeBits -- from, to
                   | FieldLookup T.Text (Maybe Int)
                   | CoroPrim  CoroPrim ty ty
                   | PrimInlineAsm ty T.Text T.Text Bool
                   | LookupEffectHandler Uniq

data CoroPrim = CoroCreate | CoroInvoke | CoroYield | CoroParent | CoroIsDead deriving (Show, Eq)

-- TODO distinguish stable pointers from lively pointers?
--      stable-pointer-bit at compile time or runtime?
-- TODO other allocation zones? -- refcounted heap, thread-local heap,
--                                 C/malloc/free heap,
--                                 type-specific heaps, etc, etc...
data AllocMemRegion = MemRegionStack
                    | MemRegionGlobalData
                    | MemRegionGlobalHeap deriving (Show, Eq)

data AllocInfo t = AllocInfo { allocType      :: t
                             , allocRegion    :: AllocMemRegion
                             , allocTypeName  :: T.Text
                             , allocCtorRepr  :: Maybe CtorRepr
                             , allocArraySize :: Maybe (TypedId t)
                             , allocSite      :: T.Text
                             , allocZeroInit  :: ZeroInit
                             }

data ZeroInit = DoZeroInit | NoZeroInit deriving (Show, Eq)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
-- {{{ Split up a sequence of function bindings into minimal SCCs.
mkFunctionSCCs :: AExpr fn => [Ident] -> [fn] -> expr -> (fn -> Bool -> fn) ->
                             ([Ident] -> [fn] -> expr -> expr) -> expr
mkFunctionSCCs []  []  body _ k = k [] [] body
mkFunctionSCCs ids fns body recMarker k =
  let idset    = Set.fromList ids
      fnids fn = Set.toList $ Set.intersection (freeIdents fn) idset
      callGraphList = map (\(id, fn) -> ((fn, id), id, fnids fn)) (zip ids fns)
      theSCCs       = Graph.stronglyConnComp callGraphList
  in foldr (\scc body ->
          let mkFuns ids fns = k ids fns body in
          case scc of
                Graph.AcyclicSCC (fn, id) -> mkFuns [id] [recMarker fn False]
                Graph.CyclicSCC fnids ->     mkFuns ids fns'
                                              where fns' = map (\fn -> recMarker fn True) fns
                                                    (fns, ids) = unzip fnids
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
  freeIdents f = freeIdentsFn (fnBody f) (fnVars f)

freeIdentsFn :: AExpr body => body -> [TypedId t] -> Set Ident
freeIdentsFn body vars = freeIdents body `sans` map tidIdent vars

instance IntSized IntSizeBits
 where
       intSizeOf I1 = 1
       intSizeOf I8 = 8
       intSizeOf I16 = 16
       intSizeOf I32 = 32
       intSizeOf I64 = 64
       intSizeOf IWd = 32 -- TODO this is hacky =/
       intSizeOf IDw = 64

instance PrettyT CallConv where
  prettyT CCC    = text "CCC"
  prettyT FastCC = text "FastCC"

instance Pretty IntSizeBits    where pretty IWd = text "Word"
                                     pretty IDw = text "WordX2"
                                     pretty I1 = text "Bool"
                                     pretty i  = text "Int" <> pretty (intSizeOf i)
instance Pretty Ident          where pretty id = prettyIdent id --text (show id)
instance PrettyT Ident where prettyT = pretty
-- We don't use the constaint here, but want to enforce it to give ourselves
-- the flexibility to change the definition to use it.
instance PrettyT t => PrettyT (TypedId t)
                               where prettyT tid = pretty (tidIdent tid)
instance SourceRanged expr => Pretty (CompilesResult expr)
                               where pretty cr = text (T.pack $ show cr)

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

pick t NoRename = t
pick _ (RenameTo t) = t

-- Give a distinct name to the Ord instance so that profiles get a more informative name.
compareIdents (GlobalSymbol t1 alt1)
              (GlobalSymbol t2 alt2) = compare (pick t1 alt1) (pick t2 alt2)
compareIdents (Ident _t1 u1)  (Ident _t2 u2)   = compare u1 u2
compareIdents (GlobalSymbol _ _)  (Ident _  _ )    = LT
compareIdents (Ident _ _)       (GlobalSymbol _ _) = GT

instance Eq Ident where
    (GlobalSymbol t1 alt1) == (GlobalSymbol t2 alt2) = pick t1 alt1 == pick t2 alt2
    (Ident _t1 u1)         == (Ident _t2 u2) = u1 == u2 {-&& t1 == t2-}
    _ == _ = False

{-
instance Show Ident where
    show (Ident name number)   = T.unpack name ++ "!" ++ show number
    show (GlobalSymbol name (RenameTo alt)) = T.unpack name ++ "~>" ++ T.unpack alt
    show (GlobalSymbol name _) = T.unpack name
-}

instance Eq (TypedId t) where
       (==) (TypedId _ a) (TypedId _ b) = (==) a b

instance Ord (TypedId t) where
    compare (TypedId _ a) (TypedId _ b) = compareIdents a b

instance (Show ty) => Show (TypedId ty)
  where show (TypedId ty id) = show (pretty id) ++ " :: " ++ show ty

instance Eq TyVar where
  BoundTyVar s1 _    == BoundTyVar s2 _    = s1 == s2
  SkolemTyVar _ u1 _ == SkolemTyVar _ u2 _ = u1 == u2
  _ == _ = False

instance Ord TyVar where
  BoundTyVar s1 _    `compare` BoundTyVar s2 _    = s1 `compare` s2
  SkolemTyVar _ u1 _ `compare` SkolemTyVar _ u2 _ = u1 `compare` u2
  BoundTyVar s1 _    `compare` SkolemTyVar s2 _ _ = s1 `compare` s2
  SkolemTyVar s1 _ _ `compare` BoundTyVar s2 _    = s1 `compare` s2

prettyOccurrence v occ = prettyT v <> text "/" <> pretty (map fst occ)

instance Show TyVar where
    show (BoundTyVar x _) = "'" ++ T.unpack x
    show (SkolemTyVar x u k) = "$" ++ T.unpack x ++ "." ++ show u ++ "::" ++ show k

instance Show SourceRange where
    show _ = "<...source range...>"

instance (SourceRanged expr) => Show (CompilesResult expr) where
  show (CompilesResult (OK e))     = show (rangeOf e)
  show (CompilesResult (Errors _)) = "<...invalid term...>"

instance Show (PatternAtom ty) where
  show (P_Wildcard _ _)            = "P_Wildcard"
  show (P_Variable _ v)            = "P_Variable " ++ show (pretty $ tidIdent v)
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

instance PrettyT t => PrettyT (Pattern t) where
  prettyT p =
    case p of
        P_Atom          atom              -> prettyT atom
        P_Ctor          _rng _ty pats cid -> parens (text "$" <> text (ctorCtorName $ ctorInfoId cid) <+> (hsep $ map prettyT pats))
        P_Tuple         _rng _ty pats     -> parens (hsep $ punctuate comma (map prettyT pats))
        P_Or            _rng _ty pats     -> parens (hsep $ punctuate (text " or ") (map prettyT pats))

instance PrettyT t => PrettyT (PatternAtom t) where
  prettyT p =
    case p of
        P_Wildcard      _rng _ty          -> text "_"
        P_Variable      _rng tid          -> pretty (tidIdent tid)
        P_Bool          _rng _ty b        -> text $ if b then "True" else "False"
        P_Int           _rng _ty li       -> text (litIntText li)

instance PrettyT t => PrettyT (PatternRepr t) where
  prettyT p =
    case p of
        PR_Atom          atom              -> prettyT atom
        PR_Ctor          _rng _ty pats cid -> parens (text "$" <> text (ctorCtorName $ ctorLLInfoId cid) <+> (hsep $ map prettyT pats))
        PR_Tuple         _rng _ty pats     -> parens (hsep $ punctuate comma (map prettyT pats))
        PR_Or            _rng _ty pats     -> parens (hsep $ punctuate (text " or ") (map prettyT pats))

instance Show ty => Show (EPattern ty) where
  show (EP_Wildcard _)            = "EP_Wildcard"
  show (EP_Variable _ v)          = "EP_Variable " ++ show v
  show (EP_Ctor     _ _pats ctor) = "EP_Ctor     " ++ show ctor
  show (EP_Bool     _ b)          = "EP_Bool     " ++ show b
  show (EP_Int      _ str)        = "EP_Int      " ++ T.unpack str
  show (EP_Tuple    _ pats)       = "EP_Tuple    " ++ show pats
  show (EP_Or       _ pats)       = "EP_Or       " ++ show pats

instance PrettyT ty => PrettyT (EPattern ty) where
  prettyT (EP_Wildcard _)            = text "_"
  prettyT (EP_Variable _ v)          = prettyT v
  prettyT (EP_Ctor     _ pats ctor)  = text "$" <> text ctor <+> hsep (map prettyT pats)
  prettyT (EP_Bool     _ b)          = pretty b
  prettyT (EP_Int      _ str)        = text str
  prettyT (EP_Tuple    _ pats)       = tupled $ map prettyT pats
  prettyT (EP_Or       _ pats)       = parens (hsep $ punctuate (text " or ") (map prettyT pats))

instance PrettyT ty => PrettyT (E_VarAST ty) where
  prettyT (VarAST (Just ty) txt) = text txt <+> text "::" <+> prettyT ty
  prettyT (VarAST Nothing   txt) = text txt

instance PrettyT t => PrettyT (FosterPrim t) where
  prettyT (NamedPrim (TypedId _ i)) = pretty i
  prettyT (PrimOp nm _ty) = text nm
  prettyT (PrimOpInt op frm to) = text op <> text "from " <> pretty frm <> text " to " <> pretty to
  prettyT (CoroPrim c t1 t2) = pretty c <> text ":[" <> prettyT t1
                                       <> text "," <+> prettyT t2
                                       <> text "]"
  prettyT (FieldLookup fieldName _) = text "." <> text fieldName
  prettyT (PrimInlineAsm _ cnt _cns _haseffects) = text "inline-asm" <+> text cnt
  prettyT (LookupEffectHandler tag) = text "lookup_handler_for_effect{" <> pretty tag <> text "}"

instance Pretty CoroPrim where
  pretty CoroCreate = text "CoroCreate"
  pretty CoroInvoke = text "CoroInvoke"
  pretty CoroYield  = text "CoroYield"
  pretty CoroParent = text "CoroParent"
  pretty CoroIsDead = text "CoroIsDead"

instance Pretty CtorId where
  pretty (CtorId tynm ctnm sm) = pretty tynm <> text "." <> pretty ctnm <> parens (pretty sm)

instance Pretty CtorRepr where
  pretty (CR_Default int) = text "#" <> pretty int
  pretty (CR_Tagged  int) = text "#" <> pretty int
  pretty (CR_Transparent)  = text "#" <> text "~"
  pretty (CR_TransparentU) = text "#{}"
  pretty (CR_Nullary int) = text "##" <> pretty int <> text "~"
  pretty (CR_Value   int) = text "##" <> pretty int

instance PrettyT CtorId where prettyT = pretty
instance PrettyT CtorRepr where prettyT = pretty
instance (PrettyT t) => PrettyT (LLCtorInfo t) where
  prettyT (LLCtorInfo id repr tys lone) =
    parens $ text "LLCtorInfo" <+> prettyT id <+> prettyT repr <+> prettyT tys <+> prettyT lone

instance PrettyT Bool where prettyT = pretty
instance PrettyT Int  where prettyT = pretty
instance PrettyT T.Text where prettyT = pretty
--instance (PrettyT t) => PrettyT (TypedId t) where prettyT = pretty

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

instance PrettyT IsForeignDecl where
  prettyT ifd = text (T.pack $ show ifd)

instance PrettyT t => PrettyT (DataType t) where
  prettyT dt =
    text "type case" <+> pretty (dataTypeName dt) <+>
         hsep (map (parens . pretty) (dataTypeTyFormals dt))
     <$> indent 2 (vsep (map prettyDataTypeCtor (dataTypeCtors dt)))
     <$> text ";"
     <$> text ""

prettyDataTypeCtor dc =
  text "of" <+> text "$" <> text (dataCtorName dc)
                        <+> (group (hang 2 $ vsep (PP.emptyDoc : map prettyT (dataCtorTypes dc))))

instance PrettyT t => PrettyT (EffectDecl t) where
  prettyT ed =
    text "effect" <+> pretty (effectDeclName ed) <+>
         hsep (map (parens . pretty) (effectDeclTyFormals ed))
     <$> indent 2 (vsep (map prettyEffectCtor (effectDeclCtors ed)))
     <$> text ";"
     <$> text ""

prettyEffectCtor ec = prettyDataTypeCtor (effectCtorAsData ec)
                        <+> text "=>" <+> prettyT (effectCtorOutput ec)

prettyHandler :: (PrettyT expr, PrettyT (pat ty)) => expr -> [CaseArm pat expr ty] -> Maybe expr -> Doc AnsiStyle
prettyHandler action arms mb_xform =
            kwd "handle" <+> prettyT action
            <$> indent 2 (vsep [ kwd "of" <+>
                                        (hsep $ [{- fill 20 -} (prettyT epat)]
                                            ++  prettyGuard guard
                                            ++ [text "->" <+> prettyT body])
                              | (CaseArm epat body guard _ _) <- arms
                              ])
            <> (case mb_xform of
                 Nothing -> text ""
                 Just x  -> text "" <$> lkwd "as" <> prettyT x)
            <$> end
  where
    prettyGuard Nothing  = []
    prettyGuard (Just e) = [text "if" <+> prettyT e]
    kwd  s = dullblue  (text s)
    lkwd s = dullwhite (text s)
    end    = lkwd "end"

(<$>) :: Doc a -> Doc a -> Doc a
(<$>) a b = a <> line <> b

(</>) a b = a <> softline <> b
(<$$>) a b = a <> linebreak <> b

linebreak = flatAlt line emptyDoc
softbreak = group linebreak

dullblue, dullgreen, dullwhite, dullyellow,
  dullred, red, blue, green, yellow :: Doc AnsiStyle -> Doc AnsiStyle
dullred d = annotate (colorDull Red) d
dullblue d = annotate (colorDull Blue) d
dullwhite d = annotate (colorDull White) d
dullgreen d = annotate (colorDull Green) d
dullyellow d = annotate (colorDull Yellow) d
red d = annotate (color Red) d
blue d = annotate (color Blue) d
green d = annotate (color Green) d
yellow d = annotate (color Yellow) d

string :: String -> Doc ann
string s = pretty s

-- For (temporary) compatibility with ansi-wl-pprint
text :: T.Text -> Doc a
text s = pretty s

instance (PrettyT t) => PrettyT (Seq t) where
  prettyT seq = align $ PP.list (map prettyT (Foldable.toList seq))

instance (PrettyT t) => PrettyT (Maybe t) where
    prettyT Nothing = text "Nothing"
    prettyT (Just t) = text "Just" <+> prettyT t

instance PrettyT Char where prettyT c = pretty c
instance (PrettyT a, PrettyT b) => PrettyT (a, b) where
    prettyT (x, y) = tupled [prettyT x, prettyT y]
instance (PrettyT a, PrettyT b, PrettyT c) => PrettyT (a, b, c) where
    prettyT (x, y, z) = tupled [prettyT x, prettyT y, prettyT z]

prettyCase :: (PrettyT expr, PrettyT (pat ty)) => expr -> [CaseArm pat expr ty] -> Doc AnsiStyle
prettyCase scrutinee arms =
            kwd "case" <+> prettyT scrutinee
            <$> indent 2 (vsep [ kwd "of" <+>
                                        (hsep $ [{- fill 20 -} (prettyT epat)]
                                            ++  prettyGuard guard
                                            ++ [text "->" <+> prettyT body])
                              | (CaseArm epat body guard _ _) <- arms
                              ])
            <$> end
  where
    prettyGuard Nothing  = []
    prettyGuard (Just e) = [text "if" <+> prettyT e]
    kwd  s = dullblue  (text s)
    lkwd s = dullwhite (text s)
    end    = lkwd "end"

instance TExpr (ArrayIndex (TypedId t)) t where
   freeTypedIds (ArrayIndex v1 v2 _ _) = [v1, v2]

instance AExpr a => AExpr (Maybe a) where
   freeIdents Nothing = Set.fromList []
   freeIdents (Just x) = freeIdents x

deriving instance (Show ty) => Show (EffectDecl ty)
deriving instance (Show ty) => Show (EffectCtor ty)

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

compareLLCtorInfo (LLCtorInfo c1 r1 _ o1) (LLCtorInfo c2 r2 _ o2) =
  compare (c1, r1, o1) (c2, r2, o2)

instance Eq  (LLCtorInfo ty) where
  c1 == c2 = compare c1 c2 == EQ

instance (PrettyT t) => PrettyT [t] where
    prettyT xs = list (map prettyT xs)

eqTextL :: TL.Text -> TL.Text -> Bool
eqTextL = (==)

instance Eq (Doc AnsiStyle) where d1 == d2 = renderLazy (layoutCompact d1) `eqTextL` renderLazy (layoutCompact d2)

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
deriving instance Functor EffectDecl
deriving instance Functor EffectCtor
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

