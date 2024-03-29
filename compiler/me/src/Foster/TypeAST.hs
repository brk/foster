{-# LANGUAGE Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST(
  TypeAST(..), IntSizeBits(..)
, MetaTyVar(..), Sigma, Rho, Tau, MTVQ(..)
, fosBoolType, fosStringType, gFosterPrimOpsTable, primitiveDecls, primopDecls
, effectSingle, nullFx
, minimalTupleAST
, convertTyFormal
)
where

import Data.Map as Map(fromList, toList, Map)
import Data.Char as Char(isLetter)
import qualified Data.Text as T

import Prettyprinter(Pretty(..), hsep, (<+>), parens, tupled, emptyDoc)

import Foster.Base
import Foster.Kind
import Foster.ExprAST
import Foster.SourceRange(SourceRange(MissingSourceRange))

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere
type Effect = TypeAST

data TypeAST =
           PrimIntAST       IntSizeBits
         | TyConAST         DataTypeName
         | TyAppAST         Rho  [Sigma]
         | RecordTypeAST    [T.Text] [Sigma]
         | TupleTypeAST     Kind [Sigma]
         | RefTypeAST       (Sigma)
         | ArrayTypeAST     (Sigma)
         | FnTypeAST        { fnTypeDomain :: [Sigma]
                            , fnTypeRange  ::  Sigma
                            , fnTypeEffect ::  Effect
                            , fnTypeCallConv :: CallConv
                            , fnTypeProcOrFunc :: ProcOrFunc }
         | ForAllAST        [(TyVar, Kind)] Rho
         | TyVarAST         TyVar
         | MetaPlaceholderAST MTVQ String
         | RefinedTypeAST   String TypeAST (ExprAST TypeAST)

-- For MetaPlaceholderAST, user-written placeholders can only be tau's, but we
-- must be able to generate sigmas for function type skeletons and such

instance Eq (MetaTyVar t) where
  m1 == m2 = case (mtvUniq m1 == mtvUniq m2, mtvRef m1 == mtvRef m2) of
       (True,  True)  -> True
       (False, False) -> False
       _ -> error $ "Malformed meta type variables "
         ++ show (mtvUniq m1) ++ "@" ++ (T.unpack $ mtvDesc m1) ++ " and "
         ++ show (mtvUniq m2) ++ "@" ++ (T.unpack $ mtvDesc m2) ++ ": mismatch between uniqs and refs!"

hpre [] = emptyDoc
hpre ds = emptyDoc <+> hsep ds

instance PrettyT TypeAST where
    prettyT x = case x of
        PrimIntAST         size     -> pretty size
        TyConAST nam                -> text nam
        TyAppAST con []             ->          prettyT con
        TyAppAST con types          -> parens $ prettyT con <> hpre (map prettyT types)
        RecordTypeAST _labels types     -> text "RecordAST" <> tupled (map prettyT types)
        TupleTypeAST k   types          -> tupled (map prettyT types) <> text (kindAsHash k)
        FnTypeAST    s t fx cc cs       -> text "(" <> prettyT s <> text " =" <> text (briefCC cc) <> text ";"
                                              <+> prettyT fx <> text "> " <> prettyT t <> text " @{" <> string (show cs) <> text "})"
        ForAllAST  tvs rho              -> text "(forall " <> hsep (prettyTVs tvs) <> text ". " <> prettyT rho <> text ")"
        TyVarAST   tv                   -> prettySrc tv
        -- MetaTyVar m                     -> text "(~(" <> pretty (descMTVQ (mtvConstraint m)) <> text ")!" <> text (show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")")
        RefTypeAST    ty                -> text "(Ref " <> prettyT ty <> text ")"
        ArrayTypeAST  ty                -> text "(Array " <> prettyT ty <> text ")"
        RefinedTypeAST _nm ty _e        -> text "(Refined " <> prettyT ty <> text ")"
        MetaPlaceholderAST _ nm         -> text "(.meta " <> string nm <> text ")"

prettyTVs tvs = map (\(tv,k) -> parens (pretty tv <+> text "::" <+> pretty k)) tvs

instance Show TypeAST where show x = show (prettyT x)
  {-
instance Show TypeAST where
    show x = case x of
        PrimIntAST         size         -> "(PrimIntAST " ++ show size ++ ")"
        PrimFloat64AST                  -> "(PrimFloat64)"
        TyConAppAST    tc types         -> "(TyCon: " ++ show tc ++ joinWith " " ("":map show types) ++ ")"
        TupleTypeAST      types         -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeAST    s t cc cs          -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        ForAllAST  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarAST   tv                   -> show tv
        MetaTyVar m                     -> "(~(" ++ descMTVQ (mtvConstraint m) ++ ")!" ++ show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")"
        RefTypeAST    ty                -> "(Ref " ++ show ty ++ ")"
        ArrayTypeAST  ty                -> "(Array " ++ show ty ++ ")"
-}

instance Summarizable TypeAST where
    textOf e _width =
        case e of
            PrimIntAST     size            -> string $ "PrimIntAST " ++ show size
            TyConAST       nam             -> text $ nam
            TyAppAST con   _               -> string "(TyAppAST" <+> prettyT con <> text ")"
            RecordTypeAST   _   _          -> string $ "RecordTypeAST"
            TupleTypeAST   k   _           -> string $ "TupleTypeAST" ++ kindAsHash k
            FnTypeAST    {}                -> string $ "FnTypeAST"
            ForAllAST  tvs _rho            -> string $ "ForAllAST " ++ show tvs
            TyVarAST   tv                  -> string $ "TyVarAST " ++ show tv
            -- MetaTyVar m                 -> string $ "MetaTyVar " ++ mtvDesc m
            RefTypeAST    _                -> string $ "RefTypeAST"
            ArrayTypeAST  _                -> string $ "ArrayTypeAST"
            RefinedTypeAST {}              -> string $ "RefinedTypeAST"
            MetaPlaceholderAST mtvq _      -> string $ "MetaPlaceholderAST " ++ descMTVQ mtvq

instance Structured TypeAST where
    childrenOf e =
        case e of
            PrimIntAST         _           -> []
            TyConAST           _           -> []
            TyAppAST     con  types        -> con:types
            RecordTypeAST  _  types        -> types
            TupleTypeAST  _k  types        -> types
            FnTypeAST   ss t fx _ _        -> ss ++ [t, fx]
            ForAllAST  _tvs rho            -> [rho]
            TyVarAST   _tv                 -> []
            -- MetaTyVar _                    -> []
            RefTypeAST    ty               -> [ty]
            ArrayTypeAST  ty               -> [ty]
            RefinedTypeAST _ ty _          -> [ty]
            MetaPlaceholderAST {}          -> []

fosBoolType = PrimIntAST I1
fosStringType = TyAppAST (TyConAST "Text") []

minimalTupleAST []    = TupleTypeAST KindPointerSized []
minimalTupleAST [arg] = arg
minimalTupleAST args  = TupleTypeAST KindPointerSized args

nullFx = TyAppAST (TyConAST "effect.Empty") []

mkProcType args rets = mkProcTypeWithFx nullFx args rets
mkFnType   args rets = mkFnTypeWithFx nullFx   args rets

mkProcTypeWithFx fx args rets = FnTypeAST args (minimalTupleAST rets) fx CCC    FT_Proc
mkFnTypeWithFx   fx args rets = FnTypeAST args (minimalTupleAST rets) fx FastCC FT_Func

--------------------------------------------------------------------------------
effectSingle :: T.Text -> [TypeAST] -> Effect
effectSingle name tys = effectExtend (TyAppAST (TyConAST name) tys) nullFx

effectExtend :: Effect -> Effect -> Effect
effectExtend eff row = TyAppAST (TyConAST "effect.Extend") [eff, row]

effectsExtends :: [Effect] -> Effect -> Effect
effectsExtends effs eff = foldr effectExtend eff effs

_effectsClosed :: [Effect] -> Effect
_effectsClosed effs = effectsExtends effs nullFx
--------------------------------------------------------------------------------

i8  = PrimIntAST I8
--i16 = PrimIntAST I16
i32 = PrimIntAST I32
i64 = PrimIntAST I64
i1  = PrimIntAST I1
iwd = PrimIntAST IWd
f64 = TyAppAST (TyConAST "Float64") []
f32 = TyAppAST (TyConAST "Float32") []
int = TyAppAST (TyConAST "Int") []
big = TyAppAST (TyConAST "IntInf") []

primTyVars tyvars = map (\v -> (v, KindAnySizeType)) tyvars
boxedTyVars tyvars = map (\v -> (v, KindPointerSized)) tyvars

-- These names correspond to (the C symbols of)
-- functions implemented by the Foster runtime.
primitiveDecls :: [(T.Text, TypeAST, IsForeignDecl)]
primitiveDecls = map (\(n,t) -> (n,t,NotForeign)) $
    [(,) "expect_i64"  $ mkProcType [i64] []
    ,(,)  "print_i64"  $ mkProcType [i64] []

    ,(,) "opaquely_i32" $ mkProcType [i32] [i32]
    ,(,) "opaquely_i64" $ mkProcType [i64] [i64]

    ,(,) "get_cmdline_n_args" $ mkProcType [] [i32]
    ,(,) "get_cmdline_arg_n" $ mkProcType [i32] [fosStringType]

    ,(,) "memcpy_i8_to_at_from_at_len" $ mkProcType [ArrayTypeAST i8, i64,
                                                   ArrayTypeAST i8, i64, i64] [i64]

    ,(,) "prim_print_bytes_stdout" $ mkProcType [ArrayTypeAST i8, i32, i32] []
    ,(,) "prim_print_bytes_stderr" $ mkProcType [ArrayTypeAST i8, i32, i32] []

    ,(,) "print_float_p9f64"       $ mkProcType [f64] []
    ,(,) "expect_float_p9f64"      $ mkProcType [f64] []
    ,(,) "print_float_f64"         $ mkProcType [f64] []
    ,(,) "expect_float_f64"        $ mkProcType [f64] []
    ,(,) "print_float_f32"         $ mkProcType [f32] []
    ,(,) "expect_float_f32"        $ mkProcType [f32] []

    -- Calls to this function are internally transformed to AIAllocArray nodes.
    -- forall a, i32 -> Array a
    ,(,) "allocDArray" $ let a = BoundTyVar "a" (MissingSourceRange "allocDArray") in
                         ForAllAST (primTyVars [a])
                           (mkProcType [i32] [ArrayTypeAST (TyVarAST a)])

    -- forall a, Array a -> i64
    ,(,) "prim_arrayLength" $ let a = BoundTyVar "a" (MissingSourceRange "prim_arrayLength") in
                         ForAllAST (primTyVars [a])
                           (mkProcType [ArrayTypeAST (TyVarAST a)] [i64])
    
    ,(,) "force_gc_for_debugging_purposes" $ mkProcType [] [i32]

    -- TODO this is not correct for Solaris, AIX, or SGI/Irix,
    -- which use structs for time results, and is misleading on
    -- Alpha and Sparc v9, which have a 32-bit result.
    ,(,) "foster_getticks"         $ mkProcType [] [i64]
    ,(,) "foster_getticks_elapsed" $ mkProcType [i64, i64] [f64]

    ,(,) "foster_gettime_microsecs"    $ mkProcType [] [i64]
    ,(,) "foster_gettime_elapsed_secs" $ mkProcType [i64, i64] [f64]
    ]

primopDecls = map (\(name, (ty, _op)) -> (name, ty, NotForeign)) $ Map.toList gFosterPrimOpsTable

intSize bitsize = show $ pretty bitsize

prettyOpName :: T.Text -> String -> T.Text
prettyOpName nmtxt tystr =
  let nm = T.unpack nmtxt
      s  = if Char.isLetter (head nm)
              then nm ++ "-" ++ tystr  -- e.g. "bitand-Int32"
              else nm ++        tystr  -- e.g. "+Int32"
  in T.pack s

-- Note: we don't wrap LLVM's shift intrisics directly; we mask the shift
-- value to avoid undefined values. For constant shift values, the mask will
-- be trivially eliminated by LLVM.
fixnumPrimitives :: IntSizeBits -> [(T.Text, (TypeAST, FosterPrim TypeAST))]
fixnumPrimitives bitsize =
  let iKK = PrimIntAST bitsize in
  let mkPrim nm ty = (prettyOpName nm (intSize bitsize), (ty, PrimOp nm iKK)) in
  [(T.pack $  "<U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  "<u" iKK))
  ,(T.pack $  ">U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  ">u" iKK))
  ,(T.pack $ "<=U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp "<=u" iKK))
  ,(T.pack $ ">=U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp ">=u" iKK))
  ,(T.pack $  "<S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  "<s" iKK))
  ,(T.pack $  ">S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  ">s" iKK))
  ,(T.pack $ "<=S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp "<=s" iKK))
  ,(T.pack $ ">=S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp ">=s" iKK))
  ] ++
  [mkPrim "+"           $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "-"           $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "*"           $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "+uc"         $ mkProcType [iKK, iKK] [iKK] -- checked variants
  ,mkPrim "-uc"         $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "*uc"         $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "+sc"         $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "-sc"         $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "*sc"         $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "bitand"      $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "bitor"       $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "bitxor"      $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "bitshl"      $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "bitlshr"     $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "bitashr"     $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "srem-unsafe" $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "sdiv-unsafe" $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "urem-unsafe" $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "udiv-unsafe" $ mkProcType [iKK, iKK] [iKK]
  ,mkPrim "=="          $ mkProcType [iKK, iKK] [i1]
  ,mkPrim "!="          $ mkProcType [iKK, iKK] [i1]
  ,mkPrim "negate"      $ mkProcType [iKK]      [iKK]
  ,mkPrim "bitnot"      $ mkProcType [iKK]      [iKK]
  ,mkPrim "ctlz"        $ mkProcType [iKK]      [iKK]
  ,mkPrim "ctpop"       $ mkProcType [iKK]      [iKK]
  ]

-- For example, we'll have a function with external signature
--      (+f64) :: Float64 -> Float64 -> Float64
-- and internal signature
--      (PrimOp "f+" PrimFloat64AST)
flonumPrimitives :: String -> TypeAST -> [(T.Text, (TypeAST, FosterPrim TypeAST))]
flonumPrimitives tystr ty =
  let mkPrim nm fnty = (prettyOpName nm tystr, (fnty, PrimOp ("f" `T.append` nm) ty)) in
  [mkPrim "+"       $ mkProcType [ty, ty] [ty]
  ,mkPrim "-"       $ mkProcType [ty, ty] [ty]
  ,mkPrim "*"       $ mkProcType [ty, ty] [ty]
  ,mkPrim "div"     $ mkProcType [ty, ty] [ty]
  ,mkPrim "rem"     $ mkProcType [ty, ty] [ty]
  ,mkPrim "<"       $ mkProcType [ty, ty] [i1]
  ,mkPrim ">"       $ mkProcType [ty, ty] [i1]
  ,mkPrim "<="      $ mkProcType [ty, ty] [i1]
  ,mkPrim ">="      $ mkProcType [ty, ty] [i1]
  ,mkPrim "=="      $ mkProcType [ty, ty] [i1]
  ,mkPrim "!="      $ mkProcType [ty, ty] [i1]
  ,mkPrim "abs"     $ mkProcType [ty]     [ty]
  ,mkPrim "sqrt"    $ mkProcType [ty]     [ty]
  ,mkPrim "exp"     $ mkProcType [ty]     [ty]
  ,mkPrim "exp2"    $ mkProcType [ty]     [ty]
  ,mkPrim "log"     $ mkProcType [ty]     [ty]
  ,mkPrim "log2"    $ mkProcType [ty]     [ty]
  ,mkPrim "log10"   $ mkProcType [ty]     [ty]
  ,mkPrim "sin"     $ mkProcType [ty]     [ty]
  ,mkPrim "cos"     $ mkProcType [ty]     [ty]
  ,mkPrim "tan"     $ mkProcType [ty]     [ty]
  ,mkPrim "atan"    $ mkProcType [ty]     [ty]
  ,mkPrim "atan2"   $ mkProcType [ty, ty] [ty]
  ,mkPrim "ceil"    $ mkProcType [ty]     [ty]
  ,mkPrim "floor"   $ mkProcType [ty]     [ty]
  ,mkPrim "round"   $ mkProcType [ty]     [ty]
  ,mkPrim "trunc"   $ mkProcType [ty]     [ty]
  ,mkPrim "powi"    $ mkProcType [ty, i32]    [ty]
  ,mkPrim "pow"     $ mkProcType [ty, ty]     [ty]
  ,mkPrim "muladd"  $ mkProcType [ty, ty, ty] [ty]
  ]

data IntSizedBitsCmp = ISB_DefinitelySmaller
                     | ISB_DefinitelyLarger
                     | ISB_EqualOrLarger
                     | ISB_EqualOrSmaller
                     | ISB_Equal

allSizes = [I32, I64, I8, I16, IWd, IDw]
allSizePairs = [(a, b) | a <- allSizes, b <- allSizes]

isbCompare a b =
  if a == b then ISB_Equal
    else case (a, b) of
            (I1,  _)   -> ISB_DefinitelySmaller

            (I8,  I1)  -> ISB_DefinitelyLarger
            (I8,  _ )  -> ISB_DefinitelySmaller

            (I16, I1)  -> ISB_DefinitelyLarger
            (I16, I8)  -> ISB_DefinitelyLarger
            (I16, _ )  -> ISB_DefinitelySmaller

            (I32, IWd) -> ISB_EqualOrSmaller
            (I32, I64) -> ISB_DefinitelySmaller
            (I32, IDw) -> ISB_DefinitelySmaller
            (I32, _  ) -> ISB_DefinitelyLarger

            (I64, IWd) -> ISB_EqualOrLarger
            (I64, IDw) -> ISB_EqualOrSmaller
            (I64, _  ) -> ISB_DefinitelyLarger

            (IWd, IDw) -> ISB_DefinitelySmaller
            (IWd, I64) -> ISB_EqualOrSmaller
            (IWd, _  ) -> ISB_DefinitelyLarger

            (IDw, I64) -> ISB_EqualOrLarger
            (IDw, _  ) -> ISB_DefinitelyLarger

isSmaller (a, b) =
  case isbCompare a b of
     ISB_DefinitelySmaller -> True
     ISB_DefinitelyLarger  -> False
     ISB_EqualOrLarger     -> False
     ISB_EqualOrSmaller    -> True
     ISB_Equal             -> False

isLarger (a, b) =
  case isbCompare a b of
     ISB_DefinitelySmaller -> False
     ISB_DefinitelyLarger  -> True
     ISB_EqualOrLarger     -> True
     ISB_EqualOrSmaller    -> False
     ISB_Equal             -> False

sizeConversions = [mkTruncate p | p <- allSizePairs, isLarger  p] ++
                  [mkSignExt  p | p <- allSizePairs, isSmaller p] ++
                  [mkZeroExt  p | p <- allSizePairs, isSmaller p]
  where
    mkSignExt  (a, b) = (,) (mkSignExtName  a b)     $ (,) (mkFnType [PrimIntAST a] [PrimIntAST b] ) $ PrimOpInt "sext" a b
    mkZeroExt  (a, b) = (,) (mkZeroExtName  a b)     $ (,) (mkFnType [PrimIntAST a] [PrimIntAST b] ) $ PrimOpInt "zext" a b
    mkTruncate (a, b) = (,) (mkTruncateName a b)     $ (,) (mkFnType [PrimIntAST a] [PrimIntAST b] ) $ PrimOpInt "trunc" a b
    mkTruncateName a b = T.pack $ "trunc_" ++ i a ++ "_to_" ++ i b
    mkSignExtName  a b = T.pack $ "sext_"  ++ i a ++ "_to_" ++ i b
    mkZeroExtName  a b = T.pack $ "zext_"  ++ i a ++ "_to_" ++ i b

    i IWd = "Word"
    i IDw = "WordX2"
    i I1  = "Bool"
    i I8  = "i8"
    i I16 = "i16"
    i I32 = "i32"
    i I64 = "i64"

unitTypeAST = TupleTypeAST KindPointerSized []

eqRefType = let a = BoundTyVar "a" (MissingSourceRange "==Ref") in
            ForAllAST (primTyVars [a])
              (mkProcType [RefTypeAST (TyVarAST a), RefTypeAST (TyVarAST a)] [fosBoolType])

eqBoxedType = let a = BoundTyVar "a" (MissingSourceRange "==Boxed") in
            ForAllAST (boxedTyVars [a])
              (mkProcType [(TyVarAST a), (TyVarAST a)] [fosBoolType])

eqArrayType = let a = BoundTyVar "a" (MissingSourceRange "==Ref") in
            ForAllAST (primTyVars [a])
              (mkProcType [ArrayTypeAST (TyVarAST a), ArrayTypeAST (TyVarAST a)] [fosBoolType])

-- These primitive names are known to the interpreter and compiler backends.
gFosterPrimOpsTable :: Map.Map T.Text (TypeAST, FosterPrim TypeAST)
gFosterPrimOpsTable = Map.fromList $
  [(,) "not"                  $ (,) (mkFnType [i1]  [i1]  ) $ PrimOp "bitnot" i1
  ,(,) "==Bool"               $ (,) (mkFnType [i1,i1][i1] ) $ PrimOp "==" i1
  ,(,) "==Ref"                $ (,) eqRefType               $ PrimOp "==" (RefTypeAST unitTypeAST)
  ,(,) "==Boxed"              $ (,) eqBoxedType             $ PrimOp "==" (unitTypeAST)
  ,(,) "sameArrayStorage"     $ (,) eqArrayType             $ PrimOp "==" (ArrayTypeAST unitTypeAST)
  ,(,) "f64-to-s32-unsafe"    $ (,) (mkFnType [f64] [i32] ) $ PrimOp "fptosi_f64_i32" i32
  ,(,) "f64-to-u32-unsafe"    $ (,) (mkFnType [f64] [i32] ) $ PrimOp "fptoui_f64_i32" i32
  ,(,) "f64-to-s64-unsafe"    $ (,) (mkFnType [f64] [i64] ) $ PrimOp "fptosi_f64_i64" i64
  ,(,) "f64-to-u64-unsafe"    $ (,) (mkFnType [f64] [i64] ) $ PrimOp "fptoui_f64_i64" i64
  ,(,) "s64-to-f64-unsafe"    $ (,) (mkFnType [i64] [f64] ) $ PrimOp "sitofp_f64" i64
  ,(,) "u64-to-f64-unsafe"    $ (,) (mkFnType [i64] [f64] ) $ PrimOp "uitofp_f64" i64
  ,(,) "s32-to-f64"           $ (,) (mkFnType [i32] [f64] ) $ PrimOp "sitofp_f64" i32
  ,(,) "u32-to-f64"           $ (,) (mkFnType [i32] [f64] ) $ PrimOp "uitofp_f64" i32
  ,(,) "f64-as-i64"           $ (,) (mkFnType [f64] [i64] ) $ PrimOp "bitcast" i64
  ,(,) "i64-as-f64"           $ (,) (mkFnType [i64] [f64] ) $ PrimOp "bitcast" f64
  ,(,) "f32-as-i32"           $ (,) (mkFnType [f32] [i32] ) $ PrimOp "bitcast" i32
  ,(,) "i32-as-f32"           $ (,) (mkFnType [i32] [f32] ) $ PrimOp "bitcast" f32
  ,(,) "s64-to-f32-unsafe"    $ (,) (mkFnType [i64] [f32] ) $ PrimOp "sitofp_f32" i64
  ,(,) "u64-to-f32-unsafe"    $ (,) (mkFnType [i64] [f32] ) $ PrimOp "uitofp_f32" i64
  ,(,) "s32-to-f32-unsafe"    $ (,) (mkFnType [i32] [f32] ) $ PrimOp "sitofp_f32" i32
  ,(,) "u32-to-f32-unsafe"    $ (,) (mkFnType [i32] [f32] ) $ PrimOp "uitofp_f32" i32
  ,(,) "f32-to-s32-unsafe"    $ (,) (mkFnType [f32] [i32] ) $ PrimOp "fptosi_f32_i32" i32
  ,(,) "f32-to-u32-unsafe"    $ (,) (mkFnType [f32] [i32] ) $ PrimOp "fptoui_f32_i32" i32
  ,(,) "f32-to-f64"           $ (,) (mkFnType [f32] [f64] ) $ PrimOp "fpext_f64" f32
  ,(,) "f64-to-f32"           $ (,) (mkFnType [f64] [f32] ) $ PrimOp "fptrunc_f32" f64
  ,(,) "Int-isSmall"          $ (,) (mkFnType [int] [i1 ] ) $ PrimOp "Int-isSmall" i1
  ,(,) "Int-toSmall"          $ (,) (mkFnType [int] [iwd] ) $ PrimOp "Int-toSmall" i1 -- TODO: Precondition: Int-isSmall
  ,(,) "Int-ofSmall"          $ (,) (mkFnType [iwd] [int] ) $ PrimOp "Int-ofSmall" i1 -- TODO: Precondition: Int-isSmallWord
  ,(,) "Int-toBig"            $ (,) (mkFnType [int] [big] ) $ PrimOp "Int-toBig" big -- TODO: Precondition: !isSmall
  ,(,) "Int-ofBig"            $ (,) (mkFnType [big] [int] ) $ PrimOp "Int-ofBig" int -- No precondition!
  
  ] ++ concatMap fixnumPrimitives [I32, I64, I8, I16, IWd, IDw]
    ++ sizeConversions
    ++ flonumPrimitives "f64" f64
    ++ flonumPrimitives "f32" f32
