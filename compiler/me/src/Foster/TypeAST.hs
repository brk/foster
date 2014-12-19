-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST(
  TypeAST(..), IntSizeBits(..)
, MetaTyVar(..), Sigma, Rho, Tau, MTVQ(..)
, fosBoolType, fosStringType, gFosterPrimOpsTable, primitiveDecls
, minimalTupleAST
, mkFnType, convertTyFormal
)
where

import Data.Map as Map(fromList, toList, Map)
import Data.Char as Char(isLetter)

import Text.PrettyPrint.ANSI.Leijen

import Foster.Base
import Foster.Kind
import Foster.ExprAST

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere

data TypeAST =
           PrimIntAST       IntSizeBits
         | PrimFloat64AST
         | TyConAppAST      DataTypeName [Sigma]
         | TupleTypeAST     [Sigma]
         | CoroTypeAST      (Sigma) (Sigma)
         | RefTypeAST       (Sigma)
         | ArrayTypeAST     (Sigma)
         | FnTypeAST        { fnTypeDomain :: [Sigma]
                            , fnTypeRange  ::  Sigma
                            , fnTypeCallConv :: CallConv
                            , fnTypeProcOrFunc :: ProcOrFunc }
         | ForAllAST        [(TyVar, Kind)] (Rho)
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
         ++ show (mtvUniq m1) ++ "@" ++ (mtvDesc m1) ++ " and "
         ++ show (mtvUniq m2) ++ "@" ++ (mtvDesc m2) ++ ": mismatch between uniqs and refs!"

hpre [] = empty
hpre ds = empty <+> hsep ds

instance Pretty TypeAST where
    pretty x = case x of
        PrimIntAST         size         -> pretty size
        PrimFloat64AST                  -> text "Float64"
        TyConAppAST  tcnm types         -> parens $ text tcnm <> hpre (map pretty types)
        TupleTypeAST      types         -> tupled $ map pretty types
        FnTypeAST    s t  cc cs         -> text "(" <> pretty s <> text " =" <> text (briefCC cc) <> text "> " <> pretty t <> text " @{" <> text (show cs) <> text "})"
        CoroTypeAST  s t                -> text "(Coro " <> pretty s <> text " " <> pretty t <> text ")"
        ForAllAST  tvs rho              -> text "(forall " <> hsep (prettyTVs tvs) <> text ". " <> pretty rho <> text ")"
        TyVarAST   tv                   -> text (show tv)
        -- MetaTyVar m                     -> text "(~(" <> pretty (descMTVQ (mtvConstraint m)) <> text ")!" <> text (show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")")
        RefTypeAST    ty                -> text "(Ref " <> pretty ty <> text ")"
        ArrayTypeAST  ty                -> text "(Array " <> pretty ty <> text ")"
        RefinedTypeAST _nm ty _e        -> text "(Refined " <> pretty ty <> text ")"
        MetaPlaceholderAST _ nm         -> text "(.meta " <> text nm <> text ")"

prettyTVs tvs = map (\(tv,k) -> parens (pretty tv <+> text "::" <+> pretty k)) tvs

instance Show TypeAST where show x = show (pretty x)
  {-
instance Show TypeAST where
    show x = case x of
        PrimIntAST         size         -> "(PrimIntAST " ++ show size ++ ")"
        PrimFloat64AST                  -> "(PrimFloat64)"
        TyConAppAST    tc types         -> "(TyCon: " ++ show tc ++ joinWith " " ("":map show types) ++ ")"
        TupleTypeAST      types         -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeAST    s t cc cs          -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeAST  s t                -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllAST  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarAST   tv                   -> show tv
        MetaTyVar m                     -> "(~(" ++ descMTVQ (mtvConstraint m) ++ ")!" ++ show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")"
        RefTypeAST    ty                -> "(Ref " ++ show ty ++ ")"
        ArrayTypeAST  ty                -> "(Array " ++ show ty ++ ")"
-}

descMTVQ MTVSigma = "S"
descMTVQ MTVTau   = "R"

instance Structured TypeAST where
    textOf e _width =
        case e of
            PrimIntAST     size            -> text $ "PrimIntAST " ++ show size
            PrimFloat64AST                 -> text $ "PrimFloat64"
            TyConAppAST    tc  _           -> text $ "TyConAppAST " ++ tc
            TupleTypeAST       _           -> text $ "TupleTypeAST"
            FnTypeAST    _ _    _ _        -> text $ "FnTypeAST"
            CoroTypeAST  _ _               -> text $ "CoroTypeAST"
            ForAllAST  tvs _rho            -> text $ "ForAllAST " ++ show tvs
            TyVarAST   tv                  -> text $ "TyVarAST " ++ show tv
            -- MetaTyVar m                    -> text $ "MetaTyVar " ++ mtvDesc m
            RefTypeAST    _                -> text $ "RefTypeAST"
            ArrayTypeAST  _                -> text $ "ArrayTypeAST"
            RefinedTypeAST {}              -> text $ "RefinedTypeAST"
            MetaPlaceholderAST mtvq _      -> text $ "MetaPlaceholderAST " ++ descMTVQ mtvq

    childrenOf e =
        case e of
            PrimIntAST         _           -> []
            PrimFloat64AST                 -> []
            TyConAppAST   _tc types        -> types
            TupleTypeAST      types        -> types
            FnTypeAST   ss t   _ _         -> ss ++ [t]
            CoroTypeAST  s t               -> [s, t]
            ForAllAST  _tvs rho            -> [rho]
            TyVarAST   _tv                 -> []
            -- MetaTyVar _                    -> []
            RefTypeAST    ty               -> [ty]
            ArrayTypeAST  ty               -> [ty]
            RefinedTypeAST _ ty _          -> [ty]
            MetaPlaceholderAST {}          -> []

fosBoolType = PrimIntAST I1
fosStringType = TyConAppAST "Text" []

minimalTupleAST []    = TupleTypeAST []
minimalTupleAST [arg] = arg
minimalTupleAST args  = TupleTypeAST args

mkProcType args rets = FnTypeAST args (minimalTupleAST rets) CCC    FT_Proc
mkFnType   args rets = FnTypeAST args (minimalTupleAST rets) FastCC FT_Func
mkCoroType args rets = CoroTypeAST (minimalTupleAST args) (minimalTupleAST rets)

--------------------------------------------------------------------------------

i8  = PrimIntAST I8
i32 = PrimIntAST I32
i64 = PrimIntAST I64
i1  = PrimIntAST I1
iw0 = PrimIntAST (IWord 0)
iw1 = PrimIntAST (IWord 1)
f64 = PrimFloat64AST

primTyVars tyvars = map (\v -> (v, KindAnySizeType)) tyvars

-- These names correspond to (the C symbols of)
-- functions implemented by the Foster runtime.

primitiveDecls =
    [(,) "expect_i32"  $ mkProcType [i32] []
    ,(,)  "print_i32"  $ mkProcType [i32] []
    ,(,) "expect_i32x" $ mkProcType [i32] []
    ,(,)  "print_i32x" $ mkProcType [i32] []
    ,(,) "expect_i64"  $ mkProcType [i64] []
    ,(,)  "print_i64"  $ mkProcType [i64] []
    ,(,) "expect_i64x" $ mkProcType [i64] []
    ,(,)  "print_i64x" $ mkProcType [i64] []
    ,(,)  "print_i64_bare"  $ mkProcType [i64] []

    ,(,) "expect_i1"   $ mkProcType [i1] []
    ,(,)  "print_i1"   $ mkProcType [i1] []
    ,(,) "expect_i8"   $ mkProcType [i8] []
    ,(,)  "print_i8"   $ mkProcType [i8] []
    ,(,) "expect_i8x"  $ mkProcType [i8] []
    ,(,)  "print_i8x"  $ mkProcType [i8] []
    ,(,) "expect_i8b"  $ mkProcType [i8] []
    ,(,)  "print_i8b"  $ mkProcType [i8] []
    ,(,) "expect_i32b" $ mkProcType [i32] []
    ,(,)  "print_i32b" $ mkProcType [i32] []
    ,(,) "expect_i64b" $ mkProcType [i64] []
    ,(,)  "print_i64b" $ mkProcType [i64] []

    ,(,) "opaquely_i32" $ mkProcType [i32] [i32]
    ,(,) "opaquely_i64" $ mkProcType [i64] [i64]
    ,(,) "get_cmdline_arg_n" $ mkProcType [i32] [TyConAppAST "Text" []]

    ,(,) "expect_newline" $ mkProcType [] []
    ,(,) "print_newline" $ mkProcType [] []

    ,(,) "memcpy_i8_to_from_at_len" $ mkProcType [ArrayTypeAST i8,
                                                  ArrayTypeAST i8, i32, i32] []
    ,(,) "memcpy_i8_to_at_from_len" $ mkProcType [ArrayTypeAST i8, i32,
                                                  ArrayTypeAST i8, i32] []
    ,(,) "memcpy_i8_to_at_from_at_len" $ mkProcType [ArrayTypeAST i8, i64,
                                                     ArrayTypeAST i8, i64, i64] []

    ,(,) "prim_print_bytes_stdout" $ mkProcType [ArrayTypeAST i8, i32] []
    ,(,) "prim_print_bytes_stderr" $ mkProcType [ArrayTypeAST i8, i32] []

    ,(,) "print_float_p9f64"       $ mkProcType [f64] []
    ,(,) "expect_float_p9f64"      $ mkProcType [f64] []

    -- Calls to this function are internally transformed to AIAllocArray nodes.
    -- forall a, i32 -> Array a
    ,(,) "allocDArray" $ let a = BoundTyVar "a" (MissingSourceRange "allocDArray") in
                         ForAllAST (primTyVars [a])
                           (mkProcType [i32] [ArrayTypeAST (TyVarAST a)])

    -- forall a, Array a -> i64
    ,(,) "prim_arrayLength" $ let a = BoundTyVar "a" (MissingSourceRange "prim_arrayLength") in
                         ForAllAST (primTyVars [a])
                           (mkProcType [ArrayTypeAST (TyVarAST a)] [i64])

    -- forall a b, (a -> b) -> Coro a b
    ,(,) "coro_create" $ let a = BoundTyVar "a" (MissingSourceRange "coro_create") in
                         let b = BoundTyVar "b" (MissingSourceRange "coro_create") in
                         (ForAllAST (primTyVars [a, b])
                           (mkFnType [mkFnType   [TyVarAST a] [TyVarAST b]]
                                     [mkCoroType [TyVarAST a] [TyVarAST b]]))

    -- forall a b, (Coro a b, a) -> b
    ,(,) "coro_invoke" $ let a = BoundTyVar "a" (MissingSourceRange "coro_invoke") in
                         let b = BoundTyVar "b" (MissingSourceRange "coro_invoke") in
                         (ForAllAST (primTyVars [a, b])
                            (mkFnType [(mkCoroType [TyVarAST a] [TyVarAST b]), (TyVarAST a)]
                                      [TyVarAST b]))

    -- forall a b, (b -> a)
    -- (only not quite: a and b must be unifiable
    --  with the arg & return types of the containing function)
    ,(,) "coro_yield"  $ let a = BoundTyVar "a" (MissingSourceRange "coro_yield") in
                         let b = BoundTyVar "b" (MissingSourceRange "coro_yield") in
                         (ForAllAST (primTyVars [a, b])
                            (mkFnType [TyVarAST b] [TyVarAST a]))

    ,(,) "force_gc_for_debugging_purposes" $ mkFnType [] [i32]

    -- TODO this is not correct for Solaris, AIX, or SGI/Irix,
    -- which use structs for time results, and is misleading on
    -- Alpha and Sparc v9, which have a 32-bit result.
    ,(,) "foster_getticks"         $ mkFnType [] [i64]
    ,(,) "foster_getticks_elapsed" $ mkFnType [i64, i64] [f64]

    ,(,) "foster_fmttime_secs"     $ mkFnType [f64] [TyConAppAST "Text" []]
    ,(,) "foster_gettime_microsecs"    $ mkFnType [] [i64]
    ,(,) "foster_gettime_elapsed_secs" $ mkFnType [i64, i64] [f64]

    ] ++ (map (\(name, (ty, _op)) -> (name, ty)) $ Map.toList gFosterPrimOpsTable)

intSize I1  = "Bool"
intSize I8  = "Int8"
--intSize I16 = "Int16"
intSize I32 = "Int32"
intSize I64 = "Int64"
intSize (IWord 0) = "Word"
intSize (IWord 1) = "WordX2"
intSize (IWord x) = error $ "Unable to handle Word " ++ show x

prettyOpName nm tystr =
  if Char.isLetter (head nm)
    then nm ++ "-" ++ tystr  -- e.g. "bitand-Int32"
    else nm ++        tystr  -- e.g. "+Int32"

-- Note: we don't wrap LLVM's shift intrisics directly; we mask the shift
-- value to avoid undefined values. For constant shift values, the mask will
-- be trivially eliminated by LLVM.
fixnumPrimitives bitsize =
  let iKK = PrimIntAST bitsize in
  let mkPrim nm ty = (prettyOpName nm (intSize bitsize), (ty, PrimOp nm iKK)) in
  [( "<U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  "<u" iKK))
  ,( ">U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  ">u" iKK))
  ,("<=U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp "<=u" iKK))
  ,(">=U" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp ">=u" iKK))
  ,( "<S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  "<s" iKK))
  ,( ">S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp  ">s" iKK))
  ,("<=S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp "<=s" iKK))
  ,(">=S" ++ (intSize bitsize), (mkFnType [iKK, iKK] [i1], PrimOp ">=s" iKK))
  ] ++
  [mkPrim "+"           $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "-"           $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "*"           $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "+uc"         $ mkFnType [iKK, iKK] [iKK] -- checked variants
  ,mkPrim "-uc"         $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "*uc"         $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "+sc"         $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "-sc"         $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "*sc"         $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitand"      $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitor"       $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitxor"      $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitshl"      $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitlshr"     $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitashr"     $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "srem-unsafe" $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "sdiv-unsafe" $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "urem-unsafe" $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "udiv-unsafe" $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "=="          $ mkFnType [iKK, iKK] [i1]
  ,mkPrim "!="          $ mkFnType [iKK, iKK] [i1]
  ,mkPrim "negate"      $ mkFnType [iKK]      [iKK]
  ,mkPrim "bitnot"      $ mkFnType [iKK]      [iKK]
  ,mkPrim "ctlz"        $ mkFnType [iKK]      [iKK]
  ,mkPrim "ctpop"       $ mkFnType [iKK]      [iKK]
  ]

-- For example, we'll have a function with external signature
--      (+f64) :: Float64 -> Float64 -> Float64
-- and internal signature
--      (PrimOp "f+" PrimFloat64AST)
flonumPrimitives tystr ty =
  let mkPrim nm fnty = (prettyOpName nm tystr, (fnty, PrimOp ("f" ++ nm) ty)) in
  [mkPrim "+"       $ mkFnType [ty, ty] [ty]
  ,mkPrim "-"       $ mkFnType [ty, ty] [ty]
  ,mkPrim "*"       $ mkFnType [ty, ty] [ty]
  ,mkPrim "div"     $ mkFnType [ty, ty] [ty]
  ,mkPrim "<"       $ mkFnType [ty, ty] [i1]
  ,mkPrim ">"       $ mkFnType [ty, ty] [i1]
  ,mkPrim "<="      $ mkFnType [ty, ty] [i1]
  ,mkPrim ">="      $ mkFnType [ty, ty] [i1]
  ,mkPrim "=="      $ mkFnType [ty, ty] [i1]
  ,mkPrim "!="      $ mkFnType [ty, ty] [i1]
  ,mkPrim "sqrt"    $ mkFnType [ty]     [ty]
  ,mkPrim "muladd"  $ mkFnType [ty, ty, ty] [ty]
  ]

-- These primitive names are known to the interpreter and compiler backends.
gFosterPrimOpsTable :: Map.Map String (TypeAST, FosterPrim TypeAST)
gFosterPrimOpsTable = Map.fromList $
  [(,) "not"                  $ (,) (mkFnType [i1]  [i1]  ) $ PrimOp "bitnot" i1
  ,(,) "==Bool"               $ (,) (mkFnType [i1,i1][i1] ) $ PrimOp "==" i1
  ,(,) "sext_i32_to_i64"      $ (,) (mkFnType [i32] [i64] ) $ PrimOp "sext_i64" i32
  ,(,) "zext_i32_to_i64"      $ (,) (mkFnType [i32] [i64] ) $ PrimOp "zext_i64" i32
  ,(,) "zext_Word_to_i64"     $ (,) (mkFnType [iw0] [i64] ) $ PrimOp "zext_i64" iw0
  ,(,) "sext_Word_to_i64"     $ (,) (mkFnType [iw0] [i64] ) $ PrimOp "sext_i64" iw0
  ,(,) "sext_i8_to_i32"       $ (,) (mkFnType [i8 ] [i32] ) $ PrimOp "sext_i32" i8
  ,(,) "zext_i8_to_i32"       $ (,) (mkFnType [i8 ] [i32] ) $ PrimOp "zext_i32" i8
  ,(,) "sext_i8_to_i64"       $ (,) (mkFnType [i8 ] [i64] ) $ PrimOp "sext_i64" i8
  ,(,) "zext_i8_to_i64"       $ (,) (mkFnType [i8 ] [i64] ) $ PrimOp "zext_i64" i8
  ,(,) "sext_i8_to_Word"      $ (,) (mkFnType [i8 ] [iw0] ) $ PrimOp "sext_Word"   i8
  ,(,) "zext_i8_to_Word"      $ (,) (mkFnType [i8 ] [iw0] ) $ PrimOp "zext_Word"   i8
  ,(,) "sext_i32_to_Word"     $ (,) (mkFnType [i32] [iw0] ) $ PrimOp "sext_Word"   i32
  ,(,) "zext_i32_to_Word"     $ (,) (mkFnType [i32] [iw0] ) $ PrimOp "zext_Word"   i32
  ,(,) "zext_i32_to_WordX2"   $ (,) (mkFnType [i32] [iw1] ) $ PrimOp "zext_WordX2" i32
  ,(,) "zext_Word_to_WordX2"  $ (,) (mkFnType [iw0] [iw1] ) $ PrimOp "zext_WordX2" iw0
  ,(,) "sext_Word_to_WordX2"  $ (,) (mkFnType [iw0] [iw1] ) $ PrimOp "sext_WordX2" iw0
  ,(,) "trunc_i32_to_i8"      $ (,) (mkFnType [i32] [i8 ] ) $ PrimIntTrunc I32 I8
  ,(,) "trunc_i64_to_i8"      $ (,) (mkFnType [i64] [i8 ] ) $ PrimIntTrunc I64 I8
  ,(,) "trunc_i64_to_i32"     $ (,) (mkFnType [i64] [i32] ) $ PrimIntTrunc I64 I32
  ,(,) "trunc_i64_to_Word"    $ (,) (mkFnType [i64] [iw0] ) $ PrimIntTrunc I64 (IWord 0)
  ,(,) "trunc_Word_to_i32"    $ (,) (mkFnType [iw0] [i32] ) $ PrimIntTrunc (IWord 0) I32
  ,(,) "trunc_Word_to_i8"     $ (,) (mkFnType [iw0] [i8 ] ) $ PrimIntTrunc (IWord 0) I8
  ,(,) "trunc_WordX2_to_i32"  $ (,) (mkFnType [iw1] [i32] ) $ PrimIntTrunc (IWord 1) I32
  ,(,) "trunc_WordX2_to_Word" $ (,) (mkFnType [iw1] [iw0] ) $ PrimIntTrunc (IWord 1) (IWord 0)
  ,(,) "f64-to-s32-unsafe"    $ (,) (mkFnType [f64] [i32] ) $ PrimOp "fptosi_f64_i32" i32
  ,(,) "f64-to-u32-unsafe"    $ (,) (mkFnType [f64] [i32] ) $ PrimOp "fptoui_f64_i32" i32
  ,(,) "f64-to-s64-unsafe"    $ (,) (mkFnType [f64] [i64] ) $ PrimOp "fptosi_f64_i64" i64
  ,(,) "f64-to-u64-unsafe"    $ (,) (mkFnType [f64] [i64] ) $ PrimOp "fptoui_f64_i64" i64
  ,(,) "s32-to-f64"    $(,) (mkFnType [i32] [f64]     ) $ PrimOp "sitofp_f64" i32
  ,(,) "u32-to-f64"    $(,) (mkFnType [i32] [f64]     ) $ PrimOp "uitofp_f64" i32
  ] ++ fixnumPrimitives I64
    ++ fixnumPrimitives I32
    ++ fixnumPrimitives I8
    ++ flonumPrimitives "f64" PrimFloat64AST
    ++ fixnumPrimitives (IWord 0)
    ++ fixnumPrimitives (IWord 1)
