-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST(
  TypeAST(..), IntSizeBits(..)
, MetaTyVar(..), Sigma, Rho, Tau, MTVQ(..)
, fosBoolType, fosStringType, gFosterPrimOpsTable, primitiveDecls, primopDecls
, minimalTupleAST
, convertTyFormal
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
type Effect = TypeAST

data TypeAST =
           PrimIntAST       IntSizeBits
         | TyConAST         DataTypeName
         | TyAppAST         Rho [Sigma]
         | TupleTypeAST     [Sigma]
         | CoroTypeAST      (Sigma) (Sigma) Effect
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
         ++ show (mtvUniq m1) ++ "@" ++ (mtvDesc m1) ++ " and "
         ++ show (mtvUniq m2) ++ "@" ++ (mtvDesc m2) ++ ": mismatch between uniqs and refs!"

hpre [] = empty
hpre ds = empty <+> hsep ds

instance Pretty TypeAST where
    pretty x = case x of
        PrimIntAST         size         -> pretty size
        TyConAST nam                    -> text nam
        TyAppAST con []     ->          pretty con
        TyAppAST con types  -> parens $ pretty con <> hpre (map pretty types)
        TupleTypeAST      types         -> tupled $ map pretty types
        FnTypeAST    s t fx cc cs       -> text "(" <> pretty s <> text " =" <> text (briefCC cc) <> text ";"
                                              <+> pretty fx <> text "> " <> pretty t <> text " @{" <> text (show cs) <> text "})"
        CoroTypeAST  s t fx             -> text "(Coro " <> pretty s <+> pretty t <+> pretty fx <> text ")"
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

instance Structured TypeAST where
    textOf e _width =
        case e of
            PrimIntAST     size            -> text $ "PrimIntAST " ++ show size
            TyConAST       nam             -> text $ nam
            TyAppAST con   _               -> text "(TyAppAST" <+> pretty con <> text ")"
            TupleTypeAST       _           -> text $ "TupleTypeAST"
            FnTypeAST    {}                -> text $ "FnTypeAST"
            CoroTypeAST  _ _ _             -> text $ "CoroTypeAST"
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
            TyConAST           _           -> []
            TyAppAST     con  types        -> con:types
            TupleTypeAST      types        -> types
            FnTypeAST   ss t fx _ _        -> ss ++ [t, fx]
            CoroTypeAST  s t fx            -> [s, t, fx]
            ForAllAST  _tvs rho            -> [rho]
            TyVarAST   _tv                 -> []
            -- MetaTyVar _                    -> []
            RefTypeAST    ty               -> [ty]
            ArrayTypeAST  ty               -> [ty]
            RefinedTypeAST _ ty _          -> [ty]
            MetaPlaceholderAST {}          -> []

fosBoolType = PrimIntAST I1
fosStringType = TyAppAST (TyConAST "Text") []

minimalTupleAST []    = TupleTypeAST []
minimalTupleAST [arg] = arg
minimalTupleAST args  = TupleTypeAST args

nullFx = TyAppAST (TyConAST "effect.Empty") []

mkProcType args rets = mkProcTypeWithFx nullFx args rets
mkFnType   args rets = mkFnTypeWithFx nullFx   args rets

mkProcTypeWithFx fx args rets = FnTypeAST args (minimalTupleAST rets) fx CCC    FT_Proc
mkFnTypeWithFx   fx args rets = FnTypeAST args (minimalTupleAST rets) fx FastCC FT_Func
mkCoroType args rets eff = CoroTypeAST (minimalTupleAST args) (minimalTupleAST rets) eff

--------------------------------------------------------------------------------
effectSingle :: String -> Effect
effectSingle name = effectExtend (TyAppAST (TyConAST name) []) nullFx

effectExtend :: Effect -> Effect -> Effect
effectExtend eff row = TyAppAST (TyConAST "effect.Extend") [eff, row]

effectsExtends :: [Effect] -> Effect -> Effect
effectsExtends effs eff = foldr effectExtend eff effs

effectsClosed :: [Effect] -> Effect
effectsClosed effs = effectsExtends effs nullFx

effectYield :: Tau -> Tau -> Effect
effectYield inp outp = effectExtend (TyAppAST (TyConAST "Yield") [inp, outp]) nullFx
--------------------------------------------------------------------------------

i8  = PrimIntAST I8
i16 = PrimIntAST I16
i32 = PrimIntAST I32
i64 = PrimIntAST I64
i1  = PrimIntAST I1
f64 = TyAppAST (TyConAST "Float64") []

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
    ,(,) "expect_i16"  $ mkProcType [i16] []
    ,(,)  "print_i16"  $ mkProcType [i16] []
    ,(,) "expect_i32b" $ mkProcType [i32] []
    ,(,)  "print_i32b" $ mkProcType [i32] []
    ,(,) "expect_i64b" $ mkProcType [i64] []
    ,(,)  "print_i64b" $ mkProcType [i64] []

    ,(,) "opaquely_i32" $ mkProcType [i32] [i32]
    ,(,) "opaquely_i64" $ mkProcType [i64] [i64]
    ,(,) "get_cmdline_arg_n" $ mkProcType [i32] [fosStringType]

    ,(,) "expect_newline" $ mkProcType [] []
    ,(,) "print_newline" $ mkProcType [] []

    ,(,) "memcpy_i8_to_from_at_len" $ mkProcType [ArrayTypeAST i8,
                                                ArrayTypeAST i8, i32, i32] []
    ,(,) "memcpy_i8_to_at_from_len" $ mkProcType [ArrayTypeAST i8, i32,
                                                ArrayTypeAST i8, i32] []
    ,(,) "memcpy_i8_to_at_from_at_len" $ mkProcType [ArrayTypeAST i8, i64,
                                                   ArrayTypeAST i8, i64, i64] [i8]

    ,(,) "prim_print_bytes_stdout" $ mkProcType [ArrayTypeAST i8, i32, i32] []
    ,(,) "prim_print_bytes_stderr" $ mkProcType [ArrayTypeAST i8, i32, i32] []

    ,(,) "print_float_p9f64"       $ mkProcType [f64] []
    ,(,) "expect_float_p9f64"      $ mkProcType [f64] []
    ,(,) "print_float_f64x"        $ mkProcType [f64] []
    ,(,) "expect_float_f64x"       $ mkProcType [f64] []

    ,(,) "foster__logf64"          $ mkProcType [f64] [f64]

    -- Calls to this function are internally transformed to AIAllocArray nodes.
    -- forall a, i32 -> Array a
    ,(,) "allocDArray" $ let a = BoundTyVar "a" (MissingSourceRange "allocDArray") in
                         ForAllAST (primTyVars [a])
                           (mkProcType [i32] [ArrayTypeAST (TyVarAST a)])

    -- forall a, Array a -> i64
    ,(,) "prim_arrayLength" $ let a = BoundTyVar "a" (MissingSourceRange "prim_arrayLength") in
                         ForAllAST (primTyVars [a])
                           (mkProcType [ArrayTypeAST (TyVarAST a)] [i64])

    -- forall a b e, { a => b  @(Yield a b | e) } -> Coro a b e
    ,(,) "coro_create" $ let a = BoundTyVar "a" (MissingSourceRange "coro_create") in
                         let b = BoundTyVar "b" (MissingSourceRange "coro_create") in
                         let fx = BoundTyVar "fx" (MissingSourceRange "coro_create") in
                         (ForAllAST (primTyVars [a, b] ++ [(fx, KindEffect)])
                           (mkFnType [mkFnTypeWithFx (effectExtend (effectYield (TyVarAST a) (TyVarAST b)) (TyVarAST fx))
                                                     [TyVarAST a] [TyVarAST b]]
                                     [mkCoroType [TyVarAST a] [TyVarAST b] (TyVarAST fx)]))

    -- TODO should probably include an IO effect on this, to reflect/expose
    --      the internal mutation occuring to track the coro state.
    -- forall a b e, (Coro a b e, a) -> b @e
    ,(,) "coro_invoke" $ let a = BoundTyVar "a" (MissingSourceRange "coro_invoke") in
                         let b = BoundTyVar "b" (MissingSourceRange "coro_invoke") in
                         let fx = BoundTyVar "fx" (MissingSourceRange "coro_invoke") in
                         (ForAllAST (primTyVars [a, b] ++ [(fx, KindEffect)])
                            (mkFnTypeWithFx (TyVarAST fx)
                               [(mkCoroType [TyVarAST a] [TyVarAST b] (TyVarAST fx)), (TyVarAST a)]
                                            [TyVarAST b]))

    -- forall a b, { b -> a  @(Yield a b) }
    ,(,) "coro_yield"  $ let a = BoundTyVar "a" (MissingSourceRange "coro_yield") in
                         let b = BoundTyVar "b" (MissingSourceRange "coro_yield") in
                         (ForAllAST (primTyVars [a, b])
                            (mkFnTypeWithFx (effectYield (TyVarAST a) (TyVarAST b))
                                [TyVarAST b] [TyVarAST a]))

    ,(,) "force_gc_for_debugging_purposes" $ mkProcType [] [i32]

    -- TODO this is not correct for Solaris, AIX, or SGI/Irix,
    -- which use structs for time results, and is misleading on
    -- Alpha and Sparc v9, which have a 32-bit result.
    ,(,) "foster_getticks"         $ mkProcType [] [i64]
    ,(,) "foster_getticks_elapsed" $ mkProcType [i64, i64] [f64]

    ,(,) "foster_fmttime_secs"     $ mkProcType [f64] [fosStringType]
    ,(,) "foster_gettime_microsecs"    $ mkProcType [] [i64]
    ,(,) "foster_gettime_elapsed_secs" $ mkProcType [i64, i64] [f64]
    ]

primopDecls = map (\(name, (ty, _op)) -> (name, ty)) $ Map.toList gFosterPrimOpsTable

intSize bitsize = show $ pretty bitsize

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
flonumPrimitives tystr ty =
  let mkPrim nm fnty = (prettyOpName nm tystr, (fnty, PrimOp ("f" ++ nm) ty)) in
  [mkPrim "+"       $ mkProcType [ty, ty] [ty]
  ,mkPrim "-"       $ mkProcType [ty, ty] [ty]
  ,mkPrim "*"       $ mkProcType [ty, ty] [ty]
  ,mkPrim "div"     $ mkProcType [ty, ty] [ty]
  ,mkPrim "<"       $ mkProcType [ty, ty] [i1]
  ,mkPrim ">"       $ mkProcType [ty, ty] [i1]
  ,mkPrim "<="      $ mkProcType [ty, ty] [i1]
  ,mkPrim ">="      $ mkProcType [ty, ty] [i1]
  ,mkPrim "=="      $ mkProcType [ty, ty] [i1]
  ,mkPrim "!="      $ mkProcType [ty, ty] [i1]
  ,mkPrim "sqrt"    $ mkProcType [ty]     [ty]
  ,mkPrim "powi"    $ mkProcType [ty, i32]    [ty]
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
            (I8,  _)   -> ISB_DefinitelySmaller
            (I16, _)   -> ISB_DefinitelySmaller

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
    mkSignExt  (a, b) = (,) (mkSignExtName  a b)     $ (,) (mkFnType [PrimIntAST a] [PrimIntAST b] ) $ PrimOp ("sext_" ++ i b) (PrimIntAST a)
    mkZeroExt  (a, b) = (,) (mkZeroExtName  a b)     $ (,) (mkFnType [PrimIntAST a] [PrimIntAST b] ) $ PrimOp ("zext_" ++ i b) (PrimIntAST a)
    mkTruncate (a, b) = (,) (mkTruncateName a b)     $ (,) (mkFnType [PrimIntAST a] [PrimIntAST b] ) $ PrimIntTrunc a b
    mkTruncateName a b = "trunc_" ++ i a ++ "_to_" ++ i b
    mkSignExtName  a b = "sext_"  ++ i a ++ "_to_" ++ i b
    mkZeroExtName  a b = "zext_"  ++ i a ++ "_to_" ++ i b

    i IWd = "Word"
    i IDw = "WordX2"
    i I1  = "Bool"
    i I8  = "i8"
    i I16 = "i16"
    i I32 = "i32"
    i I64 = "i64"

-- These primitive names are known to the interpreter and compiler backends.
gFosterPrimOpsTable :: Map.Map String (TypeAST, FosterPrim TypeAST)
gFosterPrimOpsTable = Map.fromList $
  [(,) "not"                  $ (,) (mkFnType [i1]  [i1]  ) $ PrimOp "bitnot" i1
  ,(,) "==Bool"               $ (,) (mkFnType [i1,i1][i1] ) $ PrimOp "==" i1
  {-
  ,(,) "sext_i32_to_i64"      $ (,) (mkFnType [i32] [i64] ) $ PrimOp "sext_i64" i32
  ,(,) "zext_i32_to_i64"      $ (,) (mkFnType [i32] [i64] ) $ PrimOp "zext_i64" i32
  ,(,) "zext_Word_to_i64"     $ (,) (mkFnType [iw0] [i64] ) $ PrimOp "zext_i64" iw0
  ,(,) "sext_Word_to_i64"     $ (,) (mkFnType [iw0] [i64] ) $ PrimOp "sext_i64" iw0
  ,(,) "sext_i8_to_i16"       $ (,) (mkFnType [i8 ] [i16] ) $ PrimOp "sext_i16" i8
  ,(,) "zext_i8_to_i16"       $ (,) (mkFnType [i8 ] [i16] ) $ PrimOp "zext_i16" i8
  ,(,) "sext_i8_to_i32"       $ (,) (mkFnType [i8 ] [i32] ) $ PrimOp "sext_i32" i8
  ,(,) "zext_i8_to_i32"       $ (,) (mkFnType [i8 ] [i32] ) $ PrimOp "zext_i32" i8
  ,(,) "sext_i8_to_i64"       $ (,) (mkFnType [i8 ] [i64] ) $ PrimOp "sext_i64" i8
  ,(,) "zext_i8_to_i64"       $ (,) (mkFnType [i8 ] [i64] ) $ PrimOp "zext_i64" i8
  ,(,) "sext_i8_to_Word"      $ (,) (mkFnType [i8 ] [iw0] ) $ PrimOp "sext_Word"   i8
  ,(,) "zext_i8_to_Word"      $ (,) (mkFnType [i8 ] [iw0] ) $ PrimOp "zext_Word"   i8
  ,(,) "sext_i16_to_i32"      $ (,) (mkFnType [i16] [i32] ) $ PrimOp "sext_i32"    i16
  ,(,) "zext_i16_to_i32"      $ (,) (mkFnType [i16] [i32] ) $ PrimOp "zext_i32"    i16
  ,(,) "sext_i16_to_i64"      $ (,) (mkFnType [i16] [i64] ) $ PrimOp "sext_i64"    i16
  ,(,) "zext_i16_to_i64"      $ (,) (mkFnType [i16] [i64] ) $ PrimOp "zext_i64"    i16
  ,(,) "sext_i16_to_Word"     $ (,) (mkFnType [i16] [iw0] ) $ PrimOp "sext_Word"   i16
  ,(,) "zext_i16_to_Word"     $ (,) (mkFnType [i16] [iw0] ) $ PrimOp "zext_Word"   i16
  ,(,) "sext_i32_to_Word"     $ (,) (mkFnType [i32] [iw0] ) $ PrimOp "sext_Word"   i32
  ,(,) "zext_i32_to_Word"     $ (,) (mkFnType [i32] [iw0] ) $ PrimOp "zext_Word"   i32
  ,(,) "zext_i32_to_WordX2"   $ (,) (mkFnType [i32] [iw1] ) $ PrimOp "zext_WordX2" i32
  ,(,) "zext_Word_to_WordX2"  $ (,) (mkFnType [iw0] [iw1] ) $ PrimOp "zext_WordX2" iw0
  ,(,) "sext_Word_to_WordX2"  $ (,) (mkFnType [iw0] [iw1] ) $ PrimOp "sext_WordX2" iw0
  ,(,) "trunc_i32_to_i8"      $ (,) (mkFnType [i32] [i8 ] ) $ PrimIntTrunc I32 I8
  ,(,) "trunc_i64_to_i8"      $ (,) (mkFnType [i64] [i8 ] ) $ PrimIntTrunc I64 I8
  ,(,) "trunc_i32_to_i16"     $ (,) (mkFnType [i32] [i16] ) $ PrimIntTrunc I32 I16
  ,(,) "trunc_i64_to_i16"     $ (,) (mkFnType [i64] [i16] ) $ PrimIntTrunc I64 I16
  ,(,) "trunc_i64_to_i32"     $ (,) (mkFnType [i64] [i32] ) $ PrimIntTrunc I64 I32
  ,(,) "trunc_i64_to_Word"    $ (,) (mkFnType [i64] [iw0] ) $ PrimIntTrunc I64 IWd
  ,(,) "trunc_Word_to_i32"    $ (,) (mkFnType [iw0] [i32] ) $ PrimIntTrunc IWd I32
  ,(,) "trunc_Word_to_i8"     $ (,) (mkFnType [iw0] [i8 ] ) $ PrimIntTrunc IWd I8
  ,(,) "trunc_WordX2_to_i32"  $ (,) (mkFnType [iw1] [i32] ) $ PrimIntTrunc IDw I32
  ,(,) "trunc_WordX2_to_Word" $ (,) (mkFnType [iw1] [iw0] ) $ PrimIntTrunc IDw IWd
  -}
  ,(,) "f64-to-s32-unsafe"    $ (,) (mkFnType [f64] [i32] ) $ PrimOp "fptosi_f64_i32" i32
  ,(,) "f64-to-u32-unsafe"    $ (,) (mkFnType [f64] [i32] ) $ PrimOp "fptoui_f64_i32" i32
  ,(,) "f64-to-s64-unsafe"    $ (,) (mkFnType [f64] [i64] ) $ PrimOp "fptosi_f64_i64" i64
  ,(,) "f64-to-u64-unsafe"    $ (,) (mkFnType [f64] [i64] ) $ PrimOp "fptoui_f64_i64" i64
  ,(,) "s64-to-f64-unsafe"    $ (,) (mkFnType [i64] [f64] ) $ PrimOp "sitofp_f64" i64
  ,(,) "u64-to-f64-unsafe"    $ (,) (mkFnType [i64] [f64] ) $ PrimOp "uitofp_f64" i64
  ,(,) "s32-to-f64"    $(,) (mkFnType [i32] [f64]     ) $ PrimOp "sitofp_f64" i32
  ,(,) "u32-to-f64"    $(,) (mkFnType [i32] [f64]     ) $ PrimOp "uitofp_f64" i32
  ,(,) "f64-as-i64"    $(,) (mkFnType [f64] [i64]     ) $ PrimOp "bitcast_i64" f64
  ,(,) "i64-as-f64"    $(,) (mkFnType [i64] [f64]     ) $ PrimOp "bitcast_f64" i64
  ] ++ concatMap fixnumPrimitives [I32, I64, I8, I16, IWd, IDw]
    ++ sizeConversions
    ++ flonumPrimitives "f64" f64
