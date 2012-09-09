-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST(
  TypeAST(..), EPattern(..), E_VarAST(..), IntSizeBits(..), AnnVar
, MetaTyVar(..), Sigma, Rho, Tau, MTVQ(..)
, fosBoolType, fosStringType
, minimalTupleAST
, mkFnType, convertTyFormal
, gFosterPrimOpsTable, primitiveDecls
)
where

import Data.Map as Map(fromList, toList)
import Data.Char as Char(isLetter)
import Text.PrettyPrint.ANSI.Leijen

import Foster.Base
import Foster.Kind

type AnnVar = TypedId TypeAST

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere

data TypeAST =
           PrimIntAST       IntSizeBits
         | PrimFloat64AST
         | TyConAppAST      DataTypeName [Sigma]
         | TupleTypeAST     [Sigma]
         | CoroTypeAST      Sigma Sigma
         | RefTypeAST       Sigma
         | ArrayTypeAST     Sigma
         | FnTypeAST        { fnTypeDomain :: [Sigma]
                            , fnTypeRange  :: Sigma
                            , fnTypeCallConv :: CallConv
                            , fnTypeProcOrFunc :: ProcOrFunc }
         | ForAllAST        [(TyVar, Kind)] Rho
         | TyVarAST         TyVar
         | MetaTyVar        (MetaTyVar TypeAST)

instance Eq (MetaTyVar t) where
  m1 == m2 = case (mtvUniq m1 == mtvUniq m2, mtvRef m1 == mtvRef m2) of
       (True,  True)  -> True
       (False, False) -> False
       _ -> error $ "Malformed meta type variables "
         ++ show (mtvUniq m1) ++ "@" ++ (mtvDesc m1) ++ " and "
         ++ show (mtvUniq m2) ++ "@" ++ (mtvDesc m2) ++ ": mismatch between uniqs and refs!"


instance Pretty TypeAST where
    pretty x = case x of
        PrimIntAST         size         -> text "Int" <> pretty size
        PrimFloat64AST                  -> text "Float64"
        TyConAppAST    tc types         -> parens $ text (show tc) <+> hsep (map pretty types)
        TupleTypeAST      types         -> tupled $ map pretty types
        FnTypeAST    s t cc cs          -> text "(" <> pretty s <> text " =" <> text (briefCC cc) <> text "> " <> pretty t <> text " @{" <> text (show cs) <> text "})"
        CoroTypeAST  s t                -> text "(Coro " <> pretty s <> text " " <> pretty t <> text ")"
        ForAllAST  tvs rho              -> text "(forall " <> hsep (prettyTVs tvs) <> text ". " <> pretty rho <> text ")"
        TyVarAST   tv                   -> text (show tv)
        MetaTyVar m                     -> text "(~(" <> pretty (descMTVQ (mtvConstraint m)) <> text ")!" <> text (show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")")
        RefTypeAST    ty                -> text "(Ref " <> pretty ty <> text ")"
        ArrayTypeAST  ty                -> text "(Array " <> pretty ty <> text ")"

prettyTVs tvs = map (\(tv,k) -> parens (pretty tv <+> text "::" <+> pretty k)) tvs

instance Pretty Kind where
  pretty KindAnySizeType = text "Type"
  pretty KindPointerSized = text "Boxed"

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
            FnTypeAST    _ _  _  _         -> text $ "FnTypeAST"
            CoroTypeAST  _ _               -> text $ "CoroTypeAST"
            ForAllAST  tvs _rho            -> text $ "ForAllAST " ++ show tvs
            TyVarAST   tv                  -> text $ "TyVarAST " ++ show tv
            MetaTyVar m                    -> text $ "MetaTyVar " ++ mtvDesc m
            RefTypeAST    _                -> text $ "RefTypeAST"
            ArrayTypeAST  _                -> text $ "ArrayTypeAST"

    childrenOf e =
        case e of
            PrimIntAST         _           -> []
            PrimFloat64AST                 -> []
            TyConAppAST   _tc types        -> types
            TupleTypeAST      types        -> types
            FnTypeAST   ss t _ _           -> ss ++ [t]
            CoroTypeAST  s t               -> [s, t]
            ForAllAST  _tvs rho            -> [rho]
            TyVarAST   _tv                 -> []
            MetaTyVar _                    -> []
            RefTypeAST    ty               -> [ty]
            ArrayTypeAST  ty               -> [ty]

convertTyFormal (TypeFormalAST name kind) = (BoundTyVar name, kind)

fosBoolType = i1
fosStringType = TyConAppAST "Text" []

minimalTupleAST []    = TupleTypeAST []
minimalTupleAST [arg] = arg
minimalTupleAST args  = TupleTypeAST args

mkProcType args rets = FnTypeAST args (minimalTupleAST rets) CCC    FT_Proc
mkFnType   args rets = FnTypeAST args (minimalTupleAST rets) FastCC FT_Func
mkCoroType args rets = CoroTypeAST (minimalTupleAST args) (minimalTupleAST rets)
i8  = PrimIntAST I8
i32 = PrimIntAST I32
i64 = PrimIntAST I64
i1  = PrimIntAST I1
f64 = PrimFloat64AST

primTyVars tyvars = map (\v -> (v, KindAnySizeType)) tyvars

-- These names correspond to (the C symbols of)
-- functions implemented by the Foster runtime.

primitiveDecls =
    [(,) "expect_i32"  $ mkProcType [i32] []
    ,(,)  "print_i32"  $ mkProcType [i32] []
    ,(,) "expect_i64"  $ mkProcType [i64] []
    ,(,)  "print_i64"  $ mkProcType [i64] []

    ,(,) "expect_i1"   $ mkProcType [i1] []
    ,(,)  "print_i1"   $ mkProcType [i1] []
    ,(,) "expect_i8"   $ mkProcType [i8] []
    ,(,)  "print_i8"   $ mkProcType [i8] []
    ,(,) "expect_i32b" $ mkProcType [i32] []
    ,(,)  "print_i32b" $ mkProcType [i32] []

    ,(,) "opaquely_i32" $ mkProcType [i32] [i32]
    ,(,) "get_cmdline_arg_n" $ mkProcType [i32] [fosStringType]

    ,(,) "expect_newline" $ mkProcType [] []
    ,(,) "print_newline" $ mkProcType [] []

    ,(,) "memcpy_i8_to_from_at_len" $ mkProcType [ArrayTypeAST i8,
                                                  ArrayTypeAST i8, i32, i32] []

    ,(,) "prim_print_bytes_stdout" $ mkProcType [ArrayTypeAST i8, i32] []
    ,(,) "prim_print_bytes_stderr" $ mkProcType [ArrayTypeAST i8, i32] []

    ,(,) "print_float_p9f64"       $ mkProcType [PrimFloat64AST] []
    ,(,) "expect_float_p9f64"      $ mkProcType [PrimFloat64AST] []

    -- Calls to this function are internally transformed to AIAllocArray nodes.
    -- forall a, i32 -> Array a
    ,(,) "allocDArray" $ let a = BoundTyVar "a" in
                         ForAllAST (primTyVars [a])
                           (mkProcType [i32] [ArrayTypeAST (TyVarAST a)])

    -- forall a, Array a -> i64
    ,(,) "prim_arrayLength" $ let a = BoundTyVar "a" in
                         ForAllAST (primTyVars [a])
                           (mkProcType [ArrayTypeAST (TyVarAST a)] [i64])

    -- forall a b, (a -> b) -> Coro a b
    ,(,) "coro_create" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAllAST (primTyVars [a, b])
                           (mkFnType [mkFnType   [TyVarAST a] [TyVarAST b]]
                                     [mkCoroType [TyVarAST a] [TyVarAST b]]))

    -- forall a b, (Coro a b, a) -> b
    ,(,) "coro_invoke" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAllAST (primTyVars [a, b])
                            (mkFnType [(mkCoroType [TyVarAST a] [TyVarAST b]), (TyVarAST a)]
                                      [TyVarAST b]))

    -- forall a b, (b -> a)
    -- (only not quite: a and b must be unifiable
    --  with the arg & return types of the containing function)
    ,(,) "coro_yield"  $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAllAST (primTyVars [a, b])
                            (mkFnType [TyVarAST b] [TyVarAST a]))

    ,(,) "force_gc_for_debugging_purposes" $ mkFnType [] []
    ,(,) "llvm_readcyclecounter" $ mkFnType [] [i64]

    ] ++ (map (\(name, (ty, _op)) -> (name, ty)) $ Map.toList gFosterPrimOpsTable)

intSize I1  = "Bool"
intSize I8  = "Int8"
intSize I32 = "Int32"
intSize I64 = "Int64"

prettyOpName nm tystr =
  if Char.isLetter (head nm)
    then nm ++ "-" ++ tystr  -- e.g. "bitand-Int32"
    else nm ++        tystr

fixnumPrimitives bitsize =
  let iKK = PrimIntAST bitsize in
  let mkPrim nm ty = (prettyOpName nm (intSize bitsize), (ty, PrimOp nm iKK)) in
  [mkPrim "+"       $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "-"       $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "*"       $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitand"  $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitor"   $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitxor"  $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitshl"  $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitlshr" $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "bitashr" $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "srem"    $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "sdiv"    $ mkFnType [iKK, iKK] [iKK]
  ,mkPrim "<"       $ mkFnType [iKK, iKK] [i1]
  ,mkPrim ">"       $ mkFnType [iKK, iKK] [i1]
  ,mkPrim "<="      $ mkFnType [iKK, iKK] [i1]
  ,mkPrim ">="      $ mkFnType [iKK, iKK] [i1]
  ,mkPrim "=="      $ mkFnType [iKK, iKK] [i1]
  ,mkPrim "!="      $ mkFnType [iKK, iKK] [i1]
  ,mkPrim "negate"  $ mkFnType [iKK]      [iKK]
  ,mkPrim "bitnot"  $ mkFnType [iKK]      [iKK]
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
  ]

-- These primitive names are known to the interpreter and compiler backends.
gFosterPrimOpsTable = Map.fromList $
  [(,) "not"                    $ (,) (mkFnType [i1]  [i1]      ) $ PrimOp "bitnot" i1
  ,(,) "primitive_sext_i64_i32" $ (,) (mkFnType [i32] [i64]     ) $ PrimOp "sext_i64" i32
  ,(,) "primitive_sext_i8_to_i32"$(,) (mkFnType [i8 ] [i32]     ) $ PrimOp "sext_i32" i8
  ,(,) "primitive_trunc_i32_i8" $ (,) (mkFnType [i32] [i8 ]     ) $ PrimIntTrunc I32 I8
  ,(,) "primitive_trunc_i64_i32"$ (,) (mkFnType [i64] [i32]     ) $ PrimIntTrunc I64 I32
  ,(,) "primitive_f64_to_i32"    $(,) (mkFnType [f64] [i32]     ) $ PrimOp "fptosi_f64_i32" i32
  ,(,) "primitive_i32_to_f64"    $(,) (mkFnType [i32] [f64]     ) $ PrimOp "sitofp_f64" i32
  ] ++ fixnumPrimitives I64
    ++ fixnumPrimitives I32
    ++ fixnumPrimitives I8
    ++ flonumPrimitives "f64" PrimFloat64AST
