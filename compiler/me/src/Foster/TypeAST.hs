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

import Data.IORef(IORef)
import Data.Map as Map(fromList, toList)
import Data.Char as Char(isLetter)

import Foster.Base
import Foster.Kind
import Foster.Output(out)

type AnnVar = TypedId TypeAST

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere

data TypeAST =
           PrimIntAST       IntSizeBits
         | PrimFloat64
         | TyConAppAST      DataTypeName [Sigma]
         | TupleTypeAST     [Sigma]
         | CoroTypeAST      Sigma Sigma
         | RefTypeAST       Sigma
         | ArrayTypeAST     Sigma
         | FnTypeAST        { fnTypeDomain :: Sigma
                            , fnTypeRange  :: Sigma
                            , fnTypeCallConv :: CallConv
                            , fnTypeProcOrFunc :: ProcOrFunc }
         | ForAllAST        [(TyVar, Kind)] Rho
         | TyVarAST         TyVar
         | MetaTyVar        MetaTyVar

data MTVQ = MTVSigma | MTVTau deriving (Eq)
data MetaTyVar = Meta { mtvConstraint :: MTVQ
                      , mtvDesc       :: String
                      , mtvUniq       :: Uniq
                      , mtvRef        :: TyRef
                      }

type TyRef = IORef (Maybe TypeAST)
    -- Nothing: type variable not substituted
    -- Just ty: ty var has been substituted by ty

instance Eq MetaTyVar where
  m1 == m2 = case (mtvUniq m1 == mtvUniq m2, mtvRef m1 == mtvRef m2) of
       (True,  True)  -> True
       (False, False) -> False
       _ -> error $ "Malformed meta type variables "
         ++ show (mtvUniq m1) ++ "@" ++ (mtvDesc m1) ++ " and "
         ++ show (mtvUniq m2) ++ "@" ++ (mtvDesc m2) ++ ": mismatch between uniqs and refs!"

instance Show TypeAST where
    show x = case x of
        PrimIntAST         size         -> "(PrimIntAST " ++ show size ++ ")"
        PrimFloat64                     -> "(PrimFloat64)"
        TyConAppAST    tc types         -> "(TyCon: " ++ show tc ++ joinWith " " ("":map show types) ++ ")"
        TupleTypeAST      types         -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeAST    s t cc cs          -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeAST  s t                -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllAST  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarAST   tv                   -> show tv
        MetaTyVar m                     -> "(~!" ++ show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")"
        RefTypeAST    ty                -> "(Ref " ++ show ty ++ ")"
        ArrayTypeAST  ty                -> "(Array " ++ show ty ++ ")"

instance Structured TypeAST where
    textOf e _width =
        case e of
            PrimIntAST     size            -> out $ "PrimIntAST " ++ show size
            PrimFloat64                    -> out $ "PrimFloat64"
            TyConAppAST    tc  _           -> out $ "TyConAppAST " ++ tc
            TupleTypeAST       _           -> out $ "TupleTypeAST"
            FnTypeAST    _ _  _  _         -> out $ "FnTypeAST"
            CoroTypeAST  _ _               -> out $ "CoroTypeAST"
            ForAllAST  tvs _rho            -> out $ "ForAllAST " ++ show tvs
            TyVarAST   tv                  -> out $ "TyVarAST " ++ show tv
            MetaTyVar m                    -> out $ "MetaTyVar " ++ mtvDesc m
            RefTypeAST    _                -> out $ "RefTypeAST"
            ArrayTypeAST  _                -> out $ "ArrayTypeAST"

    childrenOf e =
        case e of
            PrimIntAST         _           -> []
            PrimFloat64                    -> []
            TyConAppAST   _tc types        -> types
            TupleTypeAST      types        -> types
            FnTypeAST    s t _ _           -> [s, t]
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

mkProcType args rets = FnTypeAST (TupleTypeAST args) (minimalTupleAST rets) CCC    FT_Proc
mkFnType   args rets = FnTypeAST (TupleTypeAST args) (minimalTupleAST rets) FastCC FT_Func
mkCoroType args rets = CoroTypeAST (minimalTupleAST args) (minimalTupleAST rets)
i8  = PrimIntAST I8
i32 = PrimIntAST I32
i64 = PrimIntAST I64
i1  = PrimIntAST I1

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

    ,(,) "prim_print_bytes_stdout" $ mkProcType [ArrayTypeAST i8, i32] []
    ,(,) "prim_print_bytes_stderr" $ mkProcType [ArrayTypeAST i8, i32] []

    ,(,) "print_float_p9f64"       $ mkProcType [PrimFloat64] []
    ,(,) "expect_float_p9f64"      $ mkProcType [PrimFloat64] []

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
  ] ++ fixnumPrimitives I64
    ++ fixnumPrimitives I32
    ++ fixnumPrimitives I8
    ++ flonumPrimitives "f64" PrimFloat64
