-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST(
  TypeAST(..), EPattern(..), E_VarAST(..), IntSizeBits(..), AnnVar
, fosBoolType, MetaTyVar(Meta), Sigma, Rho, Tau
, minimalTupleAST
, mkFnType, convertTyFormal
, gFosterPrimOpsTable, primitiveDecls
)
where

import Data.IORef(IORef)
import Data.Map as Map(fromList, toList)

import Foster.Base
import Foster.Kind
import Foster.Output(out)

type AnnVar = TypedId TypeAST

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere

data TypeAST =
           PrimIntAST       IntSizeBits
         | TyConAppAST      DataTypeName [TypeAST]
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        { fnTypeDomain :: TypeAST
                            , fnTypeRange  :: TypeAST
                            , fnTypeCallConv :: CallConv
                            , fnTypeProcOrFunc :: ProcOrFunc }
         | CoroTypeAST      TypeAST TypeAST
         | ForAllAST        [(TyVar, Kind)] Rho
         | TyVarAST         TyVar
         | MetaTyVar        MetaTyVar
         | RefTypeAST       TypeAST
         | ArrayTypeAST     TypeAST

data MetaTyVar = Meta Uniq TyRef String

type TyRef = IORef (Maybe Tau)
    -- Nothing: type variable not substituted
    -- Just ty: ty var has been substituted by ty

instance Show TypeAST where
    show x = case x of
        PrimIntAST         size         -> "(PrimIntAST " ++ show size ++ ")"
        TyConAppAST    tc types         -> "(TyCon: " ++ show tc ++ joinWith " " ("":map show types) ++ ")"
        TupleTypeAST      types         -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeAST    s t cc cs          -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeAST  s t                -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllAST  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarAST   tv                   -> show tv
        MetaTyVar (Meta u _tyref desc)  -> "(~!" ++ show u ++ ":" ++ desc ++ ")"
        RefTypeAST    ty                -> "(Ref " ++ show ty ++ ")"
        ArrayTypeAST  ty                -> "(Array " ++ show ty ++ ")"

instance Structured TypeAST where
    textOf e _width =
        case e of
            PrimIntAST     size            -> out $ "PrimIntAST " ++ show size
            TyConAppAST    tc  _           -> out $ "TyConAppAST " ++ tc
            TupleTypeAST       _           -> out $ "TupleTypeAST"
            FnTypeAST    _ _  _  _         -> out $ "FnTypeAST"
            CoroTypeAST  _ _               -> out $ "CoroTypeAST"
            ForAllAST  tvs _rho            -> out $ "ForAllAST " ++ show tvs
            TyVarAST   tv                  -> out $ "TyVarAST " ++ show tv
            MetaTyVar (Meta _ _tyref desc) -> out $ "MetaTyVar " ++ desc
            RefTypeAST    _                -> out $ "RefTypeAST"
            ArrayTypeAST  _                -> out $ "ArrayTypeAST"

    childrenOf e =
        case e of
            PrimIntAST         _           -> []
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

minimalTupleAST []    = TupleTypeAST []
minimalTupleAST [arg] = arg
minimalTupleAST args  = TupleTypeAST args

mkProcType args rets = FnTypeAST (TupleTypeAST args) (minimalTupleAST rets) CCC    FT_Proc
mkFnType   args rets = FnTypeAST (TupleTypeAST args) (minimalTupleAST rets) FastCC FT_Func
mkCoroType args rets = CoroTypeAST (minimalTupleAST args) (minimalTupleAST rets)
i32 = PrimIntAST I32
i64 = PrimIntAST I64
i1  = PrimIntAST I1

primTyVars tyvars = map (\v -> (v, KindAnySizeType)) tyvars

primitiveDecls =
    [(,) "expect_i32"  $ mkProcType [i32] []
    ,(,)  "print_i32"  $ mkProcType [i32] []
    ,(,) "expect_i64"  $ mkProcType [i64] []
    ,(,)  "print_i64"  $ mkProcType [i64] []

    ,(,) "expect_i1"   $ mkProcType [i1] []
    ,(,)  "print_i1"   $ mkProcType [i1] []
    ,(,) "expect_i32b" $ mkProcType [i32] []
    ,(,)  "print_i32b" $ mkProcType [i32] []

    ,(,) "opaquely_i32" $ mkProcType [i32] [i32]

    -- forall a, i32 -> Array a
    ,(,) "allocDArray" $ let a = BoundTyVar "a" in
                         ForAllAST (primTyVars [a])
                           (mkProcType [i32] [ArrayTypeAST (TyVarAST a)])

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

gFosterPrimOpsTable = Map.fromList $
  [(,) "not"           $ (,) (mkFnType [i1] [i1]       ) $ PrimOp "bitnot" 1
  ,(,) "primitive_sext_i64_i32" $ (,) (mkFnType [i32] [i64]     ) $ PrimOp "sext_i64" 32
  ,(,) "+Int64"        $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "+" 64
  ,(,) "-Int64"        $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "-" 64
  ,(,) "*Int64"        $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "*" 64
  ,(,) "bitand-Int64"  $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "bitand"  64
  ,(,) "bitor-Int64"   $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "bitor"   64
  ,(,) "bitxor-Int64"  $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "bitxor"  64
  ,(,) "bitshl-Int64"  $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "bitshl"  64
  ,(,) "bitlshr-Int64" $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "bitlshr" 64
  ,(,) "bitashr-Int64" $ (,) (mkFnType [i64, i64] [i64]) $ PrimOp "bitashr" 64
  ,(,) "<Int64"        $ (,) (mkFnType [i64, i64] [i1] ) $ PrimOp "<"  64
  ,(,) ">Int64"        $ (,) (mkFnType [i64, i64] [i1] ) $ PrimOp ">"  64
  ,(,) "<=Int64"       $ (,) (mkFnType [i64, i64] [i1] ) $ PrimOp "<=" 64
  ,(,) ">=Int64"       $ (,) (mkFnType [i64, i64] [i1] ) $ PrimOp ">=" 64
  ,(,) "==Int64"       $ (,) (mkFnType [i64, i64] [i1] ) $ PrimOp "==" 64
  ,(,) "!=Int64"       $ (,) (mkFnType [i64, i64] [i1] ) $ PrimOp "!=" 64
  ,(,) "negate-Int64"  $ (,) (mkFnType [i64] [i64]     ) $ PrimOp "negate"  64
  ,(,) "bitnot-Int64"  $ (,) (mkFnType [i64] [i64]     ) $ PrimOp "bitnot"  64
  ,(,) "+Int32"        $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "+" 32
  ,(,) "-Int32"        $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "-" 32
  ,(,) "*Int32"        $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "*" 32
  ,(,) "bitand-Int32"  $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "bitand"  32
  ,(,) "bitor-Int32"   $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "bitor"   32
  ,(,) "bitxor-Int32"  $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "bitxor"  32
  ,(,) "bitshl-Int32"  $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "bitshl"  32
  ,(,) "bitlshr-Int32" $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "bitlshr" 32
  ,(,) "bitashr-Int32" $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "bitashr" 32
  ,(,) "srem-Int32"    $ (,) (mkFnType [i32, i32] [i32]) $ PrimOp "srem" 32 -- TODO 64
  ,(,) "<Int32"        $ (,) (mkFnType [i32, i32] [i1] ) $ PrimOp "<"  32
  ,(,) ">Int32"        $ (,) (mkFnType [i32, i32] [i1] ) $ PrimOp ">"  32
  ,(,) "<=Int32"       $ (,) (mkFnType [i32, i32] [i1] ) $ PrimOp "<=" 32
  ,(,) ">=Int32"       $ (,) (mkFnType [i32, i32] [i1] ) $ PrimOp ">=" 32
  ,(,) "==Int32"       $ (,) (mkFnType [i32, i32] [i1] ) $ PrimOp "==" 32
  ,(,) "!=Int32"       $ (,) (mkFnType [i32, i32] [i1] ) $ PrimOp "!=" 32
  ,(,) "negate-Int32"  $ (,) (mkFnType [i32] [i32]     ) $ PrimOp "negate"  32
  ,(,) "bitnot-Int32"  $ (,) (mkFnType [i32] [i32]     ) $ PrimOp "bitnot"  32
  ]
