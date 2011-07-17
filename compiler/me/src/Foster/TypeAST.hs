-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST where

import Foster.Base
import List(length)
import Data.IORef(IORef)
import Data.Map as Map(fromList, toList)

data EPattern =
          EP_Wildcard      ESourceRange
        | EP_Variable      ESourceRange E_VarAST
        | EP_Bool          ESourceRange Bool
        | EP_Int           ESourceRange String
        | EP_Tuple         ESourceRange [EPattern]
        deriving (Show)

data E_VarAST = VarAST { evarMaybeType :: Maybe TypeAST
                       , evarName      :: String } deriving (Show)

type AnnVar = TypedId TypeAST

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere

data TypeAST =
           NamedTypeAST     String
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        { fnTypeDomain :: TypeAST
                            , fnTypeRange  :: TypeAST
                            , fnTypeCallConv :: CallConv
                            , fnTypeProcOrFunc :: ProcOrFunc }
         | CoroTypeAST      TypeAST TypeAST
         | ForAllAST        [TyVar] Rho
         | TyVarAST         TyVar
         | MetaTyVar        MetaTyVar
         | RefTypeAST       TypeAST
         | ArrayTypeAST     TypeAST

data MetaTyVar = Meta Uniq TyRef String

type TyRef = IORef (Maybe Tau)
    -- Nothing: type variable not substituted
    -- Just ty: ty var has been substituted by ty

instance Show TyVar where
    show (BoundTyVar x) = "'" ++ x
    show (SkolemTyVar x u) = "~(" ++ x ++ "/" ++ show u ++ ")"

instance Show TypeAST where
    show x = case x of
        (NamedTypeAST s)     -> s
        (TupleTypeAST types) -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        (FnTypeAST s t cc cs)-> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        (CoroTypeAST s t)   -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        (ForAllAST tvs rho) -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        (TyVarAST tv)     -> show tv
        (MetaTyVar (Meta u tyref desc))  -> "(~!" ++ show u ++ ":" ++ desc ++ ")"
        (RefTypeAST    ty)  -> "(Ref " ++ show ty ++ ")"
        (ArrayTypeAST  ty)  -> "(Array " ++ show ty ++ ")"

instance Eq MetaTyVar where
    (Meta u1 _ _) == (Meta u2 _ _) = u1 == u2


typesEqual :: TypeAST -> TypeAST -> Bool

typesEqual (NamedTypeAST x) (NamedTypeAST y) = x == y
typesEqual (TupleTypeAST as) (TupleTypeAST bs) =
    List.length as == List.length bs && Prelude.and [typesEqual a b | (a, b) <- Prelude.zip as bs]
typesEqual (FnTypeAST a1 b1 c1 d1) (FnTypeAST a2 b2 c2 d2) =
    typesEqual a1 a2 && typesEqual b1 b2
                      && c1 == c2
                -- ignore d1 and d2 for now...
typesEqual (CoroTypeAST a1 b1) (CoroTypeAST a2 b2) = typesEqual a1 a2 && typesEqual b1 b2
typesEqual (ForAllAST vars1 ty1) (ForAllAST vars2 ty2) =
    vars1 == vars2 && typesEqual ty1 ty2
typesEqual (TyVarAST tv1) (TyVarAST tv2) = tv1 == tv2
typesEqual (MetaTyVar mtv1) (MetaTyVar mtv2) = mtv1 == mtv2
typesEqual _ _ = False


fosBoolType = NamedTypeAST "i1"

minimalTupleAST []    = TupleTypeAST []
minimalTupleAST [arg] = arg
minimalTupleAST args  = TupleTypeAST args

mkProcType args rets = FnTypeAST (TupleTypeAST args) (minimalTupleAST rets) CCC    FT_Proc
mkFnType   args rets = FnTypeAST (TupleTypeAST args) (minimalTupleAST rets) FastCC FT_Func
mkCoroType args rets = CoroTypeAST (minimalTupleAST args) (minimalTupleAST rets)
i32 = (NamedTypeAST "i32")
i64 = (NamedTypeAST "i64")
i1  = (NamedTypeAST "i1")

coroInvokeType args rets = mkFnType ((mkCoroType args rets) : args) rets
coroYieldType  args rets = mkFnType rets args
coroCreateType args rets = mkFnType [mkFnType args rets] [mkCoroType args rets]

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
                         ForAllAST [a]
                           (mkProcType [i32] [ArrayTypeAST (TyVarAST a)])

    -- forall a b, (a -> b) -> Coro a b
    ,(,) "coro_create" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAllAST [a, b]
                           (mkFnType [mkFnType   [TyVarAST a] [TyVarAST b]]
                                     [mkCoroType [TyVarAST a] [TyVarAST b]]))

    -- forall a b, (Coro a b, a) -> b
    ,(,) "coro_invoke" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAllAST [a, b]
                            (mkFnType [(mkCoroType [TyVarAST a] [TyVarAST b]), (TyVarAST a)]
                                      [TyVarAST b]))

    -- forall a b, (b -> a)
    -- (only not quite: a and b must be unifiable
    --  with the arg & return types of the containing function)
    ,(,) "coro_yield"  $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAllAST [a, b] (mkFnType [TyVarAST b] [TyVarAST a]))

    ,(,) "force_gc_for_debugging_purposes" $ mkFnType [] []
    ,(,) "llvm_readcyclecounter" $ mkFnType [] [i64]

    ] ++ (map (\(name, (ty, op)) -> (name, ty)) $ Map.toList gFosterPrimOpsTable)

gFosterPrimOpsTable = Map.fromList $
  [(,) "primitive_negate_i1"    $ (,) (mkFnType [i1] [i1]       ) $ ILPrimOp "negate" 1
  ,(,) "primitive_bitnot_i1"    $ (,) (mkFnType [i1] [i1]       ) $ ILPrimOp "bitnot" 1
  ,(,) "primitive_sext_i64_i32" $ (,) (mkFnType [i32] [i64]     ) $ ILPrimOp "sext_i64" 32
  ,(,) "primitive_+_i64"        $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "+" 64
  ,(,) "primitive_-_i64"        $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "-" 64
  ,(,) "primitive_*_i64"        $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "*" 64
  ,(,) "primitive_bitand_i64"   $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "bitand"  64
  ,(,) "primitive_bitor_i64"    $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "bitor"   64
  ,(,) "primitive_bitxor_i64"   $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "bitxor"  64
  ,(,) "primitive_bitshl_i64"   $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "bitshl"  64
  ,(,) "primitive_bitlshr_i64"  $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "bitlshr" 64
  ,(,) "primitive_bitashr_i64"  $ (,) (mkFnType [i64, i64] [i64]) $ ILPrimOp "bitashr" 64
  ,(,) "primitive_<_i64"        $ (,) (mkFnType [i64, i64] [i1] ) $ ILPrimOp "<"  64
  ,(,) "primitive_>_i64"        $ (,) (mkFnType [i64, i64] [i1] ) $ ILPrimOp ">"  64
  ,(,) "primitive_<=_i64"       $ (,) (mkFnType [i64, i64] [i1] ) $ ILPrimOp "<=" 64
  ,(,) "primitive_>=_i64"       $ (,) (mkFnType [i64, i64] [i1] ) $ ILPrimOp ">=" 64
  ,(,) "primitive_==_i64"       $ (,) (mkFnType [i64, i64] [i1] ) $ ILPrimOp "==" 64
  ,(,) "primitive_!=_i64"       $ (,) (mkFnType [i64, i64] [i1] ) $ ILPrimOp "!=" 64
  ,(,) "primitive_negate_i64"   $ (,) (mkFnType [i64] [i64]     ) $ ILPrimOp "negate"  64
  ,(,) "primitive_bitnot_i64"   $ (,) (mkFnType [i64] [i64]     ) $ ILPrimOp "bitnot"  64
  ,(,) "primitive_+_i32"        $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "+" 32
  ,(,) "primitive_-_i32"        $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "-" 32
  ,(,) "primitive_*_i32"        $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "*" 32
  ,(,) "primitive_bitand_i32"   $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "bitand"  32
  ,(,) "primitive_bitor_i32"    $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "bitor"   32
  ,(,) "primitive_bitxor_i32"   $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "bitxor"  32
  ,(,) "primitive_bitshl_i32"   $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "bitshl"  32
  ,(,) "primitive_bitlshr_i32"  $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "bitlshr" 32
  ,(,) "primitive_bitashr_i32"  $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "bitashr" 32
  ,(,) "primitive_srem_i32"     $ (,) (mkFnType [i32, i32] [i32]) $ ILPrimOp "srem" 32 -- TODO 64
  ,(,) "primitive_<_i32"        $ (,) (mkFnType [i32, i32] [i1] ) $ ILPrimOp "<"  32
  ,(,) "primitive_>_i32"        $ (,) (mkFnType [i32, i32] [i1] ) $ ILPrimOp ">"  32
  ,(,) "primitive_<=_i32"       $ (,) (mkFnType [i32, i32] [i1] ) $ ILPrimOp "<=" 32
  ,(,) "primitive_>=_i32"       $ (,) (mkFnType [i32, i32] [i1] ) $ ILPrimOp ">=" 32
  ,(,) "primitive_==_i32"       $ (,) (mkFnType [i32, i32] [i1] ) $ ILPrimOp "==" 32
  ,(,) "primitive_!=_i32"       $ (,) (mkFnType [i32, i32] [i1] ) $ ILPrimOp "!=" 32
  ,(,) "primitive_negate_i32"   $ (,) (mkFnType [i32] [i32]     ) $ ILPrimOp "negate"  32
  ,(,) "primitive_bitnot_i32"   $ (,) (mkFnType [i32] [i32]     ) $ ILPrimOp "bitnot"  32
  ]
