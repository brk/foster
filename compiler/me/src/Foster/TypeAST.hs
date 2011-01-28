-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST where

import Foster.Base
import List(foldr1, intersperse, length)
import Data.IORef(IORef)

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere

data TypeAST =
           MissingTypeAST { missingTypeProgAnnotation :: String }
         | NamedTypeAST     String
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        TypeAST TypeAST (Maybe [String])
         | CoroType         TypeAST TypeAST
         | ForAll           [TyVar] Rho
         | T_TyVar          TyVar
         | MetaTyVar        MetaTyVar

data TyVar = BoundTyVar String -- bound by a ForAll, that is
           | SkolemTyVar String Uniq deriving (Eq)

data MetaTyVar = Meta Uniq TyRef

type TyRef = IORef (Maybe Tau)
    -- Nothing: type variable not substituted
    -- Just ty: ty var has been substituted by ty

instance Show TyVar where
    show (BoundTyVar x) = "'" ++ x
    show (SkolemTyVar x u) = "~(" ++ x ++ "/" ++ show u ++ ")"

instance Show TypeAST where
    show x = case x of
        (MissingTypeAST s)   -> "(MissingTypeAST " ++ s ++ ")"
        (NamedTypeAST s)     -> s
        (TupleTypeAST types) -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        (FnTypeAST s t cs)   -> "(" ++ show s ++ " -> " ++ show t ++ ")"
        (CoroType s t)   -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        (ForAll tvs rho) -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        (T_TyVar tv)     -> show tv
        (MetaTyVar mtv)  -> "(~!)"

instance Eq TypeAST where
    t1 == t2 = typesEqual t1 t2

instance Eq MetaTyVar where
    (Meta u1 _) == (Meta u2 _) = u1 == u2

typesEqual :: TypeAST -> TypeAST -> Bool

typesEqual (MissingTypeAST x) (MissingTypeAST y) = x == y
typesEqual (NamedTypeAST x) (NamedTypeAST y) = x == y
typesEqual (TupleTypeAST as) (TupleTypeAST bs) =
    List.length as == List.length bs && Prelude.and [typesEqual a b | (a, b) <- Prelude.zip as bs]
typesEqual (FnTypeAST a1 b1 c1) (FnTypeAST a2 b2 c2) =
    typesEqual a1 a2 && typesEqual b1 b2 -- ignore c1 and c2 for now...
typesEqual (CoroType a1 b1) (CoroType a2 b2) = typesEqual a1 a2 && typesEqual b1 b2
typesEqual (ForAll vars1 ty1) (ForAll vars2 ty2) =
    vars1 == vars2 && typesEqual ty1 ty2
typesEqual (T_TyVar tv1) (T_TyVar tv2) = tv1 == tv2
typesEqual (MetaTyVar mtv1) (MetaTyVar mtv2) = mtv1 == mtv2
typesEqual _ _ = False


fosBoolType = NamedTypeAST "i1"

joinWith :: String -> [String] -> String
joinWith s [] = ""
joinWith s ss = foldr1 (++) (intersperse s ss)


minimalTuple []    = TupleTypeAST []
minimalTuple [arg] = arg
minimalTuple args  = TupleTypeAST args

mkFnType   args rets = FnTypeAST (TupleTypeAST args) (minimalTuple rets) Nothing
mkCoroType args rets =  CoroType (minimalTuple args) (minimalTuple rets)
i32 = (NamedTypeAST "i32")
i64 = (NamedTypeAST "i64")
i1  = (NamedTypeAST "i1")

coroInvokeType args rets = mkFnType ((mkCoroType args rets) : args) rets
coroYieldType  args rets = mkFnType rets args
coroCreateType args rets = mkFnType [mkFnType args rets] [mkCoroType args rets]

rootContextPairs =
    [(,) "llvm_readcyclecounter" $ mkFnType [] [i64]
    ,(,) "expect_i32"  $ mkFnType [i32] [i32]
    ,(,)  "print_i32"  $ mkFnType [i32] [i32]
    ,(,) "expect_i32b" $ mkFnType [i32] [i32]
    ,(,)  "print_i32b" $ mkFnType [i32] [i32]
    ,(,) "expect_i64"  $ mkFnType [i64] [i32]
    ,(,)  "print_i64"  $ mkFnType [i64] [i32]
    ,(,) "expect_i64b" $ mkFnType [i64] [i32]
    ,(,)  "print_i64b" $ mkFnType [i64] [i32]
    ,(,)   "read_i32"  $ mkFnType  []   [i32]
    ,(,) "expect_i1"   $ mkFnType [i1] [i32]
    ,(,)  "print_i1"   $ mkFnType [i1] [i32]

    ,(,) "coro_create_i32_i32" $ coroCreateType [i32] [i32]
    ,(,) "coro_invoke_i32_i32" $ coroInvokeType [i32] [i32]
    ,(,) "coro_yield_i32_i32"  $ coroYieldType  [i32] [i32]

    ,(,) "coro_create_i32x2_i32" $ coroCreateType [i32, i32] [i32]
    ,(,) "coro_invoke_i32x2_i32" $ coroInvokeType [i32, i32] [i32]
    ,(,) "coro_yield_i32x2_i32"  $ coroYieldType  [i32, i32] [i32]

    ,(,) "coro_create_i32_i32x2" $ coroCreateType [i32] [i32,i32]
    ,(,) "coro_invoke_i32_i32x2" $ coroInvokeType [i32] [i32,i32]
    ,(,) "coro_yield_i32_i32x2"  $ coroYieldType  [i32] [i32,i32]


    -- forall a b, (a -> b) -> Coro a b
    ,(,) "coro_create" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAll [a, b]
                           (FnTypeAST (FnTypeAST (T_TyVar a) (T_TyVar b) Nothing)
                                      (CoroType  (T_TyVar a) (T_TyVar b))
                                       Nothing))
    -- forall a b, (a, Coro a b) -> b
    ,(,) "coro_invoke" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAll [a, b]
                            (FnTypeAST (TupleTypeAST [(CoroType (T_TyVar a) (T_TyVar b)), (T_TyVar a)])
                                       (T_TyVar b) Nothing))
    -- forall a b, (b -> a)
    ,(,) "coro_yield"  $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAll [a, b] (FnTypeAST (T_TyVar b) (T_TyVar a) Nothing))

    ,(,) "primitive_sext_i64_i32" $ mkFnType [i32] [i64]
    ,(,) "primitive_negate_i32"   $ mkFnType [i32] [i32]
    ,(,) "primitive_bitnot_i1"    $ mkFnType [i1] [i1]
    ,(,) "primitive_bitshl_i32"   $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_bitashr_i32"  $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_bitlshr_i32"  $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_bitor_i32"    $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_bitand_i32"   $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_bitxor_i32"   $ mkFnType [i32, i32] [i32]
    ,(,) "force_gc_for_debugging_purposes" $ mkFnType [] []

    ,(,) "primitive_<_i64"  $ mkFnType [i64, i64] [i1]
    ,(,) "primitive_-_i64"  $ mkFnType [i64, i64] [i64]
    ,(,) "primitive_-_i32"  $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_*_i32"  $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_+_i32"  $ mkFnType [i32, i32] [i32]
    ,(,) "primitive_<_i32"  $ mkFnType [i32, i32] [i1]
    ,(,) "primitive_<=_i32" $ mkFnType [i32, i32] [i1]
    ,(,) "primitive_==_i32" $ mkFnType [i32, i32] [i1]
    ]
