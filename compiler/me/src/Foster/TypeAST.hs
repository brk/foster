-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST where

import Foster.Base
import List(length)
import Data.IORef(IORef)

data CallConv = CCC | FastCC deriving (Eq, Show)
briefCC CCC = "ccc"
briefCC FastCC = ""

data AnnVar = AnnVar { avarType :: TypeAST, avarIdent :: Ident }

instance Show AnnVar where
    show (AnnVar ty id) = show id ++ " :: " ++ show ty

data EPattern =
          EP_Wildcard      ESourceRange
        | EP_Variable      ESourceRange E_VarAST
        | EP_Bool          ESourceRange Bool
        | EP_Int           ESourceRange String
        | EP_Tuple         ESourceRange [EPattern]
        deriving (Show)

-- EPattern variable bindings can have type annotations
-- for typechecking.
data Pattern =
          P_Wildcard      ESourceRange
        | P_Variable      ESourceRange Ident
        | P_Bool          ESourceRange Bool
        | P_Int           ESourceRange LiteralInt
        | P_Tuple         ESourceRange [Pattern]
        deriving (Show)

data E_VarAST = VarAST { evarMaybeType :: Maybe TypeAST
                       , evarName      :: String } deriving (Show)

type Sigma = TypeAST
type Rho   = TypeAST -- No top-level ForAll
type Tau   = TypeAST -- No ForAlls anywhere

data TypeAST =
           NamedTypeAST     String
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        { fnTypeDomain :: TypeAST
                            , fnTypeRange  :: TypeAST
                            , fnTypeCallConv :: CallConv
                            , fnTypeCloses :: Maybe [AnnVar] }
         | CoroType         TypeAST TypeAST
         | ForAll           [TyVar] Rho
         | T_TyVar          TyVar
         | MetaTyVar        MetaTyVar
         | RefType          TypeAST
         | ArrayType        TypeAST
         | PtrTypeAST       TypeAST -- TODO split this into ILType

data TyVar = BoundTyVar String -- bound by a ForAll, that is
           | SkolemTyVar String Uniq deriving (Eq)

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
        (CoroType s t)   -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        (ForAll tvs rho) -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        (T_TyVar tv)     -> show tv
        (MetaTyVar (Meta u tyref desc))  -> "(~!" ++ show u ++ ":" ++ desc ++ ")"
        (RefType    ty)  -> "(Ref " ++ show ty ++ ")"
        (ArrayType  ty)  -> "(Array " ++ show ty ++ ")"
        (PtrTypeAST ty)  -> "(Ptr " ++ show ty ++ ")"

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
typesEqual (CoroType a1 b1) (CoroType a2 b2) = typesEqual a1 a2 && typesEqual b1 b2
typesEqual (ForAll vars1 ty1) (ForAll vars2 ty2) =
    vars1 == vars2 && typesEqual ty1 ty2
typesEqual (T_TyVar tv1) (T_TyVar tv2) = tv1 == tv2
typesEqual (MetaTyVar mtv1) (MetaTyVar mtv2) = mtv1 == mtv2
typesEqual (PtrTypeAST ty1) (PtrTypeAST ty2) = typesEqual ty1 ty2
typesEqual _ _ = False


fosBoolType = NamedTypeAST "i1"

minimalTuple []    = TupleTypeAST []
minimalTuple [arg] = arg
minimalTuple args  = TupleTypeAST args

mkProcType args rets = FnTypeAST (TupleTypeAST args) (minimalTuple rets) CCC    Nothing
mkFnType   args rets = FnTypeAST (TupleTypeAST args) (minimalTuple rets) FastCC Nothing
mkCoroType args rets =  CoroType (minimalTuple args) (minimalTuple rets)
i32 = (NamedTypeAST "i32")
i64 = (NamedTypeAST "i64")
i1  = (NamedTypeAST "i1")

coroInvokeType args rets = mkFnType ((mkCoroType args rets) : args) rets
coroYieldType  args rets = mkFnType rets args
coroCreateType args rets = mkFnType [mkFnType args rets] [mkCoroType args rets]

rootContextDecls =
    [(,) "llvm_readcyclecounter" $ mkFnType [] [i64]
    ,(,) "expect_i32"  $ mkProcType [i32] []
    ,(,)  "print_i32"  $ mkProcType [i32] []
    ,(,) "expect_i64"  $ mkProcType [i64] []
    ,(,)  "print_i64"  $ mkProcType [i64] []

    ,(,) "expect_i1"   $ mkProcType [i1] []
    ,(,)  "print_i1"   $ mkProcType [i1] []

    ,(,) "opaquely_i32" $ mkProcType [i32] [i32]
    ,(,) "allocDArray32" $ mkProcType [i32] [ArrayType i32]

    -- forall a b, (a -> b) -> Coro a b
    ,(,) "coro_create" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAll [a, b]
                           (mkFnType [mkFnType   [T_TyVar a] [T_TyVar b]]
                                     [mkCoroType [T_TyVar a] [T_TyVar b]]))

    -- forall a b, (Coro a b, a) -> b
    ,(,) "coro_invoke" $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAll [a, b]
                            (mkFnType [(mkCoroType [T_TyVar a] [T_TyVar b]), (T_TyVar a)]
                                      [T_TyVar b]))

    -- forall a b, (b -> a)
    -- (only not quite: a and b must be unifiable
    --  with the arg & return types of the containing function)
    ,(,) "coro_yield"  $ let a = BoundTyVar "a" in
                         let b = BoundTyVar "b" in
                         (ForAll [a, b] (mkFnType [T_TyVar b] [T_TyVar a]))

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
