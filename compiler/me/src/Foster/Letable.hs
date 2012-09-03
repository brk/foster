-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Letable where

import Foster.Base(LiteralInt, LiteralFloat, CtorInfo, ArrayIndex(..),
                   AllocMemRegion, AllocInfo(..), Occurrence, AllocationSource,
                   FosterPrim(..),
                   TypedId(..), Ident(..),
                   -- AExpr(freeIdents), tidIdent,
                   TExpr(freeTypedIds), TypedWith(..))
import Foster.MonoType

import qualified Data.Text as T

-- The reason we have both ILAllocate and ILAlloc is that
-- LLCodegen performs auto-loads from stack slots, which
-- means that a derived ILAlloc can't return a stack slot value!

data Letable ty =
          ILBool        Bool
        | ILText        T.Text
        | ILInt         ty LiteralInt
        | ILFloat       ty LiteralFloat
        | ILTuple       [TypedId ty] AllocationSource
        | ILKillProcess ty T.Text
        -- Struct member lookup
        | ILOccurrence  ty (TypedId ty) (Occurrence ty)
        -- Varieties of applications
        | ILCallPrim    ty (FosterPrim ty) [TypedId ty]
        | ILCall        ty (TypedId    ty) [TypedId ty]
        | ILAppCtor     ty (CtorInfo   ty) [TypedId ty]
        -- Stack/heap slot allocation
        | ILAllocate    (AllocInfo ty)
        -- Mutable ref cells
        | ILAlloc       (TypedId ty) AllocMemRegion
        | ILDeref       ty           (TypedId ty)
        | ILStore       (TypedId ty) (TypedId ty)
        -- Array operations
        | ILAllocArray  ty (TypedId ty)
        | ILArrayRead   ty (ArrayIndex (TypedId ty))
        | ILArrayPoke      (ArrayIndex (TypedId ty)) (TypedId ty)
        -- Others
        | ILBitcast     ty (TypedId ty) -- inserted during monomorphization
        deriving (Functor, Show)

instance TExpr (Letable ty) ty where
  freeTypedIds letable = case letable of
      ILText         {} -> []
      ILBool         {} -> []
      ILInt          {} -> []
      ILFloat        {} -> []
      ILTuple      vs _ -> vs
      ILKillProcess  {} -> []
      ILOccurrence _ v _-> [v]
      ILCallPrim _ _ vs -> vs
      ILCall     _ v vs -> (v:vs)
      ILAppCtor  _ _ vs -> vs
      ILAlloc      v _  -> [v]
      ILDeref    _ v    -> [v]
      ILStore      v v2 -> [v,v2]
      ILBitcast  _ v    -> [v]
      ILAllocArray _ v  -> [v]
      ILArrayRead _ ai  -> freeTypedIds ai
      ILArrayPoke   ai v-> (v):(freeTypedIds ai)
      ILAllocate _      -> []

instance TypedWith (Letable MonoType) MonoType where
  typeOf letable = case letable of
      ILText         {} -> TyConApp "Text" []
      ILBool         {} -> boolMonoType
      ILInt         t _ -> t
      ILFloat       t _ -> t
      ILTuple      vs _ -> TupleType (map tidType vs)
      ILKillProcess t _ -> t
      ILOccurrence t v _-> t
      ILCallPrim t _ _  -> t
      ILCall     t _ _  -> t
      ILAppCtor  t _ _  -> t
      ILAlloc      v _  -> PtrType (tidType v)
      ILDeref    t v    -> t
      ILStore      v v2 -> TupleType []
      ILBitcast  t _    -> t
      ILAllocArray t _  -> t
      ILArrayRead t _   -> t
      ILArrayPoke   ai v-> TupleType []
      ILAllocate info   -> PtrType (allocType info)

isPurePrim _ = False -- TODO: recognize pure primitives
isPureFunc _ = False -- TODO: use effect information to refine this predicate.

substVarsInLetable :: (TypedId t -> TypedId t) -> Letable t -> Letable t
substVarsInLetable s letable = case letable of
  ILText        {}                         -> letable
  ILBool        {}                         -> letable
  ILInt         {}                         -> letable
  ILFloat       {}                         -> letable
  ILKillProcess {}                         -> letable
  ILAllocate    {}                         -> letable
  ILTuple       vs asrc                    -> ILTuple       (map s vs) asrc
  ILOccurrence  t v occ                    -> ILOccurrence  t (s v) occ
  ILCallPrim    t p vs                     -> ILCallPrim    t p     (map s vs)
  ILCall        t v vs                     -> ILCall        t (s v) (map s vs)
  ILAppCtor     t c vs                     -> ILAppCtor     t c     (map s vs)
  ILAlloc       v rgn                      -> ILAlloc       (s v) rgn
  ILDeref       t v                        -> ILDeref       t (s v)
  ILStore       v1 v2                      -> ILStore       (s v1) (s v2)
  ILBitcast     t v                        -> ILBitcast     t (s v)
  ILAllocArray  t v                        -> ILAllocArray  t (s v)
  ILArrayRead   t (ArrayIndex v1 v2 rng a) -> ILArrayRead   t (ArrayIndex (s v1) (s v2) rng a)
  ILArrayPoke  (ArrayIndex v1 v2 rng a) v3 -> ILArrayPoke  (ArrayIndex (s v1) (s v2) rng a) (s v3)

isPure :: Letable MonoType -> Bool
isPure letable = case letable of
      ILText         {} -> True
      ILBool         {} -> True
      ILInt          {} -> True
      ILFloat        {} -> True
      ILTuple        {} -> True
      ILKillProcess  {} -> False
      ILOccurrence   {} -> True
      ILCallPrim  _ p _ -> isPurePrim p
      ILCall      _ v _ -> isPureFunc v
      ILAppCtor      {} -> True
      ILAllocate     {} -> True
      ILAlloc        {} -> True
      ILDeref        {} -> True
      ILStore     _v1 _ -> False -- true iff v1 unaliased && dead?
      ILBitcast      {} -> True
      ILAllocArray   {} -> True
      ILArrayRead    {} -> True
      ILArrayPoke    {} -> False -- as with store

canGC :: Letable MonoType -> Bool
canGC letable = case letable of
         ILAppCtor     {} -> True
         ILAllocate    {} -> True
         ILAlloc       {} -> True
         ILAllocArray  {} -> True
         ILCall     _ v _ -> canGCF v
         ILCallPrim _ p _ -> canGCPrim p
         ILTuple    _ _   -> True -- rather than stack allocating tuples, easier to just remove 'em probably.
         ILText        {} -> True -- unless we statically allocate such things
         ILInt         {} -> False -- unless it's a bignum...
         ILBool        {} -> False
         ILFloat       {} -> False
         ILKillProcess {} -> False
         ILOccurrence  {} -> False
         ILDeref       {} -> False
         ILStore       {} -> False
         ILBitcast     {} -> False
         ILArrayRead   {} -> False
         ILArrayPoke   {} -> False

canGCPrim (PrimIntTrunc {}) = False
canGCPrim (PrimOp       {}) = False
canGCPrim (NamedPrim (TypedId _ (GlobalSymbol name))) =
                    not $ name `elem` (map T.pack
                        ["expect_i1", "print_i1"
                        ,"expect_i64" , "print_i64" , "expect_i32", "print_i32"
                        ,"expect_i32b", "print_i32b"])
canGCPrim _ = True

canGCF :: TypedId MonoType -> Bool -- "can gc from calling this function-typed variable"
canGCF fnvarid = True -- TODO: use effect information to recognize OK calls
                      --      (or explicit mayGC annotations on call sites?)

