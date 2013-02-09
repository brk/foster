-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Letable where

import Foster.Base(Literal(..), CtorId, ArrayIndex(..),
                   AllocMemRegion, AllocInfo(..), Occurrence, AllocationSource,
                   FosterPrim(..), MayGC(..), memRegionMayGC,
                   TypedId(..), Ident(..),
                   TExpr(freeTypedIds), TypedWith(..))
import Foster.MonoType
import Foster.TypeLL

import qualified Data.Text as T

import qualified Data.Map as Map(Map, findWithDefault)

-- The reason we have both ILAllocate and ILAlloc is that
-- LLCodegen performs auto-loads from stack slots, which
-- means that a derived ILAlloc can't return a stack slot value!

data Letable ty =
          ILLiteral     ty Literal
        | ILTuple       [TypedId ty] AllocationSource
        | ILKillProcess ty T.Text
        -- Struct member lookup
        | ILOccurrence  ty (TypedId ty) (Occurrence ty)
        -- Varieties of applications
        | ILCallPrim    ty (FosterPrim ty) [TypedId ty]
        | ILCall        ty (TypedId    ty) [TypedId ty]
        | ILAppCtor     ty CtorId          [TypedId ty]
        -- Stack/heap slot allocation
        | ILAllocate    (AllocInfo ty)
        -- Mutable ref cells
        | ILAlloc       (TypedId ty) AllocMemRegion
        | ILDeref       ty           (TypedId ty)
        | ILStore       (TypedId ty) (TypedId ty)
        | ILObjectCopy  (TypedId ty) (TypedId ty)
        -- Array operations
        | ILAllocArray  ty (TypedId ty)
        | ILArrayRead   ty (ArrayIndex (TypedId ty))
        | ILArrayPoke      (ArrayIndex (TypedId ty)) (TypedId ty)
        -- Others
        | ILBitcast     ty (TypedId ty) -- inserted during monomorphization
        deriving (Functor, Show)

instance TExpr (Letable ty) ty where
  freeTypedIds letable = case letable of
      ILLiteral      {} -> []
      ILTuple      vs _ -> vs
      ILKillProcess  {} -> []
      ILOccurrence _ v _-> [v]
      ILCallPrim _ _ vs -> vs
      ILCall     _ v vs -> (v:vs)
      ILAppCtor  _ _ vs -> vs
      ILAlloc      v _  -> [v]
      ILDeref    _ v    -> [v]
      ILStore      v v2 -> [v,v2]
      ILObjectCopy v v2 -> [v,v2]
      ILBitcast  _ v    -> [v]
      ILAllocArray _ v  -> [v]
      ILArrayRead _ ai  -> freeTypedIds ai
      ILArrayPoke   ai v-> (v):(freeTypedIds ai)
      ILAllocate _      -> []

instance TypedWith (Letable MonoType) MonoType where
  typeOf letable = case letable of
      ILLiteral     t _ -> t
      ILTuple      vs _ -> TupleType (map tidType vs)
      ILKillProcess t _ -> t
      ILOccurrence t _ _-> t
      ILCallPrim t _ _  -> t
      ILCall     t _ _  -> t
      ILAppCtor  t _ _  -> t
      ILAlloc      v _  -> PtrType (tidType v)
      ILDeref      t _  -> t
      ILStore       {}  -> TupleType []
      ILObjectCopy  {}  -> TupleType []
      ILBitcast    t _  -> t
      ILAllocArray t _  -> t
      ILArrayRead  t _  -> t
      ILArrayPoke   {}  -> TupleType []
      ILAllocate info   -> PtrType (allocType info)

instance TypedWith (Letable TypeLL) TypeLL where
  typeOf letable = case letable of
      ILLiteral     t _ -> t
      ILTuple      vs _ -> LLPtrType (LLStructType (map tidType vs))
      ILKillProcess t _ -> t
      ILOccurrence t _ _-> t
      ILCallPrim t _ _  -> t
      ILCall     t _ _  -> t
      ILAppCtor  t _ _  -> t
      ILAlloc      v _  -> LLPtrType (tidType v)
      ILDeref    t _    -> t
      ILStore      {}   -> LLPtrType (LLStructType [])
      ILObjectCopy {}   -> LLPtrType (LLStructType [])
      ILBitcast  t _    -> t
      ILAllocArray t _  -> t
      ILArrayRead t _   -> t
      ILArrayPoke   _ _ -> LLPtrType (LLStructType [])
      ILAllocate info   -> LLPtrType (allocType info)

isPurePrim _ = False -- TODO: recognize pure primitives
isPureFunc _ = False -- TODO: use effect information to refine this predicate.

substVarsInLetable :: (TypedId t -> TypedId t) -> Letable t -> Letable t
substVarsInLetable s letable = case letable of
  ILLiteral     {}                         -> letable
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
  ILObjectCopy  v1 v2                      -> ILObjectCopy  (s v1) (s v2)
  ILBitcast     t v                        -> ILBitcast     t (s v)
  ILAllocArray  t v                        -> ILAllocArray  t (s v)
  ILArrayRead   t (ArrayIndex v1 v2 rng a) -> ILArrayRead   t (ArrayIndex (s v1) (s v2) rng a)
  ILArrayPoke  (ArrayIndex v1 v2 rng a) v3 -> ILArrayPoke  (ArrayIndex (s v1) (s v2) rng a) (s v3)

-- | Some letables are trivial (literals, bitcasts), others not so much.
--   It remains to be seen whether deref/store should be counted or not.
letableSize :: Letable t -> Int
letableSize letable = case letable of
      ILLiteral _ (LitText {}) -> 2 -- two calls to initialize!
      ILLiteral      {} -> 0 -- TODO: distinguish fixnums from bignums?
      ILTuple        {} -> 1
      ILKillProcess  {} -> 0
      ILOccurrence   {} -> 1
      ILCallPrim     {} -> 1
      ILCall         {} -> 1
      ILAppCtor      {} -> 1 -- 2?
      ILAllocate     {} -> 1
      ILAlloc        {} -> 1
      ILDeref        {} -> 1 -- 0?
      ILStore        {} -> 0 -- 1?
      ILObjectCopy   {} -> 0 -- 1?
      ILBitcast      {} -> 0
      ILAllocArray   {} -> 1
      ILArrayRead    {} -> 1
      ILArrayPoke    {} -> 1

isPure :: Letable MonoType -> Bool
isPure letable = case letable of
      ILLiteral      {} -> True
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
      ILObjectCopy _from _to -> False -- true iff `to` unaliased && dead?
      ILBitcast      {} -> True
      ILAllocArray   {} -> True
      ILArrayRead    {} -> True
      ILArrayPoke    {} -> False -- as with store

canGC :: Map.Map Ident MayGC -> Letable ty -> MayGC
canGC mayGCmap letable =
  case letable of
         ILAppCtor     {} -> MayGC
         ILAlloc       {} -> MayGC
         ILAllocArray  {} -> MayGC
         ILAllocate info  -> memRegionMayGC (allocRegion info)
         ILCall     _ v _ -> -- Exists due to mergeAdjacentBlocks.
                             Map.findWithDefault (GCUnknown "") (tidIdent v) mayGCmap
         ILCallPrim _ p _ -> canGCPrim p
         ILTuple    _ _   -> MayGC -- rather than stack allocating tuples, easier to just remove 'em probably.
         ILLiteral _ (LitText _) -> MayGC -- unless we statically allocate such things
         ILLiteral _ (LitInt  _) -> WillNotGC -- unless it's a bignum...
         ILLiteral _ (LitBool _) -> WillNotGC
         ILLiteral _ (LitFloat _)-> WillNotGC
         ILKillProcess {} -> WillNotGC
         ILOccurrence  {} -> WillNotGC
         ILDeref       {} -> WillNotGC
         ILStore       {} -> WillNotGC
         ILBitcast     {} -> WillNotGC
         ILArrayRead   {} -> WillNotGC
         ILArrayPoke   {} -> WillNotGC
         ILObjectCopy  {} -> WillNotGC

canGCPrim (PrimIntTrunc {}) = WillNotGC
canGCPrim (PrimOp       {}) = WillNotGC
canGCPrim (NamedPrim (TypedId _ (GlobalSymbol name))) =
                    if willNotGCGlobal name then WillNotGC
                                            else GCUnknown "canGCPrim:global"
canGCPrim _ = GCUnknown "canGCPrim:other"

willNotGCGlobal name = name `elem` (map T.pack
                        ["expect_i1", "print_i1", "expect_i8", "print_i8"
                        ,"expect_i64" , "print_i64" , "expect_i32", "print_i32"
                        ,"expect_i32b", "print_i32b", "memcpy_i8_to_from_at_len"
                        ,"expect_newline", "print_newline", "prim_arrayLength"
                        ,"prim_print_bytes_stdout", "prim_print_bytes_stderr"
                        ,"print_float_p9f64", "expect_float_p9f64"])
