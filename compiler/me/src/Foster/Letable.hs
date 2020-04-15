{-# LANGUAGE Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.Letable where

import Foster.Base(Literal(..), CtorId, CtorRepr(..), ArrayIndex(..),
                   AllocMemRegion, AllocInfo(..), Occurrence, AllocationSource,
                   FosterPrim(..),
                   TypedId(..), mapRight, ZeroInit,
                   TExpr(freeTypedIds), TypedWith(..))
import Foster.MonoType
import Foster.TypeLL
import Foster.Kind
import Foster.SourceRange(SourceRange)

import qualified Data.Text as T

-- The reason we have both ILAllocate and ILAlloc is that
-- LLCodegen performs auto-loads from stack slots, which
-- means that a derived ILAlloc can't return a stack slot value!

data Letable ty =
          ILLiteral     ty Literal
        | ILTuple       Kind [TypedId ty] AllocationSource
        | ILKillProcess ty T.Text
        -- Struct member lookup
        | ILOccurrence  ty (TypedId ty) (Occurrence ty)
        -- Varieties of applications
        | ILCallPrim    ty (FosterPrim ty) [TypedId ty]
        | ILCall        ty (TypedId    ty) [TypedId ty]
        | ILAppCtor     ty (CtorId, CtorRepr) [TypedId ty] SourceRange
        -- Stack/heap slot allocation
        | ILAllocate    (AllocInfo ty) SourceRange
        -- Mutable ref cells
        | ILAlloc       (TypedId ty) AllocMemRegion SourceRange
        | ILDeref       ty           (TypedId ty)
        | ILStore       (TypedId ty) (TypedId ty)
        -- Array operations
        | ILAllocArray  ty (TypedId ty) AllocMemRegion ZeroInit SourceRange
        | ILArrayRead   ty (ArrayIndex (TypedId ty))
        | ILArrayPoke      (ArrayIndex (TypedId ty)) (TypedId ty)
        | ILArrayLit    ty (TypedId ty) [Either Literal (TypedId ty)]
        -- Others
        | ILBitcast     ty (TypedId ty) -- inserted during monomorphization
        deriving (Functor, Show, Eq)

instance TExpr (Letable ty) ty where
  freeTypedIds letable = case letable of
      ILLiteral      {} -> []
      ILTuple    _ vs _ -> vs
      ILKillProcess  {} -> []
      ILOccurrence _ v _-> [v]
      ILCallPrim _ _ vs -> vs
      ILCall     _ v vs -> (v:vs)
      ILAppCtor  _ _ vs _sr -> vs
      ILAlloc      v _  _sr -> [v]
      ILDeref    _ v    -> [v]
      ILStore      v v2 -> [v,v2]
      ILBitcast  _ v    -> [v]
      ILAllocArray _ v _ _ _sr -> [v]
      ILArrayRead _ ai  -> freeTypedIds ai
      ILArrayPoke   ai v-> (v):(freeTypedIds ai)
      ILArrayLit _ arr vals -> arr:[val | Right val <- vals]
      ILAllocate _ _sr     -> []

instance TypedWith (Letable MonoType) MonoType where
  typeOf letable = case letable of
      ILLiteral     t _ -> t
      ILTuple    _ vs _ -> TupleType (map tidType vs)
      ILKillProcess t _ -> t
      ILOccurrence t _ _-> t
      ILCallPrim t _ _  -> t
      ILCall     t _ _  -> t
      ILAppCtor  t _ _ _sr -> t
      ILAlloc      v _ _sr -> PtrType (tidType v)
      ILDeref      t _  -> t
      ILStore       {}  -> TupleType []
      ILBitcast    t _  -> t
      ILAllocArray t _ _ _ _sr -> t
      ILArrayRead  t _  -> t
      ILArrayPoke   {}  -> TupleType []
      ILArrayLit t _ _  -> t -- or arrayOf t?
      ILAllocate info _sr  -> PtrType (allocType info)

instance TypedWith (Letable TypeLL) TypeLL where
  typeOf letable = case letable of
      ILLiteral     t _ -> t
      ILTuple KindAnySizeType  vs _ ->           (LLStructType (map tidType vs))
      ILTuple _                vs _ -> LLPtrType (LLStructType (map tidType vs))
      ILKillProcess t _ -> t
      ILOccurrence t _ _-> t
      ILCallPrim t _ _  -> t
      ILCall     t _ _  -> t
      ILAppCtor  t _ _ _sr -> t
      ILAlloc      v _ _sr -> LLPtrType (tidType v)
      ILDeref    t _    -> t
      ILStore      {}   -> LLPtrType (LLStructType [])
      ILBitcast  t _    -> t
      ILAllocArray t _ _ _ _sr -> t
      ILArrayRead t _   -> t
      ILArrayPoke   _ _ -> LLPtrType (LLStructType [])
      ILArrayLit  t _ _ -> t
      ILAllocate info _sr  -> LLPtrType (allocType info)

isPurePrim _ = False -- TODO: recognize pure primitives
isPureFunc _ = False -- TODO: use effect information to refine this predicate.

substVarsInLetable :: (TypedId t -> TypedId t) -> Letable t -> Letable t
substVarsInLetable s letable = case letable of
  ILLiteral     {}                         -> letable
  ILKillProcess {}                         -> letable
  ILAllocate    {}                         -> letable
  ILTuple  kind vs asrc                    -> ILTuple  kind (map s vs) asrc
  ILOccurrence  t v occ                    -> ILOccurrence  t (s v) occ
  ILCallPrim    t p vs                     -> ILCallPrim    t p     (map s vs)
  ILCall        t v vs                     -> ILCall        t (s v) (map s vs)
  ILAppCtor     t c vs sr                  -> ILAppCtor     t c     (map s vs) sr
  ILAlloc       v rgn  sr                  -> ILAlloc       (s v) rgn sr
  ILDeref       t v                        -> ILDeref       t (s v)
  ILStore       v1 v2                      -> ILStore       (s v1) (s v2)
  ILBitcast     t v                        -> ILBitcast     t (s v)
  ILAllocArray  t v amr zi sr              -> ILAllocArray  t (s v) amr zi sr
  ILArrayRead   t (ArrayIndex v1 v2 rng a) -> ILArrayRead   t (ArrayIndex (s v1) (s v2) rng a)
  ILArrayPoke  (ArrayIndex v1 v2 rng a) v3 -> ILArrayPoke  (ArrayIndex (s v1) (s v2) rng a) (s v3)
  ILArrayLit    t arr vals -> ILArrayLit t (s arr) (mapRight s vals)

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
      ILBitcast      {} -> 0
      ILAllocArray   {} -> 1
      ILArrayRead    {} -> 1
      ILArrayPoke    {} -> 1
      ILArrayLit _ _ vals -> length vals

isPure :: Letable t -> Bool
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
      ILBitcast      {} -> True
      ILAllocArray   {} -> True
      ILArrayRead    {} -> True
      ILArrayPoke    {} -> False -- as with store
      ILArrayLit     {} -> True -- as with tuples
