{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExpr (
  AnnExpr(..)
, AnnTuple(..)
) where

import Foster.Base
import Foster.TypeAST

import Text.PrettyPrint.ANSI.Leijen(text)
import Foster.Output(OutputOr(..))

import qualified Data.Text as T

-- Type-annotated expressions, although not necessarily with valid types.
-- Type checking isn't done until we move to AIExpr. We keep around source
-- ranges for error messages if the final stage of type checking fails.

data AnnExpr ty =
        -- Literals
          AnnBool       SourceRange Bool
        | AnnString     SourceRange T.Text
        | AnnInt        { aintRange  :: SourceRange
                        , aintType   :: ty
                        , aintLit    :: LiteralInt }
        | AnnFloat      { afltRange  :: SourceRange
                        , afltType   :: ty
                        , afltLit    :: LiteralFloat }
        | AnnTuple      (AnnTuple ty)
        | E_AnnFn       (Fn (AnnExpr ty) ty)

        -- Control flow
        | AnnIf         SourceRange ty (AnnExpr ty) (AnnExpr ty) (AnnExpr ty)
        | AnnUntil      SourceRange ty (AnnExpr ty) (AnnExpr ty)
        -- Creation of bindings
        | AnnCase       SourceRange ty (AnnExpr ty) [PatternBinding (AnnExpr ty) ty]
        | AnnLetVar     SourceRange Ident (AnnExpr ty) (AnnExpr ty)
        -- We have separate syntax for a SCC of recursive functions
        -- because they are compiled differently from non-recursive closures.
        | AnnLetFuns    SourceRange [Ident] [Fn (AnnExpr ty) ty] (AnnExpr ty)
        -- Use of bindings
        | E_AnnVar      SourceRange (TypedId ty)
        | AnnPrimitive  SourceRange (TypedId ty)
        | AnnCall       SourceRange ty (AnnExpr ty) (AnnTuple ty)
        -- Mutable ref cells
        | AnnAlloc      SourceRange              (AnnExpr ty) AllocMemRegion
        | AnnDeref      SourceRange ty           (AnnExpr ty)
        | AnnStore      SourceRange (AnnExpr ty) (AnnExpr ty)
        -- Array operations
        | AnnArrayRead  SourceRange ty (ArrayIndex (AnnExpr ty))
        | AnnArrayPoke  SourceRange ty (ArrayIndex (AnnExpr ty)) (AnnExpr ty)
        -- Terms indexed by types
        | E_AnnTyApp {  annTyAppRange       :: SourceRange
                     ,  annTyAppOverallType :: ty
                     ,  annTyAppExpr        :: (AnnExpr ty)
                     ,  annTyAppArgTypes    :: [ty] }
        -- Others
        | AnnCompiles   SourceRange (CompilesResult (AnnExpr ty))
        | AnnKillProcess SourceRange ty T.Text
        -- We keep kill-process as a primitive rather than translate it to a
        -- call to a primitive because we must ensure that its assigned value
        -- is the undef constant, which wouldn't work through a function call.

data AnnTuple ty = E_AnnTuple { annTupleRange :: SourceRange
                              , annTupleExprs :: [AnnExpr ty] }

-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{

instance TypedWith (AnnExpr TypeAST) TypeAST where
  typeOf annexpr = case annexpr of
     AnnString {}          -> fosStringType
     AnnBool   {}          -> fosBoolType
     AnnInt   _rng t _     -> t
     AnnFloat _rng t _     -> t
     AnnTuple  {}          -> TupleTypeAST [typeOf e | e <- childrenOf annexpr]
     E_AnnFn annFn         -> fnType annFn
     AnnCall _rng t _ _    -> t
     AnnCompiles {}        -> fosBoolType
     AnnKillProcess _ t _  -> t
     AnnIf _rng t _ _ _    -> t
     AnnUntil _rng t _ _   -> t
     AnnLetVar _rng _ _ b  -> typeOf b
     AnnLetFuns _rng _ _ e -> typeOf e
     AnnAlloc _rng e _     -> RefTypeAST (typeOf e)
     AnnDeref _rng t _     -> t
     AnnStore _rng _ _     -> TupleTypeAST []
     AnnArrayRead _rng t _ -> t
     AnnArrayPoke _ _ _ _  -> TupleTypeAST []
     AnnCase _rng t _ _    -> t
     E_AnnVar _rng tid     -> tidType tid
     AnnPrimitive _rng tid -> tidType tid
     E_AnnTyApp _rng substitutedTy _tm _tyArgs -> substitutedTy

instance Structured (AnnExpr TypeAST) where
  textOf e _width =
    case e of
      AnnString   _rng    _      -> text $ "AnnString    "
      AnnBool     _rng    b      -> text $ "AnnBool      " ++ (show b)
      AnnCall     _rng t _b _args-> text $ "AnnCall      " ++ " :: " ++ show t
      AnnCompiles _rng cr        -> text $ "AnnCompiles  " ++ show cr
      AnnKillProcess _rng t msg  -> text $ "AnnKillProcess " ++ show msg ++ " :: " ++ show t
      AnnIf       _rng t _ _ _   -> text $ "AnnIf        " ++ " :: " ++ show t
      AnnUntil    _rng t _ _     -> text $ "AnnUntil     " ++ " :: " ++ show t
      AnnInt      _rng ty int    -> text $ "AnnInt       " ++ (litIntText int) ++ " :: " ++ show ty
      AnnFloat    _rng ty flt    -> text $ "AnnFloat     " ++ (litFloatText flt) ++ " :: " ++ show ty
      AnnLetVar   _rng id _a _b  -> text $ "AnnLetVar    " ++ show id
      AnnLetFuns  _rng ids _ _   -> text $ "AnnLetFuns   " ++ show ids
      AnnAlloc  {}               -> text $ "AnnAlloc     "
      AnnDeref  {}               -> text $ "AnnDeref     "
      AnnStore  {}               -> text $ "AnnStore     "
      AnnArrayRead _rng t _      -> text $ "AnnArrayRead " ++ " :: " ++ show t
      AnnArrayPoke _rng t _ _    -> text $ "AnnArrayPoke " ++ " :: " ++ show t
      AnnTuple  {}               -> text $ "AnnTuple     "
      AnnCase   {}               -> text $ "AnnCase      "
      AnnPrimitive _r tid        -> text $ "AnnPrimitive " ++ show tid
      E_AnnVar _r tid            -> text $ "AnnVar       " ++ show tid
      E_AnnTyApp _rng t _e argty -> text $ "AnnTyApp     [" ++ show argty ++ "] :: " ++ show t
      E_AnnFn annFn              -> text $ "AnnFn " ++ T.unpack (identPrefix $ fnIdent annFn) ++ " // "
        ++ (show $ fnBoundNames annFn) ++ " :: " ++ show (fnType annFn) where
                   fnBoundNames :: (Show t) => Fn e t -> [String]
                   fnBoundNames fn = map show (fnVars fn)
  childrenOf e =
    case e of
      AnnString {}                         -> []
      AnnBool   {}                         -> []
      AnnCall _r _t b argtup               -> b:(annTupleExprs argtup)
      AnnCompiles  _rng (CompilesResult (OK     e)) -> [e]
      AnnCompiles  _rng (CompilesResult (Errors _)) -> []
      AnnKillProcess {}                    -> []
      AnnIf        _rng _t  a b c          -> [a, b, c]
      AnnUntil     _rng _t  a b            -> [a, b]
      AnnInt {}                            -> []
      AnnFloat {}                          -> []
      E_AnnFn annFn                        -> [fnBody annFn]
      AnnLetVar    _rng _ a b              -> [a, b]
      AnnLetFuns   _rng _ids fns e         -> (map E_AnnFn fns) ++ [e]
      AnnAlloc     _rng    a _             -> [a]
      AnnDeref     _rng _t a               -> [a]
      AnnStore     _rng    a b             -> [a, b]
      AnnArrayRead _rng _t ari             -> childrenOfArrayIndex ari
      AnnArrayPoke _rng _t ari c           -> childrenOfArrayIndex ari ++ [c]
      AnnTuple tup                         -> annTupleExprs tup
      AnnCase _rng _t e bs                 -> e:(map snd bs)
      E_AnnVar {}                          -> []
      AnnPrimitive {}                      -> []
      E_AnnTyApp _rng _t a _argty          -> [a]

-----------------------------------------------------------------------

instance AExpr body => AExpr (Fn body t) where
    freeIdents f = let bodyvars =  freeIdents (fnBody f) in
                   let boundvars =  map tidIdent (fnVars f) in
                   bodyvars `butnot` boundvars

instance AExpr (AnnExpr TypeAST) where
    freeIdents e = case e of
        AnnPrimitive {}     -> []
        AnnLetVar _rng  id  b   e -> freeIdents b ++ (freeIdents e `butnot` [id])
        AnnLetFuns _rng ids fns e -> (concatMap freeIdents fns ++ freeIdents e)
                                                                   `butnot` ids
        AnnCase _rng _t e patbnds -> freeIdents e ++ (concatMap patBindingFreeIds patbnds)
        E_AnnFn f                 -> freeIdents f
        E_AnnVar _rng v           -> [tidIdent v]
        _                         -> concatMap freeIdents (childrenOf e)

patBindingFreeIds ((_, binds), expr) =
  freeIdents expr `butnot` map tidIdent binds

-----------------------------------------------------------------------

instance SourceRanged (AnnExpr ty) where
  rangeOf expr = case expr of
      AnnString    rng    _       -> rng
      AnnBool      rng    _       -> rng
      AnnCall      rng _ _ _      -> rng
      AnnCompiles  rng _          -> rng
      AnnKillProcess rng _ _      -> rng
      AnnIf        rng _ _ _ _    -> rng
      AnnUntil     rng _ _ _      -> rng
      AnnInt       rng _ _        -> rng
      AnnFloat     rng _ _        -> rng
      E_AnnFn f                   -> fnRange f
      AnnLetVar    rng _ _ _      -> rng
      AnnLetFuns   rng _ _ _      -> rng
      AnnAlloc     rng   _ _      -> rng
      AnnDeref     rng _ _        -> rng
      AnnStore     rng _ _        -> rng
      AnnArrayRead rng _ _        -> rng
      AnnArrayPoke rng _ _ _      -> rng
      AnnTuple tup                -> annTupleRange tup
      AnnCase      rng _ _ _      -> rng
      E_AnnVar     rng _          -> rng
      AnnPrimitive rng _          -> rng
      E_AnnTyApp   rng _ _ _      -> rng

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
