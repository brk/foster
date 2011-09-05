-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExpr (
  AnnExpr(..)
, AnnFn(..)
, AnnTuple(..)
, typeAST
, fnNameA
) where

import Foster.Base
import Foster.TypeAST

-- Type-annotated expressions, although not necessarily with valid types.
-- Type checking isn't done until we move to AIExpr. We keep around source
-- ranges for error messages if the final stage of type checking fails.

data AnnExpr =
        -- Literals
          AnnBool       SourceRange Bool
        | AnnInt        { aintRange  :: SourceRange
                        , aintType   :: TypeAST
                        , aintLitInt :: LiteralInt }
        | AnnTuple      AnnTuple
        | E_AnnFn       AnnFn

        -- Control flow
        | AnnIf         SourceRange TypeAST AnnExpr AnnExpr AnnExpr
        | AnnUntil      SourceRange TypeAST AnnExpr AnnExpr
        -- Creation of bindings
        | AnnCase       SourceRange TypeAST AnnExpr [(Pattern, AnnExpr)]
        | AnnLetVar     SourceRange Ident AnnExpr AnnExpr
        -- We have separate syntax for a SCC of recursive functions
        -- because they are compiled differently from non-recursive closures.
        | AnnLetFuns    SourceRange [Ident] [AnnFn] AnnExpr
        -- Use of bindings
        | E_AnnVar      SourceRange AnnVar
        | AnnPrimitive  SourceRange AnnVar
        | AnnCall       SourceRange TypeAST AnnExpr AnnTuple
        -- Mutable ref cells
        | AnnAlloc      SourceRange AnnExpr
        | AnnDeref      SourceRange TypeAST AnnExpr
        | AnnStore      SourceRange AnnExpr AnnExpr
        -- Array operations
        | AnnArrayRead  SourceRange TypeAST AnnExpr AnnExpr
        | AnnArrayPoke  SourceRange TypeAST AnnExpr AnnExpr AnnExpr
        -- Terms indexed by types
        | E_AnnTyApp {  annTyAppRange       :: SourceRange
                     ,  annTyAppOverallType :: TypeAST
                     ,  annTyAppExpr        :: AnnExpr
                     ,  annTyAppArgTypes    :: TypeAST }
        -- Others
        | AnnCompiles   SourceRange (CompilesResult AnnExpr)
        deriving (Show)

data AnnTuple = E_AnnTuple { annTupleRange :: SourceRange
                           , annTupleExprs :: [AnnExpr] } deriving (Show)

-- Body annotated, and overall type added.
-- We also record the free identifiers used.
data AnnFn        = AnnFn  { annFnType  :: TypeAST
                           , annFnIdent :: Ident
                           , annFnVars  :: [AnnVar]
                           , annFnBody  :: AnnExpr
                           , annFnFreeVars :: [AnnVar]
                           , annFnRange :: SourceRange
                           } deriving (Show)

fnNameA f = identPrefix (annFnIdent f)

-----------------------------------------------------------------------

typeAST :: AnnExpr -> TypeAST
typeAST annexpr =
  let recur = typeAST in
  case annexpr of
     AnnBool   {}          -> fosBoolType
     AnnInt _rng t _       -> t
     AnnTuple  {}          -> TupleTypeAST [recur e | e <- childrenOf annexpr]
     E_AnnFn annFn         -> annFnType annFn
     AnnCall _rng t _ _    -> t
     AnnCompiles {}        -> fosBoolType
     AnnIf _rng t _ _ _    -> t
     AnnUntil _rng t _ _   -> t
     AnnLetVar _rng _ _ b  -> recur b
     AnnLetFuns _rng _ _ e -> recur e
     AnnAlloc _rng e       -> RefTypeAST (recur e)
     AnnDeref _rng t _     -> t
     AnnStore _rng _ _     -> TupleTypeAST []
     AnnArrayRead _r t _ _ -> t
     AnnArrayPoke _r t _ _ _-> t
     AnnCase _rng t _ _    -> t
     E_AnnVar _rng tid     -> tidType tid
     AnnPrimitive _rng tid -> tidType tid
     E_AnnTyApp _rng substitutedTy _tm _tyArgs -> substitutedTy

-----------------------------------------------------------------------

instance Structured AnnExpr where
  textOf e _width =
    case e of
      AnnBool     _rng    b      -> out $ "AnnBool      " ++ (show b)
      AnnCall     _rng t _b _args-> out $ "AnnCall      " ++ " :: " ++ show t
      AnnCompiles _rng cr        -> out $ "AnnCompiles  " ++ show cr
      AnnIf       _rng t _ _ _   -> out $ "AnnIf        " ++ " :: " ++ show t
      AnnUntil    _rng t _ _     -> out $ "AnnUntil     " ++ " :: " ++ show t
      AnnInt      _rng ty int    -> out $ "AnnInt       " ++ (litIntText int) ++ " :: " ++ show ty
      AnnLetVar   _rng id _a b   -> out $ "AnnLetVar    " ++ show id ++ " :: " ++ show (typeAST b)
      AnnLetFuns  _rng ids _ _   -> out $ "AnnLetFuns   " ++ show ids
      AnnAlloc  {}               -> out $ "AnnAlloc     "
      AnnDeref  {}               -> out $ "AnnDeref     "
      AnnStore  {}               -> out $ "AnnStore     "
      AnnArrayRead _r t _ _      -> out $ "AnnArrayRead " ++ " :: " ++ show t
      AnnArrayPoke _r t _ _ _    -> out $ "AnnArrayPoke " ++ " :: " ++ show t
      AnnTuple  {}               -> out $ "AnnTuple     "
      AnnCase   {}               -> out $ "AnnCase      "
      AnnPrimitive _r tid        -> out $ "AnnPrimitive " ++ show tid
      E_AnnVar _r tid            -> out $ "AnnVar       " ++ show tid
      E_AnnTyApp _rng t _e argty -> out $ "AnnTyApp     [" ++ show argty ++ "] :: " ++ show t
      E_AnnFn annFn              -> out $ "AnnFn " ++ fnNameA annFn ++ " // "
        ++ (show $ annFnBoundNames annFn) ++ " :: " ++ show (annFnType annFn) where
                  annFnBoundNames :: AnnFn -> [String]
                  annFnBoundNames fn = map show (annFnVars fn)
  childrenOf e =
    case e of
      AnnBool {}                           -> []
      AnnCall _r _t b argtup               -> b:(annTupleExprs argtup)
      AnnCompiles  _rng (CompilesResult (OK e))     -> [e]
      AnnCompiles  _rng (CompilesResult (Errors _)) -> []
      AnnIf        _rng _t  a b c          -> [a, b, c]
      AnnUntil     _rng _t  a b            -> [a, b]
      AnnInt {}                            -> []
      E_AnnFn annFn                        -> [annFnBody annFn]
      AnnLetVar    _rng _ a b              -> [a, b]
      AnnLetFuns   _rng _ids fns e         -> (map E_AnnFn fns) ++ [e]
      AnnAlloc     _rng    a               -> [a]
      AnnDeref     _rng _t a               -> [a]
      AnnStore     _rng    a b             -> [a, b]
      AnnArrayRead _rng _t a b             -> [a, b]
      AnnArrayPoke _rng _t a b c           -> [a, b, c]
      AnnTuple tup                         -> annTupleExprs tup
      AnnCase _rng _t e bs                 -> e:(map snd bs)
      E_AnnVar {}                          -> []
      AnnPrimitive {}                      -> []
      E_AnnTyApp _rng _t a _argty          -> [a]

-----------------------------------------------------------------------

instance AExpr AnnFn where
    freeIdents f = let bodyvars =  freeIdents (annFnBody f) in
                   let boundvars = map tidIdent (annFnVars f) in
                   bodyvars `butnot` boundvars

instance AExpr AnnExpr where
    freeIdents e = case e of
        E_AnnVar _rng v     -> [tidIdent v]
        AnnPrimitive {}     -> []
        AnnLetVar _rng id a b     -> freeIdents a ++ (freeIdents b `butnot` [id])
        AnnCase _rng _t e patbnds -> freeIdents e ++ (concatMap patBindingFreeIds patbnds)
        -- Note that all free idents of the bound expr are free in letvar,
        -- but letfuns removes the bound name from that set!
        AnnLetFuns _rng ids fns e -> ((concatMap freeIdents fns) ++ (freeIdents e))
                                     `butnot` ids
        E_AnnFn f -> map tidIdent (annFnFreeVars f)
        _         -> concatMap freeIdents (childrenOf e)

-----------------------------------------------------------------------

instance SourceRanged AnnExpr where
  rangeOf expr = case expr of
      AnnBool      rng    _       -> rng
      AnnCall      rng _ _ _      -> rng
      AnnCompiles  rng _          -> rng
      AnnIf        rng _ _ _ _    -> rng
      AnnUntil     rng _ _ _      -> rng
      AnnInt       rng _ _        -> rng
      E_AnnFn f                   -> annFnRange f
      AnnLetVar    rng _ _ _      -> rng
      AnnLetFuns   rng _ _ _      -> rng
      AnnAlloc     rng   _        -> rng
      AnnDeref     rng _ _        -> rng
      AnnStore     rng _ _        -> rng
      AnnArrayRead rng _ _ _      -> rng
      AnnArrayPoke rng _ _ _ _    -> rng
      AnnTuple tup                -> annTupleRange tup
      AnnCase      rng _ _ _      -> rng
      E_AnnVar     rng _          -> rng
      AnnPrimitive rng _          -> rng
      E_AnnTyApp   rng _ _ _      -> rng

