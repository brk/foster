-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExpr where

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
     (AnnBool _rng _)        -> fosBoolType
     (AnnInt _rng t _)       -> t
     (AnnTuple tup)          -> TupleTypeAST [recur e | e <- childrenOf annexpr]
     (E_AnnFn annFn)         -> annFnType annFn
     (AnnCall r t b a)       -> t
     (AnnCompiles _rng _)    -> fosBoolType
     (AnnIf _rng t a b c)    -> t
     (AnnUntil _rng t _ _)   -> t
     (AnnLetVar _rng _ a b)  -> recur b
     (AnnLetFuns _rng _ _ e) -> recur e
     (AnnAlloc _rng e)       -> RefTypeAST (recur e)
     (AnnDeref _rng t _)     -> t
     (AnnStore _rng _ _)     -> TupleTypeAST []
     (AnnArrayRead _r t _ _) -> t
     (AnnArrayPoke _r t _ _ _)-> t
     (AnnCase _rng t _ _)    -> t
     (E_AnnVar _rng tid)     -> tidType tid
     (AnnPrimitive _rng tid) -> tidType tid
     (E_AnnTyApp _rng substitutedTy tm tyArgs) -> substitutedTy

-----------------------------------------------------------------------

instance Structured AnnExpr where
    textOf e width =
        let spaces = Prelude.replicate width '\SP'  in
        case e of
            AnnBool _rng    b       -> out $ "AnnBool      " ++ (show b)
            AnnCall rng t b args    -> out $ "AnnCall      " ++ " :: " ++ show t
            AnnCompiles rng cr      -> out $ "AnnCompiles  " ++ show cr
            AnnIf _rng t  a b c     -> out $ "AnnIf        " ++ " :: " ++ show t
            AnnUntil _rng t a b     -> out $ "AnnUntil     " ++ " :: " ++ show t
            AnnInt _rng ty int      -> out $ "AnnInt       " ++ (litIntText int) ++ " :: " ++ show ty
            AnnLetVar _rng id a b   -> out $ "AnnLetVar    " ++ show id ++ " :: " ++ show (typeAST b)
            AnnLetFuns _r ids fns e -> out $ "AnnLetFuns   " ++ show ids
            AnnAlloc _rng   a       -> out $ "AnnAlloc     "
            AnnDeref _rng t a       -> out $ "AnnDeref     "
            AnnStore _rng   a b     -> out $ "AnnStore     "
            AnnArrayRead _r t _ _   -> out $ "AnnArrayRead " ++ " :: " ++ show t
            AnnArrayPoke _r t _ _ _ -> out $ "AnnArrayPoke " ++ " :: " ++ show t
            AnnTuple     es         -> out $ "AnnTuple     "
            AnnCase _rng t e bs     -> out $ "AnnCase      "
            AnnPrimitive _r tid     -> out $ "AnnPrimitive " ++ show tid
            E_AnnVar _r tid         -> out $ "AnnVar       " ++ show tid
            E_AnnTyApp _rng t e argty -> out $ "AnnTyApp     [" ++ show argty ++ "] :: " ++ show t
            E_AnnFn annFn           -> out $ "AnnFn " ++ fnNameA annFn ++ " // "
              ++ (show $ annFnBoundNames annFn) ++ " :: " ++ show (annFnType annFn) where
                        annFnBoundNames :: AnnFn -> [String]
                        annFnBoundNames fn = map show (annFnVars fn)
    childrenOf e =
        case e of
            AnnBool {}                           -> []
            AnnCall  r t b argtup                -> b:(annTupleExprs argtup)
            AnnCompiles _rng (CompilesResult (OK e))     -> [e]
            AnnCompiles _rng (CompilesResult (Errors _)) -> []
            AnnIf _rng t  a b c                  -> [a, b, c]
            AnnUntil _rng t  a b                 -> [a, b]
            AnnInt {}                            -> []
            E_AnnFn annFn                        -> [annFnBody annFn]
            AnnLetVar _rng _ a b                 -> [a, b]
            AnnLetFuns _rng ids fns e            -> (map E_AnnFn fns) ++ [e]
            AnnAlloc _rng   a                    -> [a]
            AnnDeref _rng t a                    -> [a]
            AnnStore _rng   a b                  -> [a, b]
            AnnArrayRead _rng t a b              -> [a, b]
            AnnArrayPoke _rng t a b c            -> [a, b, c]
            AnnTuple tup                         -> annTupleExprs tup
            AnnCase _rng t e bs                  -> e:(map snd bs)
            E_AnnVar {}                          -> []
            AnnPrimitive {}                      -> []
            E_AnnTyApp _rng t a argty            -> [a]

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
      AnnBool rng    b            -> rng
      AnnCall rng t b argtup      -> rng
      AnnCompiles rng _           -> rng
      AnnIf rng t  a b c          -> rng
      AnnUntil rng t  a b         -> rng
      AnnInt   rng t _            -> rng
      E_AnnFn f                   -> annFnRange f
      AnnLetVar rng _ a b         -> rng
      AnnLetFuns rng ids fns e    -> rng
      AnnAlloc rng   a            -> rng
      AnnDeref rng t a            -> rng
      AnnStore rng   a b          -> rng
      AnnArrayRead rng t _ _      -> rng
      AnnArrayPoke rng t _ _ _    -> rng
      AnnTuple tup                -> annTupleRange tup
      AnnCase rng t e bs          -> rng
      E_AnnVar     rng v          -> rng
      AnnPrimitive rng v          -> rng
      E_AnnTyApp rng t a argty    -> rng

