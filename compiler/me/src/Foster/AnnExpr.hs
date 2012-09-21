{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExpr (AnnExpr(..), annExprAnnot) where

import Foster.Base
import Foster.TypeAST

import Text.PrettyPrint.ANSI.Leijen
import Foster.Output(OutputOr(..))

import qualified Data.Text as T

-- Type-annotated expressions, although not necessarily with valid types.
-- Type checking isn't done until we move to AIExpr. We keep around source
-- ranges for error messages if the final stage of type checking fails.

data AnnExpr ty =
        -- Literals
          AnnBool       ExprAnnot ty Bool
        | AnnString     ExprAnnot ty T.Text
        | AnnInt        { aintRange  :: ExprAnnot
                        , aintType   :: ty
                        , aintLit    :: LiteralInt }
        | AnnFloat      { afltRange  :: ExprAnnot
                        , afltType   :: ty
                        , afltLit    :: LiteralFloat }
        | AnnTuple      ExprAnnot ([ty] -> ty) [AnnExpr ty]
        | E_AnnFn       (Fn (AnnExpr ty) ty)

        -- Control flow
        | AnnIf         ExprAnnot ty (AnnExpr ty) (AnnExpr ty) (AnnExpr ty)
        | AnnUntil      ExprAnnot ty (AnnExpr ty) (AnnExpr ty)
        -- Creation of bindings
        | AnnCase       ExprAnnot ty (AnnExpr ty) [PatternBinding (AnnExpr ty) ty]
        | AnnLetVar     ExprAnnot Ident (AnnExpr ty) (AnnExpr ty)
        -- We have separate syntax for a SCC of recursive functions
        -- because they are compiled differently from non-recursive closures.
        | AnnLetFuns    ExprAnnot [Ident] [Fn (AnnExpr ty) ty] (AnnExpr ty)
        -- Use of bindings
        | E_AnnVar      ExprAnnot (TypedId ty)
        | AnnPrimitive  ExprAnnot (TypedId ty)
        | AnnCall       ExprAnnot ty (AnnExpr ty) [AnnExpr ty]
        -- Mutable ref cells
        | AnnAlloc      ExprAnnot ty              (AnnExpr ty) AllocMemRegion
        | AnnDeref      ExprAnnot ty              (AnnExpr ty)
        | AnnStore      ExprAnnot ty (AnnExpr ty) (AnnExpr ty)
        -- Array operations
        | AnnArrayRead  ExprAnnot ty (ArrayIndex (AnnExpr ty))
        | AnnArrayPoke  ExprAnnot ty (ArrayIndex (AnnExpr ty)) (AnnExpr ty)
        -- Terms indexed by types
        | E_AnnTyApp {  annTyAppRange       :: ExprAnnot
                     ,  annTyAppOverallType :: ty
                     ,  annTyAppExpr        :: (AnnExpr ty)
                     ,  annTyAppArgTypes    :: [ty] }
        -- Others
        | AnnCompiles   ExprAnnot ty (CompilesResult (AnnExpr ty))
        | AnnKillProcess ExprAnnot ty T.Text
        -- We keep kill-process as a primitive rather than translate it to a
        -- call to a primitive because we must ensure that its assigned value
        -- is the undef constant, which wouldn't work through a function call.

-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{

instance TypedWith (AnnExpr TypeAST) TypeAST where
  typeOf annexpr = case annexpr of
     AnnString _ t _       -> t
     AnnBool   _ t _       -> t
     AnnInt   _rng t _     -> t
     AnnFloat _rng t _     -> t
     AnnTuple  _ tf _      -> tf [typeOf e | e <- childrenOf annexpr]
     E_AnnFn annFn         -> fnType annFn
     AnnCall _rng t _ _    -> t
     AnnCompiles _ t _     -> t
     AnnKillProcess _ t _  -> t
     AnnIf _rng t _ _ _    -> t
     AnnUntil _rng t _ _   -> t
     AnnLetVar _rng _ _ b  -> typeOf b
     AnnLetFuns _rng _ _ e -> typeOf e
     AnnAlloc _rng t _ _   -> t
     AnnDeref _rng t _     -> t
     AnnStore _rng t _ _   -> t
     AnnArrayRead _rng t _ -> t
     AnnArrayPoke _ _ _ _  -> TupleTypeAST []
     AnnCase _rng t _ _    -> t
     E_AnnVar _rng tid     -> tidType tid
     AnnPrimitive _rng tid -> tidType tid
     E_AnnTyApp _rng substitutedTy _tm _tyArgs -> substitutedTy

instance Structured (AnnExpr TypeAST) where
  textOf e _width =
    case e of
      AnnString   _rng _  _      -> text "AnnString    "
      AnnBool     _rng _  b      -> text "AnnBool      " <> pretty b
      AnnCall     _rng t _b _args-> text "AnnCall      :: " <> pretty t
      AnnCompiles _rng _ cr      -> text "AnnCompiles  " <> pretty cr
      AnnKillProcess _rng t msg  -> text "AnnKillProcess " <> string (show msg) <> text  " :: " <> pretty t
      AnnIf       _rng t _ _ _   -> text "AnnIf         :: " <> pretty t
      AnnUntil    _rng t _ _     -> text "AnnUntil      :: " <> pretty t
      AnnInt      _rng ty int    -> text "AnnInt       " <> text (litIntText int) <> text " :: " <> pretty ty
      AnnFloat    _rng ty flt    -> text "AnnFloat     " <> text (litFloatText flt) <> text " :: " <> pretty ty
      AnnLetVar   _rng id _a _b  -> text "AnnLetVar    " <> pretty id
      AnnLetFuns  _rng ids _ _   -> text "AnnLetFuns   " <> list (map pretty ids)
      AnnAlloc  {}               -> text "AnnAlloc     "
      AnnDeref  {}               -> text "AnnDeref     "
      AnnStore  {}               -> text "AnnStore     "
      AnnArrayRead _rng t _      -> text "AnnArrayRead :: " <> pretty t
      AnnArrayPoke _rng t _ _    -> text "AnnArrayPoke :: " <> pretty t
      AnnTuple  {}               -> text "AnnTuple     "
      AnnCase   {}               -> text "AnnCase      "
      AnnPrimitive _r tid        -> text "AnnPrimitive " <> pretty tid
      E_AnnVar _r tid            -> text "AnnVar       " <> pretty tid
      E_AnnTyApp _rng t _e argty -> text "AnnTyApp     ["  <> pretty argty <> text  "] :: " <> pretty t
      E_AnnFn annFn              -> text $ "AnnFn " ++ T.unpack (identPrefix $ fnIdent annFn) ++ " // "
        ++ (show $ fnBoundNames annFn) ++ " :: " ++ show (pretty (fnType annFn)) where
                   fnBoundNames :: (Pretty t) => Fn e t -> [String]
                   fnBoundNames fn = map (show . pretty) (fnVars fn)
  childrenOf e =
    case e of
      AnnString {}                         -> []
      AnnBool   {}                         -> []
      AnnCall _r _t b exprs                -> b:exprs
      AnnCompiles  _rng _ (CompilesResult (OK     e)) -> [e]
      AnnCompiles  _rng _ (CompilesResult (Errors _)) -> []
      AnnKillProcess {}                    -> []
      AnnIf        _rng _t  a b c          -> [a, b, c]
      AnnUntil     _rng _t  a b            -> [a, b]
      AnnInt {}                            -> []
      AnnFloat {}                          -> []
      E_AnnFn annFn                        -> [fnBody annFn]
      AnnLetVar    _rng _ a b              -> [a, b]
      AnnLetFuns   _rng _ids fns e         -> (map E_AnnFn fns) ++ [e]
      AnnAlloc     _rng _t a _             -> [a]
      AnnDeref     _rng _t a               -> [a]
      AnnStore     _rng _t a b             -> [a, b]
      AnnArrayRead _rng _t ari             -> childrenOfArrayIndex ari
      AnnArrayPoke _rng _t ari c           -> childrenOfArrayIndex ari ++ [c]
      AnnTuple _rng _ exprs                -> exprs
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

annExprAnnot :: AnnExpr ty -> ExprAnnot
annExprAnnot expr = case expr of
      AnnString    annot _  _       -> annot
      AnnBool      annot _  _       -> annot
      AnnCall      annot _ _ _      -> annot
      AnnCompiles  annot _ _        -> annot
      AnnKillProcess annot _ _      -> annot
      AnnIf        annot _ _ _ _    -> annot
      AnnUntil     annot _ _ _      -> annot
      AnnInt       annot _ _        -> annot
      AnnFloat     annot _ _        -> annot
      E_AnnFn      f                -> fnAnnot f
      AnnLetVar    annot _ _ _      -> annot
      AnnLetFuns   annot _ _ _      -> annot
      AnnAlloc     annot _ _ _      -> annot
      AnnDeref     annot _ _        -> annot
      AnnStore     annot _ _ _      -> annot
      AnnArrayRead annot _ _        -> annot
      AnnArrayPoke annot _ _ _      -> annot
      AnnTuple     annot _ _        -> annot
      AnnCase      annot _ _ _      -> annot
      E_AnnVar     annot _          -> annot
      AnnPrimitive annot _          -> annot
      E_AnnTyApp   annot _ _ _      -> annot

instance SourceRanged (AnnExpr ty) where rangeOf e = annotRange (annExprAnnot e)

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
