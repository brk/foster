{-# LANGUAGE StandaloneDeriving #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.AnnExpr (AnnExpr(..), annExprAnnot) where

import Foster.Base
import Foster.Kind
import Foster.TypeAST()
import Foster.SourceRange(SourceRanged, rangeOf)

import Data.Text.Prettyprint.Doc
import Foster.Output(OutputOr(..))

import qualified Data.Set as Set(union, unions, fromList)

import qualified Data.Text as T

-- Type-annotated expressions, although not necessarily with valid types.
-- Type checking isn't done until we move to AIExpr. We keep around source
-- ranges for error messages if the final stage of type checking fails.

data AnnExpr ty =
        -- Literals
          AnnLiteral    ExprAnnot ty Literal
        | AnnRecord     ExprAnnot ty [T.Text] [AnnExpr ty]
        | AnnTuple      ExprAnnot ty Kind [AnnExpr ty]
        | E_AnnFn       (Fn () (AnnExpr ty) ty)
        -- Control flow
        | AnnIf         ExprAnnot ty (AnnExpr ty) (AnnExpr ty) (AnnExpr ty)
        | AnnHandler    ExprAnnot ty ty (AnnExpr ty) [CaseArm Pattern (AnnExpr ty) ty] (Maybe (AnnExpr ty)) ResumeIds
        -- Creation of bindings
        | AnnCase       ExprAnnot ty (AnnExpr ty) [CaseArm Pattern (AnnExpr ty) ty]
        | AnnLetVar     ExprAnnot Ident (AnnExpr ty) (AnnExpr ty)
        -- We have separate syntax for a SCC of recursive functions
        -- because they are compiled differently from non-recursive closures.
        | AnnLetFuns    ExprAnnot [Ident] [Fn () (AnnExpr ty) ty] (AnnExpr ty)
        | AnnLetRec     ExprAnnot [Ident] [AnnExpr ty] (AnnExpr ty)
        -- Use of bindings
        | E_AnnVar      ExprAnnot (TypedId ty, Maybe CtorId)
        | AnnPrimitive  ExprAnnot ty (FosterPrim ty)
        | AnnCall       ExprAnnot ty (AnnExpr ty) [AnnExpr ty] CallAnnot
        | AnnAppCtor    ExprAnnot ty CtorId       [AnnExpr ty]
        -- Mutable ref cells
        | AnnAlloc      ExprAnnot ty              (AnnExpr ty) AllocMemRegion
        | AnnDeref      ExprAnnot ty              (AnnExpr ty)
        | AnnStore      ExprAnnot ty (AnnExpr ty) (AnnExpr ty)
        -- Array operations
        | AnnAllocArray ExprAnnot ty (AnnExpr ty) ty (Maybe AllocMemRegion) ZeroInit
        | AnnArrayLit   ExprAnnot ty [Either Literal (AnnExpr ty)]
        | AnnArrayRead  ExprAnnot ty (ArrayIndex (AnnExpr ty))
        | AnnArrayPoke  ExprAnnot ty (ArrayIndex (AnnExpr ty)) (AnnExpr ty)
        -- Terms indexed by types
        | E_AnnTyApp {  annTyAppRange       :: ExprAnnot
                     ,  annTyAppOverallType :: ty
                     ,  annTyAppExpr        :: (AnnExpr ty)
                     ,  annTyAppArgTypes    :: [ty] }
        -- Others
        | AnnCompiles    ExprAnnot ty (CompilesResult (AnnExpr ty))
        | AnnKillProcess ExprAnnot ty T.Text
        -- We keep kill-process as a primitive rather than translate it to a
        -- call to a primitive because we must ensure that its assigned value
        -- is the undef constant, which wouldn't work through a function call.

-- ||||||||||||||||||||||||| Boilerplate ||||||||||||||||||||||||{{{

instance TypedWith (AnnExpr ty) ty where
  typeOf annexpr = case annexpr of
     AnnLiteral  _ t _     -> t
     AnnRecord _ t _labs _exprs -> t
     AnnTuple _ t _k _exprs -> t
     E_AnnFn annFn         -> fnType annFn
     AnnCall _rng t _ _ _  -> t
     AnnAppCtor _rng t _ _ -> t
     AnnCompiles _ t _     -> t
     AnnKillProcess _ t _  -> t
     AnnIf _rng t _ _ _    -> t
     AnnLetVar _rng _ _ b  -> typeOf b
     AnnLetRec _rng _ _ b  -> typeOf b
     AnnLetFuns _rng _ _ e -> typeOf e
     AnnAlloc _rng t _ _   -> t
     AnnDeref _rng t _     -> t
     AnnStore _rng t _ _   -> t
     AnnArrayLit  _rng t _ -> t
     AnnArrayRead _rng t _ -> t
     AnnArrayPoke  _ t _ _ -> t
     AnnAllocArray _ t _ _ _ _ -> t
     AnnHandler _rng t _ _ _ _ _ -> t
     AnnCase _rng t _ _    -> t
     E_AnnVar _rng (tid, _)-> tidType tid
     AnnPrimitive _rng t _ -> t
     E_AnnTyApp _rng substitutedTy _tm _tyArgs -> substitutedTy

instance PrettyT ty => Summarizable (AnnExpr ty) where
  textOf e _width =
    case e of
      AnnLiteral _ _  (LitText _)  -> text "AnnText      "
      AnnLiteral _ _  (LitBool b)  -> text "AnnBool      " <> pretty b
      AnnLiteral _ ty (LitInt int) -> text "AnnInt       " <> text (litIntText int) <> text " :: " <> prettyT ty
      AnnLiteral _ ty (LitFloat f) -> text "AnnFloat     " <> text (litFloatText f) <> text " :: " <> prettyT ty
      AnnLiteral _ ty (LitByteArray _) -> text "AnnBytes     " <> text " :: " <> prettyT ty

      AnnCall     _rng t _b _ _  -> text "AnnCall      :: " <> prettyT t
      AnnAppCtor  _rng t _ _     -> text "AnnAppCtor   :: " <> prettyT t
      AnnCompiles _rng _ cr      -> text "AnnCompiles  " <> pretty cr
      AnnKillProcess _rng t msg  -> text "AnnKillProcess " <> pretty (show msg) <> text  " :: " <> prettyT t
      AnnIf       _rng t _ _ _   -> text "AnnIf         :: " <> prettyT t
      AnnLetVar   _rng id _a _b  -> text "AnnLetVar    " <> pretty id
      AnnLetRec   _rng ids _ _   -> text "AnnLetRec    " <> list (map pretty ids)
      AnnLetFuns  _rng ids _ _   -> text "AnnLetFuns   " <> list (map pretty ids)
      AnnAlloc  {}               -> text "AnnAlloc     "
      AnnDeref  {}               -> text "AnnDeref     "
      AnnStore  {}               -> text "AnnStore     "
      AnnArrayLit   _rng _ _     -> text "AnnArrayLit  "
      AnnAllocArray _rng _ _ aty _ _ -> text "AnnAllocArray:: " <> prettyT aty
      AnnArrayRead  _rng t _     -> text "AnnArrayRead :: " <> prettyT t
      AnnArrayPoke  _rng t _ _   -> text "AnnArrayPoke :: " <> prettyT t
      AnnRecord {}               -> text "AnnRecord    "
      AnnTuple  {}               -> text "AnnTuple     "
      AnnHandler {}              -> text "AnnHandler   "
      AnnCase   {}               -> text "AnnCase      "
      AnnPrimitive _r _ p        -> text "AnnPrimitive " <> prettyT p
      E_AnnVar _r (tid, _)       -> text "AnnVar       " <> prettyT tid <> text " :: " <> prettyT (tidType tid)
      E_AnnTyApp _rng t _e argty -> text "AnnTyApp     ["  <> prettyT argty <> text  "] :: " <> prettyT t
      E_AnnFn annFn              -> text "AnnFn " <> text (identPrefix $ fnIdent annFn) <> text " // "
        <> (prettyT $ fnVars annFn) <> text " :: " <> prettyT (fnType annFn)



instance Structured (AnnExpr ty) where
  childrenOf e =
    case e of
      AnnLiteral {}                        -> []
      AnnCall _r _t b exprs _              -> b:exprs
      AnnAppCtor _r _t _cid exprs          -> exprs
      AnnCompiles  _rng _ (CompilesResult (OK     e)) -> [e]
      AnnCompiles  _rng _ (CompilesResult (Errors _)) -> []
      AnnKillProcess {}                    -> []
      AnnIf        _rng _t  a b c          -> [a, b, c]
      E_AnnFn annFn                        -> [fnBody annFn]
      AnnLetVar    _rng _ a b              -> [a, b]
      AnnLetRec    _rng _ exprs e          -> exprs ++ [e]
      AnnLetFuns   _rng _ids fns e         -> (map E_AnnFn fns) ++ [e]
      AnnAlloc     _rng _t a _             -> [a]
      AnnDeref     _rng _t a               -> [a]
      AnnStore     _rng _t a b             -> [a, b]
      AnnAllocArray _rng _ e _ _ _         -> [e]
      AnnArrayLit  _rng _t exprs           -> rights exprs
      AnnArrayRead _rng _t ari             -> childrenOfArrayIndex ari
      AnnArrayPoke _rng _t ari c           -> childrenOfArrayIndex ari ++ [c]
      AnnRecord _rng _ _ exprs             -> exprs
      AnnTuple _rng _ _ exprs              -> exprs
      AnnHandler _rng _ _ e bs mb_e _resid -> e:(concatMap caseArmExprs bs)++(case mb_e of
                                                                                  Nothing -> []
                                                                                  Just x  -> [x])
      AnnCase _rng _t e bs                 -> e:(concatMap caseArmExprs bs)
      E_AnnVar {}                          -> []
      AnnPrimitive {}                      -> []
      E_AnnTyApp _rng _t a _argty          -> [a]

rights :: [Either a b] -> [b]
rights [] = []
rights (x:xs) = case x of Left _  -> rights xs
                          Right z -> z:(rights xs)

-----------------------------------------------------------------------

instance (Structured ty, PrettyT ty) => AExpr (AnnExpr ty) where
    freeIdents e = case e of
        AnnPrimitive {}     -> Set.fromList []
        AnnLetVar _rng  id  b   e -> freeIdents b `Set.union` (freeIdents e `sans` [id])
        AnnLetRec _rng  ids xps e -> (combinedFreeIdents xps `Set.union` freeIdents e) `sans` ids
        AnnLetFuns _rng ids fns e -> (combinedFreeIdents fns `Set.union` freeIdents e) `sans` ids
        AnnHandler _rng _t _ e arms mb_xform (resumeid,resbareid)
                                  -> freeIdents e `Set.union` (Set.unions (map caseArmFreeIds arms) `sans` [resumeid, resbareid])
                                                                                                  `Set.union` freeIdents mb_xform
        AnnCase _rng _t e arms    -> freeIdents e `Set.union` (Set.unions (map caseArmFreeIds arms))
        E_AnnFn f                 -> freeIdents f
        E_AnnVar _rng (v, _)      -> Set.fromList [tidIdent v]
        _                         -> combinedFreeIdents (childrenOf e)

-----------------------------------------------------------------------

annExprAnnot :: AnnExpr ty -> ExprAnnot
annExprAnnot expr = case expr of
      AnnLiteral   annot _ _        -> annot
      AnnCall      annot _ _ _ _    -> annot
      AnnAppCtor   annot _ _ _      -> annot
      AnnCompiles  annot _ _        -> annot
      AnnKillProcess annot _ _      -> annot
      AnnIf        annot _ _ _ _    -> annot
      E_AnnFn      f                -> fnAnnot f
      AnnLetVar    annot _ _ _      -> annot
      AnnLetRec    annot _ _ _      -> annot
      AnnLetFuns   annot _ _ _      -> annot
      AnnAlloc     annot _ _ _      -> annot
      AnnDeref     annot _ _        -> annot
      AnnStore     annot _ _ _      -> annot
      AnnArrayLit  annot _ _        -> annot
      AnnAllocArray annot _ _ _ _ _ -> annot
      AnnArrayRead annot _ _        -> annot
      AnnArrayPoke annot _ _ _      -> annot
      AnnRecord    annot _ _ _      -> annot
      AnnTuple     annot _ _ _      -> annot
      AnnHandler  annot _ _ _ _ _ _ -> annot
      AnnCase      annot _ _ _      -> annot
      E_AnnVar     annot _          -> annot
      AnnPrimitive annot _ _        -> annot
      E_AnnTyApp   annot _ _ _      -> annot

instance SourceRanged (AnnExpr ty) where rangeOf e = rangeOf (annExprAnnot e)

deriving instance (Eq ty) => Eq (AnnExpr ty)
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||
