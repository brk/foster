-----------------------------------------------------------------------------
-- Copyright (c) 2014 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeTC where

import Foster.Base
import Foster.Kind
import Foster.AnnExpr(AnnExpr)

import Text.PrettyPrint.ANSI.Leijen

import Data.UnionFind.IO(Point)

type RhoTC = TypeTC
type TauTC = TypeTC
type SigmaTC = TypeTC

data Unifiable ty = UniConst ty
                  | UniVar (Uniq, Point (Maybe ty))

data TypeTC =
           PrimIntTC       IntSizeBits
         | TyConAppTC      DataTypeName [TypeTC]
         | TupleTypeTC     (Unifiable Kind) [TypeTC]
         | CoroTypeTC      TypeTC  TypeTC
         | RefTypeTC       TypeTC
         | ArrayTypeTC     TypeTC
         | FnTypeTC        { fnTypeTCDomain :: [TypeTC]
                           , fnTypeTCRange  :: TypeTC
                           , fnTypeTCEffect :: TypeTC
                           , fnTypeTCCallConv :: Unifiable CallConv
                           , fnTypeTCProcOrFunc :: Unifiable ProcOrFunc }
         | ForAllTC        [(TyVar, Kind)] RhoTC
         | TyVarTC           TyVar  (Unifiable Kind)
         | MetaTyVarTC     (MetaTyVar TypeTC)
         | RefinedTypeTC   (TypedId TypeTC) (AnnExpr TypeTC) [Ident]

-- The list of idents attached to RefinedTypeTC corresponds to the set of
-- logical binders for the type, which should be a superset of the directly
-- bound variable. For example, given an expression like
--     { va : (% ra : ...) => vb : (%rb : ...) => ... }
-- each refinement would get the list of logical binders [ra, rb].
-- These binders are propagated to Monomo.hs, which uses substRefinementArgs
-- to substitute actual args for refinement variables in the type of called
-- functions.

isTau :: TypeTC -> Bool
isTau (ForAllTC {}) = False
isTau t = all isTau (childrenOf t)

{-
instance Kinded TypeTC where
  kindOf x = case x of
    PrimIntTC   {}       -> KindAnySizeType
    PrimFloat64TC        -> KindAnySizeType
    TyVarTC   _ kind     -> kind
    TyConAppTC  {}       -> KindPointerSized
    TupleTypeTC {}       -> KindPointerSized
    FnTypeTC    {}       -> KindPointerSized
    CoroTypeTC  {}       -> KindPointerSized
    ForAllTC _ktvs rho   -> kindOf rho
    ArrayTypeTC {}       -> KindPointerSized
    RefTypeTC   {}       -> KindPointerSized
-}

hpre [] = empty
hpre ds = empty <+> hsep ds

prettyTVs tvs = map (\(tv,k) -> parens (pretty tv <+> text "::" <+> pretty k)) tvs

descMTVQ MTVSigma = "S"
descMTVQ MTVTau   = "R"

instance Show ty => Show (Unifiable ty) where
  show (UniConst v)   = show v
  show (UniVar (u,_)) = "(UniVar " ++ show u ++ " ...)"

uni_briefCC (UniConst v) = briefCC v
uni_briefCC v = show v

instance Pretty TypeTC where
    pretty x = case x of
        PrimIntTC          size         -> pretty size
        TyConAppTC "Float64" []         -> text "Float64"
        TyConAppTC   tcnm types         -> parens $ text tcnm <> hpre (map pretty types)
        TupleTypeTC _kind types         -> tupled $ map pretty types
        FnTypeTC     s t fx  cc cs      -> text "(" <> pretty s <> text " ="
                                                    <> text (uni_briefCC cc) <> text ";fx=" <> pretty fx
                                                    <> text "> " <> pretty t <> text " @{" <> text (show cs) <> text "})"
        CoroTypeTC   s t                -> text "(Coro " <> pretty s <> text " " <> pretty t <> text ")"
        ForAllTC   tvs rho              -> text "(forall " <> hsep (prettyTVs tvs) <> text ". " <> pretty rho <> text ")"
        TyVarTC    tv _mbk              -> text (show tv)
        MetaTyVarTC m                   -> text "(~(" <> pretty (descMTVQ (mtvConstraint m)) <> text ")!" <> text (show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")")
        RefTypeTC     ty                -> text "(Ref " <> pretty ty <> text ")"
        ArrayTypeTC   ty                -> text "(Array " <> pretty ty <> text ")"
        RefinedTypeTC v _ args          -> text "(Refined " <> parens (pretty v <+> text "::" <> pretty (tidType v)) <> text " / " <> pretty args <> text ")"

instance Show TypeTC where
    show x = case x of
        TyConAppTC nam types   -> "(TyConAppTC " ++ nam
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntTC size         -> "(PrimIntTC " ++ show size ++ ")"
        TupleTypeTC _k types   -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeTC  s t fx cc cs -> "(" ++ show s ++ " =" ++ uni_briefCC cc ++ ";fx=" ++ show fx ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeTC s t         -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllTC ktvs rho      -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarTC     tv _mbk    -> show tv
        ArrayTypeTC ty         -> "(Array " ++ show ty ++ ")"
        RefTypeTC   ty         -> "(Ptr " ++ show ty ++ ")"
        MetaTyVarTC _          -> "(MetaTyVar" ++ show (pretty x) ++ ")"
        RefinedTypeTC v _  _   -> "(RefinedTypeTC " ++ show v ++ ")"

boolTypeTC = PrimIntTC I1
stringTypeTC = TyConAppTC "Text" []

pointedToTypeTC t = case t of
    RefTypeTC y -> y
    _ -> error $ "TypeTC.hs:pointedToType\n"
              ++ "Expected type to be a pointer, but had " ++ show t

pointedToTypeOfVarTC v = case v of
    TypedId (RefTypeTC t) _ -> t
    _ -> error $ "TypeTC.hs:pointedToTypeOfVar\n"
              ++ "Expected variable to be a pointer, but had " ++ show v

-----------------------------------------------------------------------

instance Structured TypeTC where
    textOf e _width =
        case e of
            TyConAppTC nam _types   -> text $ "TyConAppTC " ++ nam
            PrimIntTC     size      -> text $ "PrimIntTC " ++ show size
            TupleTypeTC   {}        -> text $ "TupleTypeTC"
            FnTypeTC      {}        -> text $ "FnTypeTC"
            CoroTypeTC    {}        -> text $ "CoroTypeTC"
            ForAllTC ktvs _rho      -> text $ "ForAllTC " ++ show ktvs
            TyVarTC       {}        -> text $ "TyVarTC "
            ArrayTypeTC   {}        -> text $ "ArrayTypeTC"
            RefTypeTC     {}        -> text $ "RefTypeTC"
            MetaTyVarTC   {}        -> text $ "MetaTyVarTC"
            RefinedTypeTC {}        -> text $ "RefinedTypeTC"

    childrenOf e =
        case e of
            TyConAppTC _nam types   -> types
            PrimIntTC       {}      -> []
            TupleTypeTC  _k types   -> types
            FnTypeTC  ss t fx _cc _cs  -> ss++[t,fx]
            CoroTypeTC s t          -> [s,t]
            ForAllTC  _ktvs rho     -> [rho]
            TyVarTC        _tv _mbk -> []
            ArrayTypeTC     ty      -> [ty]
            RefTypeTC       ty      -> [ty]
            MetaTyVarTC     {}      -> []
            RefinedTypeTC v _ _     -> [tidType v]

fnReturnTypeTC f@(FnTypeTC {}) = fnTypeTCRange f
fnReturnTypeTC (ForAllTC _ f@(FnTypeTC {})) = fnTypeTCRange f
fnReturnTypeTC other = error $
    "Unexpected non-function type in fnReturnType: " ++ show other


