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

import Data.IORef(IORef)
import Data.UnionFind.IO(Point)

type RhoTC = TypeTC
type TauTC = TypeTC
type SigmaTC = TypeTC

-- "Refinement status"
data RR = NoRefinement String
        | MbRefinement (Uniq, IORef (Maybe (Ident, AnnExpr TypeTC)))

data Unifiable ty = UniConst ty
                  | UniVar (Uniq, Point (Maybe ty))

data TypeTC =
           PrimIntTC       IntSizeBits             RR
         | PrimFloat64TC                           RR
         | TyConAppTC      DataTypeName [TypeTC]   RR
         | TupleTypeTC     [TypeTC]                RR
         | CoroTypeTC      TypeTC  TypeTC
         | RefTypeTC       TypeTC
         | ArrayTypeTC     TypeTC                  RR
         | FnTypeTC        { fnTypeTCDomain :: [TypeTC]
                           , fnTypeTCRange  :: TypeTC
                           , fnTypeTCCallConv :: Unifiable CallConv
                           , fnTypeTCProcOrFunc :: Unifiable ProcOrFunc }
         | ForAllTC        [(TyVar, Kind)] RhoTC
         | TyVarTC           TyVar
         | MetaTyVarTC     (MetaTyVar TypeTC)
         | RefinedTypeTC   (TypedId TypeTC) (AnnExpr TypeTC) [Ident]

maybeRRofTC x = case x of
        PrimIntTC          _size     rr -> Just rr
        PrimFloat64TC                rr -> Just rr
        TyConAppTC  _tcnm _types     rr -> Just rr
        TupleTypeTC       _types     rr -> Just rr
        FnTypeTC     _s _t _cc _cs      -> Nothing
        CoroTypeTC   _s _t              -> Nothing
        ForAllTC   _tvs _rho            -> Nothing
        TyVarTC    _tv                  -> Nothing
        MetaTyVarTC _                   -> Nothing
        RefTypeTC     _ty               -> Nothing
        ArrayTypeTC   _ty            rr -> Just rr
        RefinedTypeTC _ _ _             -> Nothing

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

instance Show RR where
  show (NoRefinement str) = "(NoRefinement " ++ str ++ ")"
  show (MbRefinement (u,_)) = "(MbRefinement " ++ show u ++ " ...)"

instance Show ty => Show (Unifiable ty) where
  show (UniConst v)   = show v
  show (UniVar (u,_)) = "(UniVar " ++ show u ++ " ...)"

uni_briefCC (UniConst v) = briefCC v
uni_briefCC v = show v

instance Pretty TypeTC where
    pretty x = case x of
        PrimIntTC          size     _rr -> pretty size <+> text (show _rr)
        PrimFloat64TC                 _ -> text "Float64"
        TyConAppTC   tcnm types       _ -> parens $ text tcnm <> hpre (map pretty types)
        TupleTypeTC       types       _ -> tupled $ map pretty types
        FnTypeTC     s t  cc cs         -> text "(" <> pretty s <> text " =" <> text (uni_briefCC cc) <> text "> " <> pretty t <> text " @{" <> text (show cs) <> text "})"
        CoroTypeTC   s t                -> text "(Coro " <> pretty s <> text " " <> pretty t <> text ")"
        ForAllTC   tvs rho              -> text "(forall " <> hsep (prettyTVs tvs) <> text ". " <> pretty rho <> text ")"
        TyVarTC    tv                   -> text (show tv)
        MetaTyVarTC m                   -> text "(~(" <> pretty (descMTVQ (mtvConstraint m)) <> text ")!" <> text (show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")")
        RefTypeTC     ty                -> text "(Ref " <> pretty ty <> text ")"
        ArrayTypeTC   ty              _ -> text "(Array " <> pretty ty <> text ")"
        RefinedTypeTC v _ args          -> text "(Refined " <> pretty (tidType v) <> text " / " <> pretty args <> text ")"

instance Show TypeTC where
    show x = case x of
        TyConAppTC nam types _ -> "(TyConAppTC " ++ nam
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntTC size       _ -> "(PrimIntTC " ++ show size ++ ")"
        PrimFloat64TC        _ -> "(PrimFloat64TC)"
        TupleTypeTC types    _ -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeTC   s t cc cs   -> "(" ++ show s ++ " =" ++ uni_briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeTC s t         -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllTC ktvs rho      -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarTC     tv         -> show tv
        ArrayTypeTC ty       _ -> "(Array " ++ show ty ++ ")"
        RefTypeTC   ty         -> "(Ptr " ++ show ty ++ ")"
        MetaTyVarTC _          -> "(MetaTyVar)"
        RefinedTypeTC v _  _   -> "(RefinedTypeTC " ++ show v ++ ")"

boolTypeTC = PrimIntTC I1           (NoRefinement "boolTypeTC")
stringTypeTC = TyConAppTC "Text" [] (NoRefinement "stringTypeTC")

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
            TyConAppTC nam _types _ -> text $ "TyConAppTC " ++ nam
            PrimIntTC     size    _ -> text $ "PrimIntTC " ++ show size
            PrimFloat64TC         _ -> text $ "PrimFloat64TC"
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
            TyConAppTC _nam types _ -> types
            PrimIntTC       {}      -> []
            PrimFloat64TC         _ -> []
            TupleTypeTC     types _ -> types
            FnTypeTC  ss t _cc _cs  -> ss++[t]
            CoroTypeTC s t          -> [s,t]
            ForAllTC  _ktvs rho     -> [rho]
            TyVarTC        _tv      -> []
            ArrayTypeTC     ty    _ -> [ty]
            RefTypeTC       ty      -> [ty]
            MetaTyVarTC     {}      -> []
            RefinedTypeTC v _ _     -> [tidType v]

fnReturnTypeTC f@(FnTypeTC {}) = fnTypeTCRange f
fnReturnTypeTC (ForAllTC _ f@(FnTypeTC {})) = fnTypeTCRange f
fnReturnTypeTC other = error $
    "Unexpected non-function type in fnReturnType: " ++ show other


