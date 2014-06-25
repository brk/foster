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

type RhoTC = TypeTC
type TauTC = TypeTC
type SigmaTC = TypeTC

data TypeTC =
           PrimIntTC       IntSizeBits
         | PrimFloat64TC
         | TyConAppTC      DataTypeName [TypeTC]
         | TupleTypeTC     [TypeTC]
         | CoroTypeTC      TypeTC  TypeTC
         | RefTypeTC       TypeTC
         | ArrayTypeTC     TypeTC
         | FnTypeTC        { fnTypeTCDomain :: [TypeTC]
                           , fnTypeTCRange  :: TypeTC
                           , fnTypeTCPrecond :: MaybePrecondition (AnnExpr TypeTC)
                           , fnTypeTCCallConv :: CallConv
                           , fnTypeTCProcOrFunc :: ProcOrFunc }
         | ForAllTC        [(TyVar, Kind)] RhoTC
         | TyVarTC           TyVar
         | MetaTyVarTC     (MetaTyVar TypeTC)
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

instance Pretty TypeTC where
    pretty x = case x of
        PrimIntTC          size         -> pretty size
        PrimFloat64TC                   -> text "Float64"
        TyConAppTC   tcnm types         -> parens $ text tcnm <> hpre (map pretty types)
        TupleTypeTC       types         -> tupled $ map pretty types
        FnTypeTC     s t _precond cc cs -> text "(" <> pretty s <> text " =" <> text (briefCC cc) <> text "> " <> pretty t <> text " @{" <> text (show cs) <> text "})"
        CoroTypeTC   s t                -> text "(Coro " <> pretty s <> text " " <> pretty t <> text ")"
        ForAllTC   tvs rho              -> text "(forall " <> hsep (prettyTVs tvs) <> text ". " <> pretty rho <> text ")"
        TyVarTC    tv                   -> text (show tv)
        MetaTyVarTC m                   -> text "(~(" <> pretty (descMTVQ (mtvConstraint m)) <> text ")!" <> text (show (mtvUniq m) ++ ":" ++ mtvDesc m ++ ")")
        RefTypeTC     ty                -> text "(Ref " <> pretty ty <> text ")"
        ArrayTypeTC   ty                -> text "(Array " <> pretty ty <> text ")"

instance Show TypeTC where
    show x = case x of
        TyConAppTC nam types -> "(TyConAppTC " ++ nam
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntTC size       -> "(PrimIntTC " ++ show size ++ ")"
        PrimFloat64TC        -> "(PrimFloat64TC)"
        TupleTypeTC types    -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeTC   s t _precond cc cs -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeTC s t       -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllTC ktvs rho    -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarTC     tv       -> show tv
        ArrayTypeTC ty       -> "(Array " ++ show ty ++ ")"
        RefTypeTC   ty       -> "(Ptr " ++ show ty ++ ")"
        MetaTyVarTC _        -> "(MetaTyVar)"

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
            TyConAppTC nam _types -> text $ "TyConAppTC " ++ nam
            PrimIntTC     size    -> text $ "PrimIntTC " ++ show size
            PrimFloat64TC         -> text $ "PrimFloat64TC"
            TupleTypeTC   {}      -> text $ "TupleTypeTC"
            FnTypeTC      {}      -> text $ "FnTypeTC"
            CoroTypeTC    {}      -> text $ "CoroTypeTC"
            ForAllTC ktvs _rho    -> text $ "ForAllTC " ++ show ktvs
            TyVarTC       {}      -> text $ "TyVarTC "
            ArrayTypeTC   {}      -> text $ "ArrayTypeTC"
            RefTypeTC     {}      -> text $ "RefTypeTC"
            MetaTyVarTC   {}      -> text $ "MetaTyVarTC"

    childrenOf e =
        case e of
            TyConAppTC _nam types  -> types
            PrimIntTC       {}     -> []
            PrimFloat64TC          -> []
            TupleTypeTC     types  -> types
            FnTypeTC  ss t _precond _cc _cs -> ss++[t]
            CoroTypeTC s t         -> [s,t]
            ForAllTC  _ktvs rho    -> [rho]
            TyVarTC        _tv     -> []
            ArrayTypeTC     ty     -> [ty]
            RefTypeTC       ty     -> [ty]
            MetaTyVarTC     {}     -> []

fnReturnTypeTC f@(FnTypeTC {}) = fnTypeTCRange f
fnReturnTypeTC (ForAllTC _ f@(FnTypeTC {})) = fnTypeTCRange f
fnReturnTypeTC other = error $
    "Unexpected non-function type in fnReturnType: " ++ show other


