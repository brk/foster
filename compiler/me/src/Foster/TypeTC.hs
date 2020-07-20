{-# LANGUAGE Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2014 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeTC where

import Prelude hiding ((<$>))

import Foster.Base
import Foster.Kind
import Foster.AnnExpr(AnnExpr)
import Foster.Config(OrdRef)

import qualified Data.Text as T

import Data.Text.Prettyprint.Doc

import Data.UnionFind.IO(Point)

type RhoTC = TypeTC
type TauTC = TypeTC
type SigmaTC = TypeTC

data Unifiable ty = UniConst ty
                  | UniVar (Uniq, Point (Maybe ty))
                  deriving Eq

instance (PrettyT ty) => PrettyT (Unifiable ty) where
    prettyT (UniConst t) = text "UniConst " <> prettyT t
    prettyT (UniVar (u, _pt)) = text "UniVar " <> pretty u

data TypeTC =
           PrimIntTC       IntSizeBits
         | TyConTC         DataTypeName
         | TyAppTC         TypeTC [TypeTC]
         | RecordTypeTC    [T.Text] [TypeTC]
         | TupleTypeTC     (Unifiable Kind) [TypeTC]
         | RefTypeTC       TypeTC
         | ArrayTypeTC     TypeTC
         | FnTypeTC        { fnTypeTCDomain :: [TypeTC]
                           , fnTypeTCRange  :: TypeTC
                           , fnTypeTCEffect :: TypeTC
                           , fnTypeTCCallConv :: Unifiable CallConv
                           , fnTypeTCProcOrFunc :: Unifiable ProcOrFunc
                           , fnTypeTCLevels :: Levels }
         | ForAllTC        [(TyVar, Kind)] RhoTC
         | TyVarTC           TyVar  (Unifiable Kind)
         | MetaTyVarTC     (MetaTyVar TypeTC)
         | RefinedTypeTC   (TypedId TypeTC) (AnnExpr TypeTC) [Ident]
         deriving Eq

unitTypeTC = TupleTypeTC (UniConst KindPointerSized) []

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

emptyEffectTC = TyAppTC (TyConTC "effect.Empty") []
effectExtendTC eff row = TyAppTC (TyConTC "effect.Extend") [eff, row]

isEmptyEffect t =
  case t of TyAppTC (TyConTC nm) [] | nm == "effect.Empty" -> True
            _ -> False


data Levels = ZeroLevels
            | Levels { levelOld :: OrdRef Level
                     , levelNew :: OrdRef Level
                     } deriving Eq
genericLevel = maxBound :: Level
markedLevel = -1 :: Level



hpre [] = emptyDoc
hpre ds = emptyDoc <+> hsep ds

prettyTVs tvs = map (\(tv,k) -> parens (pretty tv <+> text "::" <+> pretty k)) tvs

instance Show ty => Show (Unifiable ty) where
  show (UniConst v)   = show v
  show (UniVar (u,_)) = "(UniVar " ++ show u ++ " ...)"

uni_briefCC (UniConst v) = briefCC v
uni_briefCC v = show v

prettyFuncProcComment cs =
  case cs of
    UniConst FT_Func -> text ""
    _ -> text " /*" <> string (show cs) <> text "*/ "

instance PrettyT TypeTC where
    prettyT x = case x of
        PrimIntTC          size         -> pretty size
        TyConTC nam                     -> text nam
        TyAppTC con            []       -> prettyT con
        TyAppTC con types               -> parens $ prettyT con <> hpre (map prettyT types)
        RecordTypeTC labels types      -> text "Record" <> tupled (map pretty labels) <> tupled (map prettyT types)
        TupleTypeTC _kind types         -> tupled $ map prettyT types
        FnTypeTC     s t fx  cc cs _    -> text "(" <> prettyT s <> text " ="
                                                    <> string (uni_briefCC cc) <> text ";fx=" <> prettyT fx
                                                    <> text "> " <> prettyT t <> prettyFuncProcComment cs <> text ")"
        ForAllTC   tvs rho              -> text "(forall " <> hsep (prettyTVs tvs) <> text ". " <> prettyT rho <> text ")"
        TyVarTC    tv _mbk              -> string (show tv)
        MetaTyVarTC m                   -> text "(~(" <> pretty (descMTVQ (mtvConstraint m)) <> text ")!"
                                                <> pretty (show (mtvUniq m) ++ ":" ++ (T.unpack $ mtvDesc m) ++ ")")
        RefTypeTC     ty                -> text "(Ref " <> prettyT ty <> text ")"
        ArrayTypeTC   ty                -> text "(Array " <> prettyT ty <> text ")"
        RefinedTypeTC v expr args       -> text "(Refined " <> parens (prettyT v <+> text "::" <> prettyT (tidType v)) <> text " / " <> pretty args <$> showStructure expr <> text ")"

instance Show TypeTC where
    show x = case x of
        TyConTC nam -> T.unpack nam
        TyAppTC con types -> "(TyAppTC " ++ show con
                                      ++ joinWith " " ("":map show types) ++ ")"
        PrimIntTC size         -> "(PrimIntTC " ++ show size ++ ")"
        RecordTypeTC labs types -> "(" ++ joinWith ", " [T.unpack l ++ ": " ++ show t | (l, t) <- zip labs types] ++ ")"
        TupleTypeTC _k types   -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeTC  s t fx cc cs _ -> "(" ++ show s ++ " =" ++ uni_briefCC cc ++ ";fx=" ++ show fx ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        ForAllTC ktvs rho      -> "(ForAll " ++ show ktvs ++ ". " ++ show rho ++ ")"
        TyVarTC     tv _mbk    -> show tv
        ArrayTypeTC ty         -> "(Array " ++ show ty ++ ")"
        RefTypeTC   ty         -> "(Ptr " ++ show ty ++ ")"
        MetaTyVarTC _          -> "(MetaTyVar" ++ show (prettyT x) ++ ")"
        RefinedTypeTC v _  _   -> "(RefinedTypeTC " ++ show v ++ ")"

boolTypeTC = PrimIntTC I1
stringTypeTC = TyAppTC (TyConTC "Text") []

pointedToTypeTC t = case t of
    RefTypeTC y -> y
    _ -> error $ "TypeTC.hs:pointedToType\n"
              ++ "Expected type to be a pointer, but had " ++ show t

pointedToTypeOfVarTC v = case v of
    TypedId (RefTypeTC t) _ -> t
    _ -> error $ "TypeTC.hs:pointedToTypeOfVar\n"
              ++ "Expected variable to be a pointer, but had " ++ show v

-----------------------------------------------------------------------

instance Summarizable TypeTC where
    textOf e _width =
        case e of
            TyConTC nam          -> text nam
            TyAppTC con _types   -> string $ "TyAppTC " ++ show con
            PrimIntTC     size      -> string $ "PrimIntTC " ++ show size
            RecordTypeTC  {}        -> string $ "RecordTypeTC"
            TupleTypeTC   {}        -> string $ "TupleTypeTC"
            FnTypeTC      {}        -> string $ "FnTypeTC"
            ForAllTC ktvs _rho      -> string $ "ForAllTC " ++ show ktvs
            TyVarTC       {}        -> string $ "TyVarTC "
            ArrayTypeTC   {}        -> string $ "ArrayTypeTC"
            RefTypeTC     {}        -> string $ "RefTypeTC"
            MetaTyVarTC   {}        -> string $ "MetaTyVarTC"
            RefinedTypeTC {}        -> string $ "RefinedTypeTC"

instance Structured TypeTC where
    childrenOf e =
        case e of
            TyConTC {}              -> []
            TyAppTC con types       -> con:types
            PrimIntTC       {}      -> []
            RecordTypeTC  _ types   -> types
            TupleTypeTC  _k types   -> types
            FnTypeTC  ss t fx _cc _cs _ -> ss++[t,fx]
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


