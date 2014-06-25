-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ParsedType
where

import Foster.Base
import Foster.Kind
import Foster.ExprAST

import Text.PrettyPrint.ANSI.Leijen(text)

data TypeP =
           PrimIntP       IntSizeBits
         | TyConAppP      DataTypeName [TypeP]
         | TupleTypeP     [TypeP]
         | FnTypeP        { fnTypeDomain :: [TypeP]
                          , fnTypeRange  :: TypeP
                          , fnTypePrecond :: MaybePrecondition (ExprAST TypeP)
                          , fnTypeCallConv :: CallConv
                          , fnTypeProcOrFunc :: ProcOrFunc }
         | CoroTypeP      TypeP TypeP
         | ForAllP        [TypeFormal] TypeP
         | TyVarP         TyVar
         | RefTypeP       TypeP
         | ArrayTypeP     TypeP
         | MetaPlaceholder String

-- Ref and Array and PrimInt types are identified in a post-parsing pass
-- (as type constructors, by name) because there is no special type-level
-- syntax for them. However, we still need them in the parsed-type AST
-- to be able to specify the right types for primitive operations.

instance Show TypeP where
    show x = case x of
        PrimIntP         size         -> "(PrimIntP " ++ show size ++ ")"
        TyConAppP    tc types         -> "(TyCon: " ++ show tc ++ joinWith " " ("":map show types) ++ ")"
        TupleTypeP      types         -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeP    s t p cc cs        -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeP  s t                -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllP  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarP   tv                   -> show tv
        RefTypeP    ty                -> "(Ref " ++ show ty ++ ")"
        ArrayTypeP  ty                -> "(Array " ++ show ty ++ ")"
        MetaPlaceholder s             -> "??" ++ s

instance Structured TypeP where
    textOf e _width =
        case e of
            PrimIntP     size            -> text $ "PrimIntP " ++ show size
            TyConAppP    tc  _           -> text $ "TyConAppP " ++ tc
            TupleTypeP       _           -> text $ "TupleTypeP"
            FnTypeP    _ _  _  _ _       -> text $ "FnTypeP"
            CoroTypeP  _ _               -> text $ "CoroTypeP"
            ForAllP  tvs _rho            -> text $ "ForAllP " ++ show tvs
            TyVarP   tv                  -> text $ "TyVarP " ++ show tv
            RefTypeP    _                -> text $ "RefTypeP"
            ArrayTypeP  _                -> text $ "ArrayTypeP"
            MetaPlaceholder s            -> text $ "MetaPlaceholder " ++ s

    childrenOf e =
        case e of
            PrimIntP         _           -> []
            TyConAppP   _tc types        -> types
            TupleTypeP      types        -> types
            FnTypeP    ss t _ _ _        -> (t:ss)
            CoroTypeP  s t               -> [s, t]
            ForAllP  _tvs rho            -> [rho]
            TyVarP   _tv                 -> []
            RefTypeP    ty               -> [ty]
            ArrayTypeP  ty               -> [ty]
            MetaPlaceholder _            -> []

