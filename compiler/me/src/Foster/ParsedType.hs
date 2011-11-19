-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ParsedType
where

import Foster.Base
import Foster.Kind
import Foster.Output(out)

data TypeP =
           PrimIntP       IntSizeBits
         | TyConAppP      DataTypeName [TypeP]
         | TupleTypeP     [TypeP]
         | FnTypeP        { fnTypeDomain :: TypeP
                          , fnTypeRange  :: TypeP
                          , fnTypeCallConv :: CallConv
                          , fnTypeProcOrFunc :: ProcOrFunc }
         | CoroTypeP      TypeP TypeP
         | ForAllP        [TypeFormalAST] TypeP
         | TyVarP         TyVar
         | RefTypeP       TypeP
         | ArrayTypeP     TypeP
         | MetaPlaceholder String

instance Show TypeP where
    show x = case x of
        PrimIntP         size         -> "(PrimIntP " ++ show size ++ ")"
        TyConAppP    tc types         -> "(TyCon: " ++ show tc ++ joinWith " " ("":map show types) ++ ")"
        TupleTypeP      types         -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeP    s t cc cs          -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @{" ++ show cs ++ "})"
        CoroTypeP  s t                -> "(Coro " ++ show s ++ " " ++ show t ++ ")"
        ForAllP  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarP   tv                   -> show tv
        RefTypeP    ty                -> "(Ref " ++ show ty ++ ")"
        ArrayTypeP  ty                -> "(Array " ++ show ty ++ ")"
        MetaPlaceholder s             -> "??" ++ s

instance Structured TypeP where
    textOf e _width =
        case e of
            PrimIntP     size            -> out $ "PrimIntP " ++ show size
            TyConAppP    tc  _           -> out $ "TyConAppP " ++ tc
            TupleTypeP       _           -> out $ "TupleTypeP"
            FnTypeP    _ _  _  _         -> out $ "FnTypeP"
            CoroTypeP  _ _               -> out $ "CoroTypeP"
            ForAllP  tvs _rho            -> out $ "ForAllP " ++ show tvs
            TyVarP   tv                  -> out $ "TyVarP " ++ show tv
            RefTypeP    _                -> out $ "RefTypeP"
            ArrayTypeP  _                -> out $ "ArrayTypeP"
            MetaPlaceholder s            -> out $ "MetaPlaceholder " ++ s

    childrenOf e =
        case e of
            PrimIntP         _           -> []
            TyConAppP   _tc types        -> types
            TupleTypeP      types        -> types
            FnTypeP    s t _ _           -> [s, t]
            CoroTypeP  s t               -> [s, t]
            ForAllP  _tvs rho            -> [rho]
            TyVarP   _tv                 -> []
            RefTypeP    ty               -> [ty]
            ArrayTypeP  ty               -> [ty]
            MetaPlaceholder _            -> []

