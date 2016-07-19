-----------------------------------------------------------------------------
-- Copyright (c) 2011 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ParsedType
where

import Foster.Base
import Foster.ExprAST

import Data.Maybe (maybeToList)

import Text.PrettyPrint.ANSI.Leijen(text)

data TypeP =
           TyConP         DataTypeName
         | TyAppP         TypeP [TypeP]
         | TupleTypeP     [TypeP]
         | FnTypeP        { fnTypeDomain :: [TypeP]
                          , fnTypeRange  :: TypeP
                          , fnTypeEffect :: Maybe TypeP
                          , fnTypeCallConv :: CallConv
                          , fnTypeProcOrFunc :: ProcOrFunc
                          , fnTypeSource :: SourceRange }
         | ForAllP        [TypeFormal] TypeP
         | TyVarP         TyVar
         | RefinedTypeP   String TypeP (ExprAST TypeP)
         | MetaPlaceholder String

instance Show TypeP where
    show x = case x of
        TyConP    nm                  -> "(TyCon: " ++ show nm ++ ")"
        TyAppP    con types           -> show con ++ joinWith " " ("":map show types)
        TupleTypeP      types         -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        FnTypeP    s t fx cc cs _     -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @" ++ show fx ++ " #{" ++ show cs ++ "})"
        ForAllP  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarP   tv                   -> show tv
        MetaPlaceholder s             -> "??" ++ s
        RefinedTypeP nm ty _e         -> "(Refined " ++ nm ++ " : " ++ show ty ++ " : ... )"

instance Structured TypeP where
    textOf e _width =
        case e of
            TyAppP    con  _             -> text $ "TyAppP " ++ show con
            TyConP    nm                 -> text $ "TyConP " ++ nm
            TupleTypeP       _           -> text $ "TupleTypeP"
            FnTypeP    _ _  _ _ _ _      -> text $ "FnTypeP"
            ForAllP  tvs _rho            -> text $ "ForAllP " ++ show tvs
            TyVarP   tv                  -> text $ "TyVarP " ++ show tv
            MetaPlaceholder _s           -> text $ "MetaPlaceholder "
            RefinedTypeP _nm _ty _e      -> text $ "RefinedTypeP"

    childrenOf e =
        case e of
            TyConP      _nm              -> []
            TyAppP      con types        -> con:types
            TupleTypeP      types        -> types
            FnTypeP    ss t fx _ _  _    -> maybeToList fx ++ (t:ss)
            ForAllP  _tvs rho            -> [rho]
            TyVarP   _tv                 -> []
            MetaPlaceholder _            -> []
            RefinedTypeP _ ty _          -> [ty]

