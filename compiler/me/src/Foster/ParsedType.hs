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
import Foster.SourceRange(SourceRange)

import Data.Maybe (maybeToList)
import qualified Data.Text as T

data TypeP =
           TyConP         DataTypeName
         | TyAppP         TypeP [TypeP]
         | RecordTypeP    [T.Text] [TypeP]
         | TupleTypeP     Kind  [TypeP]
         | FnTypeP        { fnTypeDomain :: [TypeP]
                          , fnTypeRange  :: TypeP
                          , fnTypeEffect :: Maybe TypeP
                          , fnTypeCallConv :: CallConv
                          , fnTypeProcOrFunc :: ProcOrFunc
                          , fnTypeSource :: SourceRange }
         | ForAllP        [TypeFormal] TypeP
         | TyVarP         TyVar
         | RefinedTypeP   T.Text TypeP (ExprAST TypeP)
         | MetaPlaceholder String

instance Show TypeP where
    show x = case x of
        TyConP    nm                  -> "(TyCon: " ++ show nm ++ ")"
        TyAppP    con types           -> "(" ++ show con ++ joinWith " " ("":map show types) ++ ")"
        RecordTypeP _ types           -> "(RecordTyP: " ++ show types ++ ")"
        TupleTypeP k  types           -> "(" ++ joinWith ", " [show t | t <- types] ++ ")" ++ kindAsHash k
        FnTypeP    s t fx cc cs _     -> "(" ++ show s ++ " =" ++ briefCC cc ++ "> " ++ show t ++ " @" ++ show fx ++ " #{" ++ show cs ++ "})"
        ForAllP  tvs rho              -> "(ForAll " ++ show tvs ++ ". " ++ show rho ++ ")"
        TyVarP   tv                   -> show tv
        MetaPlaceholder s             -> "??" ++ s
        RefinedTypeP nm ty _e         -> "(Refined " ++ T.unpack nm ++ " : " ++ show ty ++ " : ... )"

instance Summarizable TypeP where
    textOf e _width =
        case e of
            TyAppP    con  _             -> string $ "TyAppP " ++ show con
            TyConP    nm                 -> string $ "TyConP " ++ T.unpack nm
            RecordTypeP _ _              -> string $ "RecordTypeP"
            TupleTypeP k     _           -> string $ "TupleTypeP" ++ kindAsHash k
            FnTypeP    _ _  _ _ _ _      -> string $ "FnTypeP"
            ForAllP  tvs _rho            -> string $ "ForAllP " ++ show tvs
            TyVarP   tv                  -> string $ "TyVarP " ++ show tv
            MetaPlaceholder _s           -> string $ "MetaPlaceholder "
            RefinedTypeP _nm _ty _e      -> string $ "RefinedTypeP"

instance Structured TypeP where
    childrenOf e =
        case e of
            TyConP      _nm              -> []
            TyAppP      con types        -> con:types
            RecordTypeP _labels types    -> types
            TupleTypeP _k   types        -> types
            FnTypeP    ss t fx _ _  _    -> maybeToList fx ++ (t:ss)
            ForAllP  _tvs rho            -> [rho]
            TyVarP   _tv                 -> []
            MetaPlaceholder _            -> []
            RefinedTypeP _ ty _          -> [ty]

