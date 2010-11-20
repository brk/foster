-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST where

import List(foldr1, intersperse)


normalizeTypes :: [TypeAST] -> TypeAST
normalizeTypes ts = case ts of
                        []  -> TypeUnitAST
                        [t] -> t
                        xs  -> TupleTypeAST xs

data TypeAST =
           MissingTypeAST { missingTypeProgAnnotation :: String }
         | TypeUnitAST
         | NamedTypeAST     String
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        TypeAST TypeAST
         deriving (Eq)

instance Show TypeAST where
    show = showTypeAST

fosBoolType = NamedTypeAST "i1"

showTypeAST :: TypeAST -> String
showTypeAST (MissingTypeAST s)   = "(MissingTypeAST " ++ s ++ ")"
showTypeAST (TypeUnitAST)        = "()"
showTypeAST (NamedTypeAST s)     = s
showTypeAST (TupleTypeAST types) = "(" ++ joinWith ", " [showTypeAST t | t <- types] ++ ")"
showTypeAST (FnTypeAST s t)      = "(" ++ show s ++ " -> " ++ show t ++ ")"

joinWith :: String -> [String] -> String
joinWith s ss = foldr1 (++) (intersperse s ss)

