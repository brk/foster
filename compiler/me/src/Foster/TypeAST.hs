-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.TypeAST where

import List(foldr1, intersperse)

data TypeAST =
           MissingTypeAST { missingTypeProgAnnotation :: String }
         | NamedTypeAST     String
         | TupleTypeAST     [TypeAST]
         | FnTypeAST        TypeAST TypeAST (Maybe [String])
         | CoroType         TypeAST TypeAST
         deriving (Eq)

instance Show TypeAST where
    show x = case x of
        (MissingTypeAST s)   -> "(MissingTypeAST " ++ s ++ ")"
        (NamedTypeAST s)     -> s
        (TupleTypeAST types) -> "(" ++ joinWith ", " [show t | t <- types] ++ ")"
        (FnTypeAST s t cs)   -> "(" ++ show s ++ " -> " ++ show t ++ ")"
        (CoroType s t)   -> "(Coro " ++ show s ++ " " ++ show t ++ ")"

fosBoolType = NamedTypeAST "i1"

joinWith :: String -> [String] -> String
joinWith s [] = ""
joinWith s ss = foldr1 (++) (intersperse s ss)

