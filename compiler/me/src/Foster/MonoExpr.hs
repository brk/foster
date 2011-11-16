-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.MonoExpr where

import Data.Map(Map)
import qualified Data.Map as Map(elems)

import Foster.Base
import Foster.MonoType
import Foster.MonoLetable
import Foster.CFG(BlockId)
import Foster.PatternMatch(DecisionTree)
import Foster.Output(out, Output)

data MoClosure = MoClosure { moClosureProcIdent :: Ident
                           , moClosureEnvIdent  :: Ident
                           , moClosureCaptures  :: [TypedId MonoType] } deriving Show

data MonoProgram = MoProgram (Map Ident MoProcDef)
                             [MoExternDecl]
                             [DataType MonoType]
                             SourceLines

data MoExternDecl = MoDecl String MonoType deriving (Show)

data MoProcDef =
     MoProcDef { moProcReturnType :: MonoType
               , moProcIdent      :: Ident
               , moProcVars       :: [MoVar]
               , moProcRange      :: SourceRange
               , moProcBlocks     :: [MoBlock]
               }

data MoBlock  = MoBlock BlockId [MoMiddle] MoLast
data MoMiddle = MoLetVal      Ident    MonoLetable
              | MoClosures    [Ident] [MoClosure]
              | MoRebindId    Ident    MoVar
              deriving Show

data MoLast = MoRetVoid
            | MoRet      MoVar
            | MoBr       BlockId
            | MoIf       MonoType MoVar  BlockId   BlockId
            | MoCase     MonoType MoVar (DecisionTree BlockId)

--------------------------------------------------------------------

showMonoProgramStructure :: MonoProgram -> Output
showMonoProgramStructure (MoProgram procdefs _decls _dtypes _lines) =
    concatMap showProcStructure (Map.elems procdefs)
  where
    showProcStructure proc =
        out (show $ moProcIdent proc) ++ (out " // ")
            ++ (out $ show $ map procVarDesc (moProcVars proc))
            ++ (out " ==> ") ++ (out $ show $ moProcReturnType proc)
          ++ out "\n" ++ concatMap showBlock (moProcBlocks proc)
          ++ out "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

    showBlock (MoBlock blockid mids last) =
           out (show blockid ++ "\n")
        ++ out (concatMap (\m -> "\t" ++ show m ++ "\n") mids)
        ++ out (show last ++ "\n\n")

instance Show MoLast where
  show (MoRetVoid      ) = "ret void"
  show (MoRet v        ) = "ret " ++ show v
  show (MoBr  bid      ) = "br " ++ show bid
  show (MoIf ty v b1 b2) = "if<" ++ show ty ++ "> " ++ show v ++ " ? " ++ show b1 ++ " : " ++ show b2
  show (MoCase ty v  dt) = "case<" ++ show ty ++ "> (" ++ show v ++ ") [decisiontree]: {\n" ++ show dt ++ "\n}"
