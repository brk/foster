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
import Foster.Output(out, Output)

data MoClosure = MoClosure { moClosureProcIdent :: Ident
                           , moClosureEnvIdent  :: Ident
                           , moClosureCaptures  :: [TypedId MonoType]
                           , moClosureAllocSite :: AllocationSource
                           } deriving Show

data MonoProgram = MoProgram (Map Ident MoProcDef)
                             [MoExternDecl]
                             [DataType MonoType]
                             SourceLines

data MoExternDecl = MoExternDecl String MonoType deriving (Show)

data MoProcDef =
     MoProcDef { moProcReturnType :: MonoType
               , moProcIdent      :: Ident
               , moProcVars       :: [MoVar]
               , moProcRange      :: SourceRange
               , moProcBlocks     :: [MoBlock]
               }

data MoBlock  = MoBlock (BlockId, [MoVar]) [MoMiddle] MoLast (Maybe Int)
data MoMiddle = MoLetVal      Ident    MonoLetable
              | MoClosures    [Ident] [MoClosure]
              | MoRebindId    Ident    MoVar
              | MoLetBitcast  Ident    MoVar
              deriving Show

data MoLast = MoRetVoid
            | MoRet      MoVar
            | MoBr       BlockId [TypedId MonoType]
            | MoCase     MoVar [(CtorId, BlockId)] (Maybe BlockId) (Occurrence MonoType)

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

    showBlock (MoBlock blockid mids last numPreds) =
           out (show blockid ++ " (" ++ show numPreds ++ " preds)\n")
        ++ out (concatMap (\m -> "\t" ++ show m ++ "\n") mids)
        ++ out (show last ++ "\n\n")

instance Show MoLast where
  show (MoRetVoid     ) = "ret void"
  show (MoRet v       ) = "ret " ++ show v
  show (MoBr  bid args) = "br " ++ show bid ++ " , " ++ show args
  show (MoCase v _arms _def _occ) = "case(" ++ show v ++ ")"
