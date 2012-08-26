{-# LANGUAGE GADTs, TypeSynonymInstances, BangPatterns #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ILExpr where

import Compiler.Hoopl

import Foster.Base
import Foster.CFG
import Foster.CloConv
import Foster.MonoType
import Foster.Letable
import Foster.Output(out, Output)

--------------------------------------------------------------------

-- | Performs closure conversion and lambda lifting, and also
-- | transforms back from Hoopl's CFG representation to lists-of-blocks.
-- |
-- | We also perform pattern match compilation at this stage.
-- |
-- | The primary differences in the general structure are:
-- |  #. LetFuns replaced with (Let)Closures
-- |  #. Module  replaced with ILProgram
-- |  #. Fn replaced with ProcDef
-- |  #. Decision trees replaced with flat switches

--------------------------------------------------------------------

-- A program consists of top-level data types and mutually-recursive procedures.
data ILProgram = ILProgram --(Map Ident ILProcDef)
                           [ILProcDef]
                           [MoExternDecl]
                           [DataType MonoType]
                           SourceLines

data ILExternDecl = ILDecl String MonoType deriving (Show)

type ILProcDef = Proc [ILBlock]

-- The standard definition of a basic block and its parts.
data ILBlock  = Block BlockEntry [ILMiddle] ILLast
data ILMiddle = ILLetVal      Ident    Letable
              -- This is equivalent to MinCaml's make_closure ...
              | ILClosures    [Ident] [Closure]
              deriving Show

--------------------------------------------------------------------

prepForCodegen :: ModuleIL CCBody MonoType -> ILProgram
prepForCodegen m =
    let decls = map (\(s,t) -> MoExternDecl s t) (moduleILdecls m) in
    let dts = moduleILprimTypes m ++ moduleILdataTypes m in
    let procs = map deHooplize (flatten $ moduleILbody m) in
    ILProgram procs decls dts (moduleILsourceLines m)

flatten :: CCBody -> [CCProc]
flatten (CCB_Procs procs _) = procs

deHooplize :: Proc BasicBlockGraph' -> Proc [ILBlock]
deHooplize p = p { procBlocks = flattenGraph (procBlocks p) }

flattenGraph :: BasicBlockGraph' -> [ILBlock]
flattenGraph bbgp =
   let jumpTo bg = case bbgpEntry bg of (bid, _) -> CCLast $ ILBr bid [] in
   let hblocks = preorder_dfs $ mkLast (jumpTo bbgp) |*><*| bbgpBody bbgp in
   map deHooplizeBlock hblocks

deHooplizeBlock :: Block Insn' C C -> ILBlock
deHooplizeBlock b = let (f, ms, l) = blockSplit b in
                    Block (frs f) (map mid (blockToList ms)) (fin l)
  where mid :: Insn' O O -> ILMiddle
        mid (CCLetVal id letable)    = ILLetVal   id  letable
        mid (CCLetFuns ids closures) = ILClosures ids closures

        frs :: Insn' C O -> BlockEntry
        frs (CCLabel be) = be

        fin :: Insn' O C -> ILLast
        fin (CCLast il) = il

showILProgramStructure :: ILProgram -> Output
showILProgramStructure (ILProgram procdefs _decls _dtypes _lines) =
    concatMap showProcStructure procdefs
  where
    showProcStructure proc =
        out (show $ procIdent proc) ++ (out " // ")
            ++ (out $ show $ map procVarDesc (procVars proc))
            ++ (out " ==> ") ++ (out $ show $ procReturnType proc)
          ++ out "\n" ++ concatMap showBlock (procBlocks proc)
          ++ out "\n^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    procVarDesc (TypedId ty id) = "( " ++ (show id) ++ " :: " ++ show ty ++ " ) "

    showBlock (Block blockid mids last) =
           out (show blockid ++ "\n")
        ++ out (concatMap (\m -> "\t" ++ show m ++ "\n") mids)
        ++ out (show last ++ "\n\n")

