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

import Data.Map(Map)
import qualified Data.Map as Map(singleton, insertWith, lookup, empty, fromList,
                                                         union, findWithDefault)

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
data ILProgram = ILProgram [ILProcDef]
                           [MoExternDecl]
                           [DataType MonoType]
                           SourceLines

data ILExternDecl = ILDecl String MonoType deriving (Show)
type ILProcDef = (Proc [ILBlock], NumPredsMap)
type NumPredsMap = Map BlockId Int

-- The standard definition of a basic block and its parts.
-- This is equivalent to MinCaml's make_closure ...
data ILBlock  = Block BlockEntry [ILMiddle] ILLast
data ILMiddle = ILLetVal      Ident    Letable
              | ILClosures    [Ident] [Closure]
              deriving Show

-- Drop call-as-a-terminator and implicitly re-allow it as a letable value,
-- which better matches LLVM's IR. (If/when we support exception handling,
-- note that a possibly-exception-raising call remains a block terminator!)
data ILLast = ILRetVoid
            | ILRet      MoVar
            | ILBr       BlockId [MoVar]
            | ILCase     MoVar [(CtorId, BlockId)] (Maybe BlockId) (Occurrence MonoType)

--------------------------------------------------------------------

prepForCodegen :: ModuleIL CCBody MonoType -> ILProgram
prepForCodegen m =
    let decls = map (\(s,t) -> MoExternDecl s t) (moduleILdecls m) in
    let dts = moduleILprimTypes m ++ moduleILdataTypes m in
    let procs = map deHooplize (flatten $ moduleILbody m) in
    ILProgram procs decls dts (moduleILsourceLines m)

flatten :: CCBody -> [CCProc]
flatten (CCB_Procs procs _) = procs

deHooplize :: Proc BasicBlockGraph' -> ILProcDef
deHooplize p =
  let (cfgBlocks , numPreds) = flattenGraph (procBlocks p) in
  ( p { procBlocks = cfgBlocks } , numPreds )

computeNumPredecessors elab blocks =
  -- The entry (i.e. postalloca) label will get an incoming edge in LLVM
  let startingMap = Map.singleton (blockId elab) 1 in
  foldr (\b m -> incrPredecessorsDueTo (lastNode b) m)
        startingMap blocks
 where
    incrPredecessorsDueTo :: Insn' O C -> NumPredsMap -> NumPredsMap
    incrPredecessorsDueTo insn' m =
        foldr (\tgt mm -> Map.insertWith (+) tgt 1 mm) m (block'TargetsOf insn')

flattenGraph :: BasicBlockGraph' -> ( [ILBlock] , NumPredsMap )
flattenGraph bbgp =
   let elab = bbgpEntry bbgp in
   let retk = bbgpRetK bbgp in
   let jumpTo bg = case bbgpEntry bg of (bid, _) -> CCLast $ CCCont bid [] in
   let hblocks = preorder_dfs $ mkLast (jumpTo bbgp) |*><*| bbgpBody bbgp in

   -- Because we do a depth-first search, "renaming" blocks are guaranteed
   -- to be adjacent to each other in the list.
   let numPreds  = computeNumPredecessors elab hblocks in
   let hblocks'  = mergeCallNamingBlocks hblocks numPreds in
   let numPreds' = computeNumPredecessors elab hblocks' in
   let ilblocks  = map (deHooplizeBlock retk) hblocks' in
   (ilblocks , numPreds' )

deHooplizeBlock :: BlockId -> Block Insn' C C -> ILBlock
deHooplizeBlock retk b =
         let (f, ms, l) = blockSplit b in
         let (lastmids, last) = fin l in
         Block (frs f) (map mid (blockToList ms) ++ lastmids) last
  where mid :: Insn' O O -> ILMiddle
        mid (CCLetVal id letable)    = ILLetVal   id  letable
        mid (CCLetFuns ids closures) = ILClosures ids closures

        frs :: Insn' C O -> BlockEntry
        frs (CCLabel be) = be

        fin :: Insn' O C -> ([ILMiddle], ILLast)
        fin (CCLast (CCCont k vs)       ) = ([], cont k vs)
        fin (CCLast (CCCase v bs mb occ)) = ([], ILCase v bs mb occ)
        -- [[f k vs]] ==> let x = f vs in [[k x]]
        fin (CCLast (CCCall k t id v vs)) = ([ILLetVal id (ILCall t v vs)]
                                            , cont k [TypedId t id] )
        -- Translate continuation application to br or ret, as appropriate.
        cont k vs =
           case (k == retk, vs) of
                (True,  [] ) -> ILRetVoid
                (True,  [v]) -> ILRet   v
                (True,   _ ) -> error $ "ILExpr.hs:No support for multiple return values yet\n" ++ show vs
                (False,  _ ) -> ILBr k vs

-- This little bit of unpleasantness is needed to ensure that we
-- don't need to create gcroot slots for the phi nodes corresponding
-- to blocks inserted from using CPS-like calls.
-- TODO we can probably do this as a Block->Block translation...
mergeCallNamingBlocks :: [Block' ] -> NumPredsMap -> [ Block' ]
mergeCallNamingBlocks blocks numpreds = go Map.empty [] blocks
  where go !subst !acc !blocks =
         case blocks of
           [] -> finalize acc subst
           [b] -> go subst (b:acc) []
           (x:y:zs) ->
              case mergeAdjacent subst (blockSplitTail x)
                                       (blockSplitHead y) of
                Just (m,s) -> go s        acc  (m:zs)
                Nothing    -> go subst (x:acc) (y:zs)
        mergeAdjacent :: Map MoVar MoVar -> (Block Insn' C O, Insn' O C)
                                         -> (Insn' C O, Block Insn' O C)
                                         -> Maybe (Block Insn' C C, Map MoVar MoVar)
        mergeAdjacent subst (xem, xl) (CCLabel (yb,yargs), yml) =
          case (yargs, xl) of
            ([yarg], CCLast (CCCall cb t _id v vs)) | cb == yb ->
                if Map.lookup yb numpreds == Just 1
                    then Just ((xem `blockSnoc`
                                 (CCLetVal (tidIdent yarg) (ILCall t v vs)))
                                    `blockAppend` yml, subst)
                    else Nothing
            (_, CCLast (CCCont cb   avs))          | cb == yb ->
                if Map.lookup yb numpreds == Just 1
                    then case (length yargs == length avs, yb) of
                           (True, _) ->
                             let subst' = Map.union subst (Map.fromList $ zip yargs avs) in
                             Just ((xem `blockAppend` yml), subst' )
                           (False, ("postalloca",_)) ->
                             Nothing
                           (False, _) ->
                             error $ "Continuation application not passing same # of arguments "
                                  ++ "as expected by the continuation!\n"
                                  ++ show avs ++ "\n" ++ show yargs
                                  ++ "\n" ++ show cb ++ " // " ++ show yb
                    else Nothing
            _ -> Nothing

        finalize revblocks subst =
            let s v = Map.findWithDefault v v subst in
            map (mapBlock' $ substIn s) (reverse revblocks)

        substIn :: VarSubstFor (Insn' e x)
        substIn s insn  = case insn of
             (CCLabel   {}        ) -> insn
             (CCLetVal  id letable) -> CCLetVal id $ substVarsInLetable s letable
             (CCLetFuns ids fns   ) -> CCLetFuns ids $ map (substForInClo s) fns
             (CCLast    cclast    ) -> case cclast of
                 (CCCont b vs)        -> CCLast (CCCont b (map s vs))
                 (CCCall b t id v vs) -> CCLast (CCCall b t id (s v) (map s vs))
                 (CCCase v cs mb occ) -> CCLast (CCCase (s v) cs mb occ)

        substForInClo :: VarSubstFor Closure
        substForInClo s clo =
          clo { closureCaptures = (map s (closureCaptures clo)) }

type VarSubstFor a = (MoVar -> MoVar) -> a -> a

--------------------------------------------------------------------

showILProgramStructure :: ILProgram -> Output
showILProgramStructure (ILProgram procdefs _decls _dtypes _lines) =
    concatMap showProcStructure procdefs
  where
    showProcStructure (proc, _) =
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

instance Show ILLast where
  show (ILRetVoid     ) = "ret void"
  show (ILRet v       ) = "ret " ++ show v
  show (ILBr  bid args) = "br " ++ show bid ++ " , " ++ show args
  show (ILCase v _arms _def _occ) = "case(" ++ show v ++ ")"

