-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufIL (
  dumpModuleToProtobufIL
) where

import Foster.Base
import Foster.ILExpr
import Foster.TypeIL
import Foster.PatternMatch
import Foster.ProtobufUtils

import qualified Data.ByteString.Lazy as L(writeFile)
import Data.Sequence as Seq(fromList)

import Text.ProtocolBuffers(messagePut)

import Foster.Bepb.ProcType as ProcType
import Foster.Bepb.Type.Tag as PbTypeTag
import Foster.Bepb.Type     as PbType
import Foster.Bepb.Closure  as Closure
import Foster.Bepb.Proc     as Proc
import Foster.Bepb.Decl     as Decl
import Foster.Bepb.PBIf     as PBIf
import Foster.Bepb.PBInt    as PBInt
import Foster.Bepb.Expr     as PbExpr
import Foster.Bepb.PbCtorId as PbCtorId
import Foster.Bepb.AllocInfo as PbAllocInfo
import Foster.Bepb.PbOccurrence as PbOccurrence
import Foster.Bepb.DecisionTree as PbDecisionTree
import Foster.Bepb.PbSwitchCase as PbSwitchCase
import Foster.Bepb.CoroPrim as PbCoroPrim
import Foster.Bepb.Module   as Module
import Foster.Bepb.Expr.Tag
import Foster.Bepb.Proc.Linkage
import Foster.Bepb.DecisionTree.Tag
import Foster.Bepb.AllocInfo.MemRegion

import qualified Text.ProtocolBuffers.Header as P'

-----------------------------------------------------------------------

dumpIdent :: Ident -> P'.Utf8
dumpIdent (GlobalSymbol name) = u8fromString name
dumpIdent i@(Ident name num) = if num < 0
                --then u8fromString $ name
                then error $ "cannot dump negative ident! " ++ show i
                else u8fromString $ show i

-----------------------------------------------------------------------

tagProcOrFunc FT_Proc = PbTypeTag.PROC
tagProcOrFunc FT_Func = PbTypeTag.CLOSURE

dumpType :: TypeIL -> PbType.Type
dumpType (NamedTypeIL s)     = P'.defaultValue { PbType.tag  = PbTypeTag.LLVM_NAMED
                                                , PbType.name = Just $ u8fromString s }
dumpType (TupleTypeIL types) = P'.defaultValue { PbType.tag  = PbTypeTag.TUPLE
                                                ,  type_parts = fromList $ fmap dumpType types }
dumpType x@(FnTypeIL s t cc cs) =
                                P'.defaultValue { PbType.tag  = tagProcOrFunc cs
                                                , PbType.procty = Just $ dumpProcType (s, t, cc)
                                                }
dumpType x@(CoroTypeIL a b)     = P'.defaultValue { PbType.tag  = PbTypeTag.CORO
                                                ,  type_parts = fromList $ fmap dumpType [a,b] }

dumpType x@(ForAllIL tyvars ty) = let tyVarName tv = case tv of
                                                    BoundTyVar nm -> u8fromString nm
                                                    SkolemTyVar s u -> error $ "dumpType (Forall ...) saw skolem var " ++ s
                                in
                                P'.defaultValue { PbType.tag  = PbTypeTag.FORALL_TY
                                                ,  type_parts = fromList $ fmap dumpType [ty]
                                                , tyvar_names = fromList $ fmap tyVarName tyvars }

dumpType x@(TyVarIL (BoundTyVar s)) =
                                P'.defaultValue { PbType.tag  = PbTypeTag.TYPE_VARIABLE
                                                , PbType.name = Just $ u8fromString s
                                                }
dumpType x@(PtrTypeIL ty) =    P'.defaultValue { PbType.tag = PbTypeTag.PTR
                                                , type_parts = fromList $ fmap dumpType [ty]
                                                }
dumpType x@(ArrayTypeIL ty) =     P'.defaultValue { PbType.tag = PbTypeTag.ARRAY
                                                , type_parts = fromList $ fmap dumpType [ty]
                                                }
dumpType other = error $ "dumpType saw unknown type " ++ show other

dumpProcType (s, t, cc) =
    let args = case s of
                TupleTypeIL types -> [dumpType x | x <- types]
                otherwise         -> [dumpType s]
    in
    ProcType.ProcType {
          arg_types = fromList args
        , ProcType.ret_type  = dumpType t
        , calling_convention = Just $ u8fromString (stringOfCC cc)
    }
      where stringOfCC FastCC = "fastcc"
            stringOfCC CCC    = "ccc"

-----------------------------------------------------------------------
dumpMemRegion :: AllocMemRegion -> Foster.Bepb.AllocInfo.MemRegion.MemRegion
dumpMemRegion amr = case amr of
        MemRegionStack      -> Foster.Bepb.AllocInfo.MemRegion.MEM_REGION_STACK
        MemRegionGlobalHeap -> Foster.Bepb.AllocInfo.MemRegion.MEM_REGION_GLOBAL_HEAP

dumpAllocate :: ILAllocInfo -> PbAllocInfo.AllocInfo
dumpAllocate (ILAllocInfo region maybe_array_size) =
    P'.defaultValue { PbAllocInfo.mem_region = dumpMemRegion region
                    , PbAllocInfo.array_size = fmap (dumpExpr.ILVar) maybe_array_size }
-----------------------------------------------------------------------
dumpCoroPrim coroPrim argty retty =
    P'.defaultValue { PbExpr.tag = coroFnTag coroPrim
                    , PbExpr.coro_prim = Just $ P'.defaultValue    {
                          PbCoroPrim.ret_type = dumpType retty ,
                          PbCoroPrim.arg_type = dumpType argty }
                    }
-----------------------------------------------------------------------

dumpExpr :: ILExpr -> PbExpr.Expr

dumpExpr (ILCall     t base args)
        = dumpCall t (dumpExpr $ ILVar base) args

dumpExpr (ILCallPrim t (ILNamedPrim base) args)
        = dumpCall t (dumpGlobalSymbol base) args

dumpExpr (ILCallPrim t (ILCoroPrim c a r) args)
        = dumpCall t (dumpCoroPrim c a r) args

dumpExpr (ILCallPrim t (ILPrimOp op size) args)
        = dumpCallPrimOp t op size args

dumpExpr x@(ILBool b) =
    P'.defaultValue { bool_value   = Just b
                    , PbExpr.tag   = IL_BOOL
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr (ILVar (TypedId t i)) = dumpILVar t i

dumpExpr x@(ILTuple vs) =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr $ ILVar v | v <- vs]
                    , PbExpr.tag   = IL_TUPLE
                    , PbExpr.type' = Just $ dumpType (typeIL x)
                    , PbExpr.alloc_info = Just $ dumpAllocate
                                (ILAllocInfo MemRegionGlobalHeap Nothing) }

dumpExpr x@(ILAlloc a) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [ILVar a])
                    , PbExpr.tag   = IL_ALLOC
                    , PbExpr.type' = Just $ dumpType (PtrTypeIL $ typeIL (ILVar a))  }

dumpExpr x@(ILAllocArray elt_ty size) =
    P'.defaultValue { PbExpr.parts = fromList []
                    , PbExpr.tag   = IL_MEMALLOC
                    , PbExpr.type' = Just $ dumpType elt_ty
                    , PbExpr.alloc_info = Just $ dumpAllocate
                                (ILAllocInfo MemRegionGlobalHeap (Just size)) }

dumpExpr x@(ILDeref t a) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [ILVar a])
                    , PbExpr.tag   = IL_DEREF
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr x@(ILStore t a b ) =
    P'.defaultValue { PbExpr.parts = fromList (fmap (dumpExpr.ILVar) [a, b])
                    , PbExpr.tag   = IL_STORE
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr x@(ILArrayRead t a b ) =
    P'.defaultValue { PbExpr.parts = fromList (fmap (dumpExpr.ILVar) [a, b])
                    , PbExpr.tag   = IL_ARRAY_READ
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr x@(ILArrayPoke v b i ) =
    P'.defaultValue { PbExpr.parts = fromList (fmap (dumpExpr.ILVar) [v, b, i])
                    , PbExpr.tag   = IL_ARRAY_POKE
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr x@(ILInt ty int) =
    P'.defaultValue { PbExpr.pb_int = Just $ dumpInt (show $ litIntValue int)
                                                     (litIntMinBits int)
                    , PbExpr.tag   = IL_INT
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr x@(ILIf t a b c) =
    P'.defaultValue { pb_if        = Just (dumpIf $ x)
                    , PbExpr.tag   = IL_IF
                    , PbExpr.type' = Just $ dumpType (typeIL x) }

dumpExpr x@(ILUntil t a b) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [a, b])
                    , PbExpr.tag   = IL_UNTIL
                    , PbExpr.type' = Just $ dumpType (typeIL x) }

dumpExpr x@(ILTyApp overallTy baseExpr argType) =
    error $ "Unable to dump type application node " ++ show x
          ++ " (should handle substitution before codegen)."

dumpExpr x@(ILCase t a _bs decisionTree) =
    P'.defaultValue { PbExpr.parts = fromList (fmap (dumpExpr.ILVar) [a])
                    , PbExpr.dt    = Just $ dumpDecisionTree decisionTree
                    , PbExpr.tag   = IL_CASE
                    , PbExpr.type' = Just $ dumpType t }

dumpExpr x@(ILClosures names closures expr) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [expr])
                    , PbExpr.tag   = IL_CLOSURES
                    , PbExpr.closures = fromList (fmap dumpClosureWithName (Prelude.zip names closures))
                    , PbExpr.type' = Just $ dumpType (typeIL expr) }

dumpExpr x@(ILLetVal _ _ inexpr) =
    let (e, nms, vals) = unzipLetVals x in
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr (e:vals))
                    , PbExpr.tag   = IL_LETVALS
                    , PbExpr.names = fromList nms
                    , PbExpr.type' = Just $ dumpType (typeIL inexpr) }

coroFnTag CoroInvoke = IL_CORO_INVOKE
coroFnTag CoroCreate = IL_CORO_CREATE
coroFnTag CoroYield  = IL_CORO_YIELD

unzipLetVals :: ILExpr -> (ILExpr, [P'.Utf8], [ILExpr])
unzipLetVals (ILLetVal x a b) =
        let (e, nms, vals) = unzipLetVals b in
        ( e , (dumpIdent x):nms , a:vals )
unzipLetVals e = (e, [], [])

dumpClosureWithName (varid, ILClosure procid envid captvars) =
    Closure { varname  = dumpIdent varid
            , procid   = u8fromString (identPrefix procid)
            , envid    = dumpIdent envid
            , env      = dumpExpr (ILTuple captvars) }

dumpDecisionTree (DT_Fail) =
    P'.defaultValue { PbDecisionTree.tag = DT_FAIL }

dumpDecisionTree (DT_Leaf expr idsoccs) =
    P'.defaultValue { PbDecisionTree.tag    = DT_LEAF
                    , PbDecisionTree.leaf_idents = fromList $ map (dumpIdent.fst) idsoccs
                    , PbDecisionTree.leaf_idoccs = fromList $ map (dumpOcc  .snd) idsoccs
                    , PbDecisionTree.leaf_action = Just $ dumpExpr expr }

dumpDecisionTree (DT_Swap i dt) = dumpDecisionTree dt

dumpDecisionTree (DT_Switch occ sc) =
    P'.defaultValue { PbDecisionTree.tag    = DT_SWITCH
                    , PbDecisionTree.switchcase = Just $ dumpSwitchCase occ sc }

dumpSwitchCase :: Occurrence -> SwitchCase ILExpr -> PbSwitchCase
dumpSwitchCase occ (SwitchCase ctorDTpairs defaultCase) =
    let (ctors, dts) = Prelude.unzip ctorDTpairs in
    P'.defaultValue { PbSwitchCase.ctors = fromList (map dumpCtorId ctors)
                    , PbSwitchCase.trees = fromList (map dumpDecisionTree dts)
                    , PbSwitchCase.defCase = fmap dumpDecisionTree defaultCase
                    , PbSwitchCase.occ   = Just $ dumpOcc occ }

dumpCtorId (CtorId s i) =
    P'.defaultValue { PbCtorId.ctorTypeName = u8fromString s
                    , PbCtorId.ctorLocalId  = intToInt32 i }

dumpOcc offs =
    P'.defaultValue { PbOccurrence.occ_offset = fromList $ map intToInt32 offs }

-----------------------------------------------------------------------

dumpGlobalSymbol base =
    P'.defaultValue { PbExpr.tag   = IL_GLOBAL_SYMBOL
                    , PbExpr.name  = Just $ dumpIdent (tidIdent base)
                    , PbExpr.type' = Just $ dumpType (tidType  base) }

dumpILVar t i@(GlobalSymbol _) = dumpGlobalSymbol (TypedId t i)
dumpILVar t i =
    P'.defaultValue { PbExpr.name  = Just $ dumpIdent i
                    , PbExpr.tag   = IL_VAR
                    , PbExpr.type' = Just $ dumpType t  }

dumpCall t base args =
    P'.defaultValue { PbExpr.parts = fromList $ base:(fmap (dumpExpr.ILVar) args)
                    , PbExpr.tag   = IL_CALL
                    , PbExpr.type' = Just $ dumpType t }

dumpCallPrimOp t op size args =
    P'.defaultValue { PbExpr.parts = fromList $ fmap (dumpExpr.ILVar) args
                    , PbExpr.tag   = IL_CALL_PRIMOP
                    , PbExpr.name         = Just $ u8fromString op
                    , PbExpr.prim_op_size = Just $ intToInt32 size
                    , PbExpr.type' = Just $ dumpType t }

dumpIf x@(ILIf t v b c) =
        PBIf { test_expr = dumpExpr (ILVar v)
             , then_expr = dumpExpr b
             , else_expr = dumpExpr c }
dumpIf other = error $ "dumpIf called with non-ILIf node: " ++ show other

dumpInt cleanText activeBits =
        PBInt.PBInt { clean = u8fromString cleanText
                    , bits  = intToInt32   activeBits }

dumpProc p =
    Proc { Proc.name  = dumpIdent (ilProcIdent p)
         , in_args    = fromList $ [dumpIdent (tidIdent v) | v <- (ilProcVars p)]
         , proctype   = dumpProcType (preProcType p)
         , Proc.body  = Just $ dumpExpr (ilProcBody p)
         , Proc.lines = Just $ u8fromString (showSourceRange $ ilProcRange p)
         , Proc.linkage = Foster.Bepb.Proc.Linkage.Internal
         }

-----------------------------------------------------------------------

dumpDecl (ILDecl s t) =
    Decl { Decl.name  = u8fromString s
         , Decl.type' = dumpType t
         }

dumpProgramToModule :: ILProgram -> Module
dumpProgramToModule (ILProgram procdefs decls (SourceLines lines)) =
    Module   { modulename = u8fromString $ "foo"
             , procs      = fromList [dumpProc p | p <- procdefs]
             , decls      = fromList [dumpDecl d | d <- decls]
             , modlines   = fmap textToPUtf8 lines
             }

dumpModuleToProtobufIL :: ILProgram -> FilePath -> IO ()
dumpModuleToProtobufIL mod outpath = do
    let llmod = dumpProgramToModule mod
    L.writeFile outpath (messagePut llmod)
    return ()

