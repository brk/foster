-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufIL (
  dumpMonoModuleToProtobuf
) where

import Foster.Base
import Foster.MonoExpr
import Foster.MonoType
import Foster.MonoLetable
import Foster.PatternMatch
import Foster.ProtobufUtils

import qualified Data.ByteString.Lazy as L(writeFile)
import Data.Sequence as Seq(fromList)
import Data.Map as Map(elems)

import Text.ProtocolBuffers(messagePut)

import Foster.Bepb.ProcType     as ProcType
import Foster.Bepb.Type.Tag     as PbTypeTag
import Foster.Bepb.Type         as PbType
import Foster.Bepb.Closure      as Closure
import Foster.Bepb.Proc         as Proc
import Foster.Bepb.Decl         as Decl
import Foster.Bepb.PBInt        as PBInt
import qualified Foster.Bepb.Block        as PbBlock
import Foster.Bepb.LetVal       as PbLetVal
import qualified Foster.Bepb.Letable      as PbLetable
import Foster.Bepb.Terminator   as PbTerminator
import Foster.Bepb.BlockMiddle  as PbBlockMiddle
import Foster.Bepb.LetClosures  as PbLetClosures
import Foster.Bepb.TermVar      as PbTermVar
import Foster.Bepb.PbCtorId     as PbCtorId
import Foster.Bepb.RebindId     as PbRebindId
import Foster.Bepb.PbDataCtor   as PbDataCtor
import Foster.Bepb.PbAllocInfo  as PbAllocInfo
import Foster.Bepb.PbOccurrence as PbOccurrence
import Foster.Bepb.DecisionTree as PbDecisionTree
import Foster.Bepb.PbSwitchCase as PbSwitchCase
import Foster.Bepb.PbCoroPrim   as PbCoroPrim
import Foster.Bepb.Module       as Module
import Foster.Bepb.Letable.Tag
import Foster.Bepb.PbCoroPrim.Tag
import Foster.Bepb.TermVar.Tag
import Foster.Bepb.Terminator.Tag
import Foster.Bepb.Proc.Linkage
import Foster.Bepb.DecisionTree.Tag
import Foster.Bepb.PbAllocInfo.MemRegion as PbMemRegion

import qualified Text.ProtocolBuffers.Header as P'
import qualified Data.Text as T

-----------------------------------------------------------------------

dumpBlockId (str, lab) = u8fromString (str ++ "." ++ show lab)

dumpIdent :: Ident -> P'.Utf8
dumpIdent (GlobalSymbol name) = textToPUtf8 name
dumpIdent i@(Ident _name num) = if num < 0
                --then u8fromString $ name
                then error $ "cannot dump negative ident! " ++ show i
                else u8fromString $ show i

mayTriggerGC :: TypedId t -> Bool
mayTriggerGC (TypedId _ (GlobalSymbol name)) = globalMayGC name
  where globalMayGC name = not $ name `Prelude.elem` (map T.pack
                        ["expect_i1", "print_i1"
                        ,"expect_i64" , "print_i64" , "expect_i32", "print_i32"
                        ,"expect_i32b", "print_i32b"])
mayTriggerGC _ = True

-----------------------------------------------------------------------

tagProcOrFunc FT_Proc = PbTypeTag.PROC
tagProcOrFunc FT_Func = PbTypeTag.CLOSURE

intOfSize I1 = 1
intOfSize I8 = 8
intOfSize I32 = 32
intOfSize I64 = 64

dumpUnknownType () =
  P'.defaultValue { PbType.tag = PbTypeTag.PTR
                  , type_parts = fromList $ [dumpIntType 999]
                  }

dumpIntType sizeBits = P'.defaultValue { PbType.tag  = PbTypeTag.PRIM_INT
                                       , PbType.carray_size = Just sizeBits }

dumpType :: MonoType -> PbType.Type
dumpType (PtrTypeUnknown)  = dumpUnknownType ()
dumpType (PrimInt size)    = dumpIntType (intOfSize size)
dumpType (TyConApp nm _tys)= P'.defaultValue { PbType.tag  = PbTypeTag.NAMED
                                             , PbType.name = Just $ u8fromString nm
                                             }
dumpType (TupleType types) = P'.defaultValue { PbType.tag  = PbTypeTag.TUPLE
                                             ,  type_parts = fromList $ fmap dumpType types }
dumpType (FnType s t cc cs) = P'.defaultValue { PbType.tag = tagProcOrFunc cs
                                              , PbType.procty = Just $ dumpProcType (s, t, cc)
                                              }
dumpType (CoroType a b)     = P'.defaultValue { PbType.tag  = PbTypeTag.CORO
                                              ,  type_parts = fromList $ fmap dumpType [a,b] }

dumpType (PtrType ty) =    P'.defaultValue { PbType.tag = PbTypeTag.PTR
                                           , type_parts = fromList $ fmap dumpType [ty]
                                           }
dumpType (ArrayType ty) =  P'.defaultValue { PbType.tag = PbTypeTag.ARRAY
                                           , type_parts = fromList $ fmap dumpType [ty]
                                           }

dumpProcType (s, t, cc) =
    let args = case s of
                TupleType types -> [dumpType x | x <- types]
                _else           -> [dumpType s]
    in
    ProcType.ProcType {
          arg_types = fromList args
        , ProcType.ret_type  = dumpType t
        , calling_convention = Just $ u8fromString (stringOfCC cc)
    }
      where stringOfCC FastCC = "fastcc"
            stringOfCC CCC    = "ccc"

dumpDataCtor (DataCtor ctorName _smallId types) =
  PbDataCtor { PbDataCtor.name  = textToPUtf8 ctorName
             , PbDataCtor.type' = fromList $ map dumpType types
             }

dumpDataType name ctors =
    P'.defaultValue { PbType.tag  = PbTypeTag.DATATYPE
                    , PbType.name = Just $ u8fromString name
                    , PbType.ctor = fromList $ fmap dumpDataCtor ctors
                    }

-----------------------------------------------------------------------
dumpMemRegion :: AllocMemRegion -> PbMemRegion.MemRegion
dumpMemRegion amr = case amr of
    MemRegionStack      -> PbMemRegion.MEM_REGION_STACK
    MemRegionGlobalHeap -> PbMemRegion.MEM_REGION_GLOBAL_HEAP

dumpAllocate :: AllocInfo MonoType -> PbAllocInfo
dumpAllocate (AllocInfo _typ region maybe_array_size unboxed) =
    P'.defaultValue { PbAllocInfo.mem_region = dumpMemRegion region
                    , PbAllocInfo.array_size = fmap dumpVar maybe_array_size
                    , PbAllocInfo.unboxed    = unboxed }
-----------------------------------------------------------------------

dumpBlock :: MoBlock -> PbBlock.Block
dumpBlock (MoBlock id mids illast) =
    P'.defaultValue { PbBlock.block_id = dumpBlockId id
                    , PbBlock.middle   = fromList $ map dumpMiddle mids
                    , PbBlock.last     = dumpLast illast
                    }

dumpMiddle :: MoMiddle -> PbBlockMiddle.BlockMiddle
dumpMiddle (MoLetVal id letable) =
    P'.defaultValue { let_val = Just (dumpLetVal id letable)
                    , let_clo = Nothing
                    }

dumpMiddle (MoClosures ids clos) =
    P'.defaultValue { let_val = Nothing
                    , let_clo = Just (dumpLetClosures ids clos)
                    }

dumpMiddle (MoRebindId from to) =
    P'.defaultValue { let_val = Nothing
                    , let_clo = Nothing
                    , rebind = Just $
            P'.defaultValue { from_id = dumpIdent from
                            , to_var  = dumpVar to
                            }
                    }

dumpLetVal :: Ident -> MonoLetable -> PbLetVal.LetVal
dumpLetVal id letable =
    P'.defaultValue { let_val_id = dumpIdent id
                    , let_expr   = dumpExpr letable
                    }

dumpLetClosures :: [Ident] -> [MoClosure] -> PbLetClosures.LetClosures
dumpLetClosures ids clos =
    P'.defaultValue { closures = fromList $ fmap dumpClosureWithName $
                                                       (Prelude.zip ids clos)
                    }

dumpLast :: MoLast -> PbTerminator.Terminator
dumpLast MoRetVoid =
    P'.defaultValue { PbTerminator.tag    = BLOCK_RET_VOID }
dumpLast (MoRet var) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_RET_VAL
                    , PbTerminator.var    = Just $ dumpVar var }
dumpLast (MoBr blockid) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_BR
                    , PbTerminator.block  = Just $ dumpBlockId blockid }
dumpLast (MoIf _ var thenid elseid) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_IF
                    , PbTerminator.var    = Just $ dumpVar var
                    , PbTerminator.block  = Just $ dumpBlockId thenid
                    , PbTerminator.block2 = Just $ dumpBlockId elseid }
dumpLast (MoCase ty var dt) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_CASE
                    , PbTerminator.var    = Just $ dumpVar var
                    , PbTerminator.typ    = Just $ dumpType ty
                    , PbTerminator.dt     = Just $ dumpDecisionTree dt }

-----------------------------------------------------------------------

dumpVar (TypedId t i) = dumpMoVar t i

-----------------------------------------------------------------------

dumpExpr :: MonoLetable -> PbLetable.Letable

dumpExpr (MoCall t base args)
        = dumpCall t (dumpVar base)          args (mayTriggerGC base)

dumpExpr (MoCallPrim t (NamedPrim base) args)
        = dumpCall t (dumpGlobalSymbol base) args (mayTriggerGC base)

dumpExpr (MoCallPrim t (PrimOp op size) args)
        = dumpCallPrimOp t op size args

dumpExpr (MoCallPrim t (CoroPrim coroPrim argty retty) args)
        = dumpCallCoroOp t coroPrim argty retty args True

dumpExpr (MoAppCtor t cid args)
        = dumpAppCtor t cid args

dumpExpr x@(MoBool b) =
    P'.defaultValue { PbLetable.bool_value = Just b
                    , PbLetable.tag   = IL_BOOL
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoTuple vs) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar v | v <- vs]
                    , PbLetable.tag   = IL_TUPLE
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.alloc_info = Just $ dumpAllocate
                         (AllocInfo (typeMo x) MemRegionGlobalHeap Nothing True) }

dumpExpr x@(MoAllocate info) =
    P'.defaultValue { PbLetable.tag   = IL_ALLOCATE
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.alloc_info = Just $ dumpAllocate info }

dumpExpr x@(MoAlloc a) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar a]
                    , PbLetable.tag   = IL_ALLOC
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr  (MoAllocArray elt_ty size) =
    P'.defaultValue { PbLetable.parts = fromList []
                    , PbLetable.tag   = IL_ALLOCATE
                    , PbLetable.type' = Just $ dumpType elt_ty
                    , PbLetable.alloc_info = Just $ dumpAllocate
                       (AllocInfo elt_ty MemRegionGlobalHeap (Just size) True) }

dumpExpr x@(MoDeref a) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar a]
                    , PbLetable.tag   = IL_DEREF
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoStore a b) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [a, b])
                    , PbLetable.tag   = IL_STORE
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoArrayRead _t a b ) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [a, b])
                    , PbLetable.tag   = IL_ARRAY_READ
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoArrayPoke v b i ) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [v, b, i])
                    , PbLetable.tag   = IL_ARRAY_POKE
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoInt _ty int) =
    P'.defaultValue { PbLetable.pb_int = Just $ dumpInt (show $ litIntValue int)
                                                     (litIntMinBits int)
                    , PbLetable.tag   = IL_INT
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpClosureWithName (varid, MoClosure procid envid captvars) =
    Closure { varname  = dumpIdent varid
            , proc_id  = textToPUtf8 (identPrefix procid)
            , env_id   = dumpIdent envid
            , env      = dumpExpr (MoTuple captvars) }

dumpDecisionTree (DT_Fail) =
    P'.defaultValue { PbDecisionTree.tag = DT_FAIL }

dumpDecisionTree (DT_Leaf block_id idsoccs) =
    P'.defaultValue { PbDecisionTree.tag    = DT_LEAF
                    , PbDecisionTree.leaf_idents = fromList $ map (dumpIdent.fst) idsoccs
                    , PbDecisionTree.leaf_idoccs = fromList $ map (dumpOcc  .snd) idsoccs
                    , PbDecisionTree.leaf_action = Just $ dumpBlockId block_id }

dumpDecisionTree (DT_Switch occ idsdts md) =
    P'.defaultValue { PbDecisionTree.tag    = DT_SWITCH
                    , PbDecisionTree.switchcase = Just $ dumpSwitchCase occ idsdts md }

dumpSwitchCase occ ctorDTpairs defaultCase =
    let (ctors, dts) = Prelude.unzip ctorDTpairs in
    P'.defaultValue { PbSwitchCase.ctors = fromList (map dumpCtorId ctors)
                    , PbSwitchCase.trees = fromList (map dumpDecisionTree dts)
                    , PbSwitchCase.defCase = fmap dumpDecisionTree defaultCase
                    , PbSwitchCase.occ   = Just $ dumpOcc occ }

dumpCtorId (CtorId s n _a i) =
    P'.defaultValue { PbCtorId.ctor_type_name = u8fromString s
                    , PbCtorId.ctor_ctor_name = u8fromString n
                    , PbCtorId.ctor_local_id  = intToInt32 i }

dumpOcc offsCtorIds =
    let (offs, ids) = unzip offsCtorIds in
    P'.defaultValue { PbOccurrence.occ_offset = fromList $ map intToInt32 offs
                    , PbOccurrence.occ_ctorid = fromList $ map dumpCtorId ids }

-----------------------------------------------------------------------

dumpGlobalSymbol base =
    P'.defaultValue { PbTermVar.tag   = IL_GLOBAL_SYMBOL
                    , PbTermVar.name  = dumpIdent (tidIdent base)
                    , PbTermVar.typ   = Just $ dumpType (tidType  base) }

dumpMoVar t i@(GlobalSymbol _) = dumpGlobalSymbol (TypedId t i)
dumpMoVar t i =
    P'.defaultValue { PbTermVar.tag  = IL_VAR
                    , PbTermVar.name = dumpIdent i
                    , PbTermVar.typ  = Just $ dumpType t  }

-----------------------------------------------------------------------

dumpCallCoroOp t coroPrim argty retty args mayGC =
    P'.defaultValue { PbLetable.tag   = IL_CALL
                    , PbLetable.parts = fromList $ fmap dumpVar args
                    , PbLetable.type' = Just $ dumpType t
                    , PbLetable.call_may_trigger_gc = Just $ mayGC
                    , PbLetable.coro_prim = Just $ P'.defaultValue    {
                          PbCoroPrim.tag = coroFnTag coroPrim  ,
                          PbCoroPrim.ret_type = dumpType retty ,
                          PbCoroPrim.arg_type = dumpType argty }
                    }
    where
        coroFnTag CoroInvoke = IL_CORO_INVOKE
        coroFnTag CoroCreate = IL_CORO_CREATE
        coroFnTag CoroYield  = IL_CORO_YIELD

dumpCall :: MonoType -> TermVar -> [TypedId MonoType] -> Bool -> PbLetable.Letable
dumpCall t base args mayGC =
    P'.defaultValue { PbLetable.tag   = IL_CALL
                    , PbLetable.parts = fromList $ base:(fmap dumpVar args)
                    , PbLetable.type' = Just $ dumpType t
                    , PbLetable.call_may_trigger_gc = Just $ mayGC }

dumpCallPrimOp t op size args =
    P'.defaultValue { PbLetable.parts = fromList $ fmap dumpVar args
                    , PbLetable.tag   = IL_CALL_PRIMOP
                    , PbLetable.prim_op_name = Just $ u8fromString op
                    , PbLetable.prim_op_size = Just $ intToInt32 size
                    , PbLetable.type' = Just $ dumpType t }

dumpAppCtor t cid args =
    P'.defaultValue { PbLetable.parts   = fromList $ fmap dumpVar args
                    , PbLetable.tag     = IL_CTOR
                    , PbLetable.ctor_id = Just $ dumpCtorId cid
                    , PbLetable.type'   = Just $ dumpType t }

dumpInt cleanText activeBits =
        PBInt.PBInt { clean = u8fromString cleanText
                    , bits  = intToInt32   activeBits }

dumpProc p =
    Proc { Proc.name  = dumpIdent $ moProcIdent p
         , in_args    = fromList $ [dumpIdent (tidIdent v) | v <- moProcVars p]
         , proctype   = dumpProcType (preProcType p)
         , Proc.blocks= fromList $ map dumpBlock (moProcBlocks p)
         , Proc.lines = Just $ u8fromString (showSourceRange $ moProcRange p)
         , Proc.linkage = Foster.Bepb.Proc.Linkage.Internal
         }
  where
        preProcType proc =
            let retty = moProcReturnType proc in
            let argtys = TupleType (map tidType (moProcVars proc)) in
            (argtys, retty, FastCC)

-----------------------------------------------------------------------

dumpDataTypeDecl datatype =
    let name = dataTypeName datatype in
    Decl { Decl.name  = u8fromString name
         , Decl.type' = dumpDataType name (dataTypeCtors datatype)
         }

dumpDecl (MoDecl s t) =
    Decl { Decl.name  = u8fromString s
         , Decl.type' = dumpType t
         }

dumpProgramToModule :: MonoProgram -> Module
dumpProgramToModule (MoProgram procdefs decls datatypes (SourceLines lines)) =
    Module   { modulename = u8fromString $ "foo"
             , procs      = fromList [dumpProc p | p <- Map.elems procdefs]
             , val_decls  = fromList (map dumpDecl decls)
             , typ_decls  = fromList (map dumpDataTypeDecl datatypes)
             , modlines   = fmap textToPUtf8 lines
             }

dumpMonoModuleToProtobuf :: MonoProgram -> FilePath -> IO ()
dumpMonoModuleToProtobuf mod outpath = do
    let llmod = dumpProgramToModule mod
    L.writeFile outpath (messagePut llmod)
    return ()

-----------------------------------------------------------------------

typeMo expr = case expr of
    MoBool _                -> PrimInt I1
    MoInt t _               -> t
    MoTuple vs              -> TupleType (map tidType vs)
    MoCall     t  _ _       -> t
    MoCallPrim t  _ _       -> t
    MoAppCtor  t  _ _       -> t
    MoAllocate info         -> allocType info
    MoAllocArray elt_ty _   -> ArrayType elt_ty
    MoAlloc v               -> PtrType (tidType v)
    MoDeref v               -> pointedToTypeOfVar v
    MoStore _ _             -> TupleType []
    MoArrayRead t _ _       -> t
    MoArrayPoke _ _ _       -> TupleType []

pointedToTypeOfVar v = case v of
    TypedId (PtrType t) _ -> t
    _ -> error $ "ProtobufIL.hs:pointedToTypeOfVar\n"
              ++ "Expected variable to be a pointer, but had " ++ show v
