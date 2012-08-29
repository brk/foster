-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufIL (
  dumpILProgramToProtobuf
) where

import Foster.Base
import Foster.ILExpr
import qualified Foster.CloConv as CC(Proc(..), Closure(Closure))
import Foster.MonoType
import Foster.Letable
import Foster.ProtobufUtils

import qualified Data.ByteString.Lazy as L(writeFile)
import Data.Sequence as Seq(fromList)
import Data.Map as Map(lookup)

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
import Foster.Bepb.PbCtorInfo   as PbCtorInfo
import Foster.Bepb.PbAllocInfo  as PbAllocInfo
import Foster.Bepb.PbOccurrence as PbOccurrence
import Foster.Bepb.PbSwitch     as PbSwitch
import Foster.Bepb.PbCoroPrim   as PbCoroPrim
import Foster.Bepb.Module       as Module
import Foster.Bepb.RootInit     as PbRootInit
import Foster.Bepb.TupleStore   as PbTupleStore
import Foster.Bepb.Letable.Tag
import Foster.Bepb.PbCoroPrim.Tag
import Foster.Bepb.TermVar.Tag
import Foster.Bepb.Terminator.Tag
import Foster.Bepb.Proc.Linkage
import Foster.Bepb.PbAllocInfo.MemRegion as PbMemRegion

import qualified Text.ProtocolBuffers.Header as P'
import qualified Data.Text as T

-----------------------------------------------------------------------

stringSG SG_Static  = u8fromString "static"
stringSG SG_Dynamic = u8fromString "dynamic"

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

-- |||||||||||||||||||||||||||| Types |||||||||||||||||||||||||||{{{

dumpUnknownType () =
  P'.defaultValue { PbType.tag = PbTypeTag.PTR
                  , type_parts = fromList $ [dumpIntType 999]
                  }

dumpIntType sizeBits = P'.defaultValue { PbType.tag  = PbTypeTag.PRIM_INT
                                       , PbType.carray_size = Just sizeBits }

dumpType :: MonoType -> PbType.Type
dumpType (PtrTypeUnknown)  = dumpUnknownType ()
dumpType (PrimInt size)    = dumpIntType (intOfSize size)
dumpType (PrimFloat64)     =
              P'.defaultValue { PbType.tag  = PbTypeTag.FLOAT64 }
dumpType (TyConApp nm _tys)=
              P'.defaultValue { PbType.tag  = PbTypeTag.NAMED
                              , PbType.name = Just $ u8fromString nm }
dumpType (StructType types) =
              P'.defaultValue { PbType.tag  = PbTypeTag.STRUCT
                              ,  type_parts = fromList $ fmap dumpType types }
dumpType (TupleType types) =
              P'.defaultValue { PbType.tag  = PbTypeTag.TUPLE
                              ,  type_parts = fromList $ fmap dumpType types }
dumpType (CoroType a b) =
              P'.defaultValue { PbType.tag  = PbTypeTag.CORO
                              ,  type_parts = fromList $ fmap dumpType [a,b] }
dumpType (PtrType ty) =
              P'.defaultValue { PbType.tag = PbTypeTag.PTR
                              , type_parts = fromList $ fmap dumpType [ty] }
dumpType (ArrayType ty) =
              P'.defaultValue { PbType.tag = PbTypeTag.ARRAY
                              , type_parts = fromList $ fmap dumpType [ty] }
dumpType (FnType s t cc cs) =
              P'.defaultValue { PbType.tag = tagProcOrFunc cs
                              , PbType.procty = Just $ dumpProcType (s, t, cc) }
dumpProcType (ss, t, cc) =
    ProcType.ProcType {
          arg_types = fromList (map dumpType ss)
        , ProcType.ret_type  = dumpType t
        , calling_convention = Just $ u8fromString (stringOfCC cc)
    }
      where stringOfCC FastCC = "fastcc"
            stringOfCC CCC    = "ccc"

dumpDataCtor (DataCtor ctorName _smallId _tyformals types) =
  PbDataCtor { PbDataCtor.name  = textToPUtf8 ctorName
             , PbDataCtor.type' = fromList $ map dumpType types
             }

dumpDataType name ctors =
    P'.defaultValue { PbType.tag  = PbTypeTag.DATATYPE
                    , PbType.name = Just $ u8fromString name
                    , PbType.ctor = fromList $ fmap dumpDataCtor ctors
                    }

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

dumpMemRegion :: AllocMemRegion -> PbMemRegion.MemRegion
dumpMemRegion amr = case amr of
    MemRegionStack      -> PbMemRegion.MEM_REGION_STACK
    MemRegionGlobalHeap -> PbMemRegion.MEM_REGION_GLOBAL_HEAP

dumpAllocate :: AllocInfo MonoType -> PbAllocInfo
dumpAllocate (AllocInfo typ region typename maybe_tag maybe_array_size allocsite) =
    P'.defaultValue { PbAllocInfo.mem_region = dumpMemRegion region
                    , PbAllocInfo.type'      = dumpType      typ
                    , PbAllocInfo.type_name  = u8fromString  typename
                    , PbAllocInfo.ctor_tag   = fmap intToInt32 maybe_tag
                    , PbAllocInfo.array_size = fmap dumpVar  maybe_array_size
                    , PbAllocInfo.alloc_site = u8fromString  allocsite
                    }

-- ||||||||||||||||||||||||||| CFGs |||||||||||||||||||||||||||||{{{
-- dumpBlock :: Map.Map BlockId (Maybe Int) -> ILBlock -> PbBlock.Block
dumpBlock predmap (Block (id, phis) mids illast) =
    P'.defaultValue { PbBlock.block_id = dumpBlockId id
                    , PbBlock.phis     = fromList $ map dumpVar phis
                    , PbBlock.middle   = fromList $ map dumpMiddle mids
                    , PbBlock.last     = dumpLast illast
                    , PbBlock.num_preds= fmap intToInt32 (Map.lookup id predmap)
                    }

dumpMiddle :: ILMiddle -> PbBlockMiddle.BlockMiddle
dumpMiddle (ILLetVal from (ILBitcast ty (TypedId _ to))) =
    P'.defaultValue { bitcast = Just $ dumpRebinding from (TypedId ty to) }
dumpMiddle (ILLetVal id letable) =
    P'.defaultValue { let_val = Just (dumpLetVal id letable) }
dumpMiddle (ILClosures ids clos) =
    P'.defaultValue { let_clo = Just (dumpLetClosures ids clos) }
dumpMiddle (ILGCRootKill v) =
    P'.defaultValue { gcroot_kill = Just (dumpVar v) }
dumpMiddle (ILGCRootInit src root) =
    P'.defaultValue { gcroot_init = Just $ P'.defaultValue {
           root_init_src  = (dumpVar src)
         , root_init_root = (dumpVar root)
      }
    }
dumpMiddle (ILTupleStore vs v r) =
    P'.defaultValue { tuple_store = Just $
      P'.defaultValue {
              stored_vars = fromList $ map dumpVar vs
            , storage     = dumpVar v
            , storage_indir = case r of
                                MemRegionStack      -> False
                                MemRegionGlobalHeap -> True
     }
   }

dumpRebinding from to = P'.defaultValue { from_id = dumpIdent from
                                        , to_var  = dumpVar to }

dumpLetVal :: Ident -> Letable -> PbLetVal.LetVal
dumpLetVal id letable =
    P'.defaultValue { let_val_id = dumpIdent id
                    , let_expr   = dumpExpr letable
                    }

dumpLetClosures :: [Ident] -> [CC.Closure] -> PbLetClosures.LetClosures
dumpLetClosures ids clos =
    P'.defaultValue { closures = fromList $ fmap dumpClosureWithName $
                                                          (Prelude.zip ids clos)
                    }

dumpLast :: ILLast -> PbTerminator.Terminator
dumpLast ILRetVoid =
    P'.defaultValue { PbTerminator.tag    = BLOCK_RET_VOID }
dumpLast (ILRet var) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_RET_VAL
                    , PbTerminator.var    = Just $ dumpVar var }
dumpLast (ILBr blockid args) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_BR
                    , PbTerminator.block  = Just $ dumpBlockId blockid
                    , PbTerminator.args   = fromList $ map dumpVar args }
dumpLast (ILCase var arms def occ) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_CASE
                    , PbTerminator.scase  = Just $ dumpSwitch var arms def occ }

dumpSwitch var arms def occ =
    let (ctors, ids) = Prelude.unzip arms in
    P'.defaultValue { PbSwitch.ctors   = fromList (map dumpCtorId ctors)
                    , PbSwitch.blocks  = fromList (map dumpBlockId ids)
                    , PbSwitch.defCase = fmap dumpBlockId def
                    , PbSwitch.occ   = Just $ dumpOccurrence var occ }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

tupStruct (TupleType ts) = StructType ts
tupStruct t              = error $ "ProtobufIL:tupStruct expected tuple type,"
                                 ++ " got " ++ show t

-- |||||||||||||||||||||||| Expressions |||||||||||||||||||||||||{{{
dumpExpr :: Letable -> PbLetable.Letable
dumpExpr (ILBitcast _ _) = error "ProtobufIL.hs cannot dump bitcast as expr"
dumpExpr (ILAlloc    {}) = error "ILAlloc should have been translated away!"

dumpExpr x@(ILText s) =
    P'.defaultValue { PbLetable.string_value = Just $ textToPUtf8 s
                    , PbLetable.tag   = IL_TEXT
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(ILBool b) =
    P'.defaultValue { PbLetable.bool_value = Just b
                    , PbLetable.tag   = IL_BOOL
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(ILKillProcess _ msg) =
    P'.defaultValue { PbLetable.string_value = Just $ textToPUtf8 msg
                    , PbLetable.tag   = IL_KILL_PROCESS
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(ILTuple [] _allocsrc) =
    P'.defaultValue { PbLetable.tag   = IL_TUPLE
                    , PbLetable.type' = Just $ dumpType (typeMo x) }

dumpExpr x@(ILTuple vs allocsrc) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar v | v <- vs]
                    , PbLetable.tag   = IL_TUPLE
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.alloc_info = Just $ dumpAllocate
                         (AllocInfo (tupStruct $ typeMo x)
                                    MemRegionGlobalHeap "xtupx" Nothing Nothing
                                    (showAllocationSource allocsrc)) }

dumpExpr   (ILOccurrence v occ) =
    P'.defaultValue { PbLetable.tag   = IL_OCCURRENCE
                    , PbLetable.occ   = Just $ dumpOccurrence v occ
                    , PbLetable.type' = Nothing } -- TODO use type here

dumpExpr x@(ILAllocate info) =
    P'.defaultValue { PbLetable.tag   = IL_ALLOCATE
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.alloc_info = Just $ dumpAllocate info }

dumpExpr  (ILAllocArray (ArrayType elt_ty) size) =
    P'.defaultValue { PbLetable.parts = fromList []
                    , PbLetable.tag   = IL_ALLOCATE
                    , PbLetable.type' = Just $ dumpType elt_ty
                    , PbLetable.alloc_info = Just $ dumpAllocate
                       (AllocInfo elt_ty MemRegionGlobalHeap "xarrayx"
                                      Nothing (Just size)  "...array...") }
dumpExpr  (ILAllocArray nonArrayType _) =
         error $ "ProtobufIL.hs: Can't dump ILAllocArray with non-array type "
              ++ show nonArrayType

dumpExpr x@(ILDeref _ a) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar a]
                    , PbLetable.tag   = IL_DEREF
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(ILStore v r) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [v, r])
                    , PbLetable.tag   = IL_STORE
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(ILArrayRead _t (ArrayIndex b i rng sg)) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [b, i])
                    , PbLetable.tag   = IL_ARRAY_READ
                    , PbLetable.string_value = Just $ stringSG sg
                    , PbLetable.prim_op_name = Just $ u8fromString $ highlightFirstLine rng
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(ILArrayPoke (ArrayIndex b i rng sg) v) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [b, i, v])
                    , PbLetable.tag   = IL_ARRAY_POKE
                    , PbLetable.string_value = Just $ stringSG sg
                    , PbLetable.prim_op_name = Just $ u8fromString $ highlightFirstLine rng
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(ILInt _ty int) =
    P'.defaultValue { PbLetable.tag   = IL_INT
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.pb_int = Just $ PBInt.PBInt
                                 { clean = u8fromString (show $ litIntValue int)
                                 , bits  = intToInt32   (litIntMinBits int) }
                    }

dumpExpr x@(ILFloat _ty flt) =
    P'.defaultValue { PbLetable.tag   = IL_FLOAT
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.dval  = Just $ litFloatValue flt
                    }

dumpExpr (ILCall t base args)
        = dumpCall t (dumpVar base)          args (mayTriggerGC base)

dumpExpr (ILCallPrim t (NamedPrim (TypedId _ (GlobalSymbol gs))) [arr])
        | gs == T.pack "prim_arrayLength"
        = dumpArrayLength t arr

dumpExpr (ILCallPrim t (NamedPrim base) args)
        = dumpCall t (dumpGlobalSymbol base) args (mayTriggerGC base)

dumpExpr (ILCallPrim t (PrimOp op _ty) args)
        = dumpCallPrimOp t op args

dumpExpr (ILCallPrim t (CoroPrim coroPrim argty retty) args)
        = dumpCallCoroOp t coroPrim argty retty args True

dumpExpr (ILCallPrim t (PrimIntTrunc _from to) args)
        = dumpCallPrimOp t ("trunc_i" ++ show tosize) args
        where tosize = intOfSize to

dumpExpr (ILAppCtor t cinfo args) = dumpAppCtor t cinfo args
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||||||| Calls ||||||||||||||||||||||||||{{{
dumpCall :: MonoType -> TermVar -> [TypedId MonoType] -> Bool -> PbLetable.Letable
dumpCall t base args mayGC =
    P'.defaultValue { PbLetable.tag   = IL_CALL
                    , PbLetable.parts = fromList $ base:(fmap dumpVar args)
                    , PbLetable.type' = Just $ dumpType t
                    , PbLetable.call_may_trigger_gc = Just $ mayGC }

dumpCallPrimOp t op args = -- TODO actually use prim_op_size from C++ side.
    P'.defaultValue { PbLetable.tag   = IL_CALL_PRIMOP
                    , PbLetable.parts = fromList $ fmap dumpVar args
                    , PbLetable.prim_op_name = Just $ u8fromString op
                    , PbLetable.type' = Just $ dumpType t }

dumpAppCtor t cinfo args =
    P'.defaultValue { PbLetable.tag     = IL_CTOR
                    , PbLetable.parts   = fromList $ fmap dumpVar args
                    , PbLetable.ctor_info = Just $ dumpCtorInfo cinfo
                    , PbLetable.type'   = Just $ dumpType t }

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

dumpArrayLength t arr =
    P'.defaultValue { PbLetable.tag   = IL_ARRAY_LENGTH
                    , PbLetable.parts = fromList $ fmap dumpVar [arr]
                    , PbLetable.type' = Just $ dumpType t
                    }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||| Other Expressions ||||||||||||||||||||||{{{
prefixAllocSrc foo   (AllocationSource                prefix  rng) =
                     (AllocationSource (foo ++ " " ++ prefix) rng)

showAllocationSource (AllocationSource prefix rng) =
                 prefix ++ highlightFirstLine rng

dumpClosureWithName (varid, CC.Closure procid envid captvars allocsrc) =
    P'.defaultValue { varname  = dumpIdent varid
                    , proc_id  = textToPUtf8 (identPrefix (tidIdent procid))
                    , env_id   = dumpIdent envid
                    , env      = dumpExpr (ILTuple captvars $
                                               prefixAllocSrc "env of" allocsrc)
                    , allocsite = u8fromString $ showAllocationSource allocsrc }

dumpCtorInfo (CtorInfo cid@(CtorId _dtn dtcn _arity ciid)
                           (DataCtor dcn dcid _tyfs tys)) =
  case (ciid == dcid, dtcn == T.unpack dcn) of
    (_, False) -> error $ "Ctor info inconsistent, had different names for ctor id and data ctor."
    (False, _) -> error $ "Ctor info inconsistent, had different tags for ctor id and data ctor."
    (_,     _) -> -- ignore type formals...
        P'.defaultValue { PbCtorInfo.ctor_id = dumpCtorId cid
                        , PbCtorInfo.ctor_arg_types = fromList $ map dumpType tys
                        }

dumpCtorId (CtorId dtn dtcn _arity ciid) =
    P'.defaultValue { PbCtorId.ctor_type_name = u8fromString dtn
                    , PbCtorId.ctor_ctor_name = u8fromString dtcn
                    , PbCtorId.ctor_local_id  = intToInt32 ciid
                    }

dumpOccurrence var offsCtorIds =
    let (offs, infos) = unzip offsCtorIds in
    let ids           = map ctorInfoId infos in
    P'.defaultValue { PbOccurrence.occ_offset = fromList $ map intToInt32 offs
                    , PbOccurrence.occ_ctorid = fromList $ map dumpCtorId ids
                    , PbOccurrence.scrutinee  = dumpVar var
                    , PbOccurrence.type'      = Just $ dumpType $
                                                occType (tidType var) offs infos
                    }

occType ty [] [] = ty
occType _ (k:offs) ((CtorInfo _ (DataCtor _ _ _ types)):infos) =
                                                 occType (types !! k) offs infos
occType ty offs infos =
        error $ "occType: " ++ show ty ++ "; offs=" ++ show offs ++ "~~~" ++ show infos

-----------------------------------------------------------------------
dumpVar (TypedId t i) = dumpMoVar t i

dumpGlobalSymbol base =
    P'.defaultValue { PbTermVar.tag   = IL_GLOBAL_SYMBOL
                    , PbTermVar.name  = dumpIdent (tidIdent base)
                    , PbTermVar.typ   = Just $ dumpType (tidType  base) }

dumpMoVar t i@(GlobalSymbol _) = dumpGlobalSymbol (TypedId t i)
dumpMoVar t i =
    P'.defaultValue { PbTermVar.tag  = IL_VAR
                    , PbTermVar.name = dumpIdent i
                    , PbTermVar.typ  = Just $ dumpType t  }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

dumpILProgramToProtobuf :: ILProgram -> FilePath -> IO ()
dumpILProgramToProtobuf m outpath = do
    L.writeFile outpath (messagePut $ dumpProgramToModule m)
  where
    dumpProgramToModule :: ILProgram -> Module
    dumpProgramToModule (ILProgram procdefs extern_decls datatypes (SourceLines lines))
        = Module { modulename = u8fromString $ "foo"
                 , procs      = fromList (map dumpProc procdefs)
          , extern_val_decls  = fromList (map dumpDecl extern_decls)
                 , typ_decls  = fromList (map dumpDataTypeDecl datatypes)
                 , modlines   = fmap textToPUtf8 lines
                 }

    dumpProc (ILProcDef p predmap gcroots)
      = Proc { Proc.name  = dumpIdent $ CC.procIdent p
             , in_args    = fromList $ [dumpIdent (tidIdent v) | v <- CC.procVars p]
             , proctype   = dumpProcType (preProcType p)
             , Proc.blocks= fromList $ map (dumpBlock predmap) (CC.procBlocks p)
             , Proc.lines = Just $ u8fromString (showSourceRange $ CC.procRange p)
             , Proc.linkage = Foster.Bepb.Proc.Linkage.Internal
             }
    preProcType proc =
        let retty = CC.procReturnType proc in
        let argtys = map tidType (CC.procVars proc) in
        (argtys, retty, FastCC)

    dumpDataTypeDecl datatype =
        let name = dataTypeName datatype in
        Decl { Decl.name  = u8fromString name
             , Decl.type' = dumpDataType name (dataTypeCtors datatype)
             }

    dumpDecl (MoExternDecl s t) =
        Decl { Decl.name  = u8fromString s
             , Decl.type' = dumpType t
             }

-- |||||||||||||||||||||||| Boilerplate |||||||||||||||||||||||||{{{
typeMo expr = case expr of
    ILText _                -> TyConApp "Text" []
    ILBool _                -> PrimInt I1
    ILInt t _               -> t
    ILFloat t _             -> t
    ILKillProcess t _       -> t
    ILTuple vs _            -> TupleType (map tidType vs)
    ILOccurrence {}         -> error $ "ProtobufIL: No typeMo for ILOccurrence"
    ILCall     t  _ _       -> t
    ILCallPrim t  _ _       -> t
    ILAppCtor  t  _ _       -> t
    ILAllocate info         -> allocType info
    ILAllocArray t _        -> t
    ILAlloc v _rgn          -> PtrType (tidType v)
    ILDeref t _             -> t
    ILStore _ _             -> TupleType []
    ILArrayRead t _         -> t
    ILArrayPoke {}          -> TupleType []
    ILBitcast   t _         -> t

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

