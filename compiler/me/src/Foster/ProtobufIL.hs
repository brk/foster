-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufIL (
  dumpILProgramToProtobuf
) where

import Foster.Base
import Foster.Kind
import Foster.ILExpr
import qualified Foster.CloConv as CC(Proc(..))
import Foster.TypeLL
import Foster.Letable
import Foster.ProtobufUtils

import qualified Data.ByteString.Lazy as L(writeFile)
import Data.Sequence as Seq(fromList)
import Data.Map as Map(lookup)

import Text.ProtocolBuffers(messagePut)

import Foster.Bepb.ProcType     as ProcType
import Foster.Bepb.Type.Tag     as PbTypeTag
import Foster.Bepb.Type         as PbType
import Foster.Bepb.Proc         as Proc
import Foster.Bepb.Decl         as Decl
import Foster.Bepb.PBInt        as PBInt
import qualified Foster.Bepb.Block        as PbBlock
import Foster.Bepb.LetVal       as PbLetVal
import qualified Foster.Bepb.Letable      as PbLetable
import Foster.Bepb.Terminator   as PbTerminator
import Foster.Bepb.BlockMiddle  as PbBlockMiddle
import Foster.Bepb.TermVar      as PbTermVar
import Foster.Bepb.PbCtorId     as PbCtorId
import Foster.Bepb.PbDataCtor   as PbDataCtor
import Foster.Bepb.PbCtorRepr   as PbCtorRepr
import Foster.Bepb.PbCallInfo   as PbCallInfo
import Foster.Bepb.PbCtorInfo   as PbCtorInfo
import Foster.Bepb.RebindId     as PbRebindId
import Foster.Bepb.PbAllocInfo  as PbAllocInfo
import Foster.Bepb.PbOccurrence as PbOccurrence
import Foster.Bepb.PbSwitch     as PbSwitch
import Foster.Bepb.PbCoroPrim   as PbCoroPrim
import Foster.Bepb.Module       as Module
import Foster.Bepb.RootInit     as PbRootInit
import Foster.Bepb.RootKill     as PbRootKill
import Foster.Bepb.TupleStore   as PbTupleStore
import Foster.Bepb.Letable.Tag
import Foster.Bepb.PbCoroPrim.Tag
import Foster.Bepb.PbCtorRepr.Tag
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
                then error $ "cannot dump negative ident! " ++ show i
                else u8fromString $ show i

-----------------------------------------------------------------------

-- |||||||||||||||||||||||||||| Types |||||||||||||||||||||||||||{{{

dumpUnknownType () =
  P'.defaultValue { PbType.tag = PbTypeTag.PTR
                  , type_parts = fromList $ [dumpIntType 999]
                  }

dumpIntType sizeBits = P'.defaultValue { PbType.tag  = PbTypeTag.PRIM_INT
                                       , PbType.carray_size = Just sizeBits }

dumpType :: TypeLL -> PbType.Type
dumpType (LLPtrTypeUnknown)  = dumpUnknownType ()
dumpType (LLPrimInt (IWord 0)) = dumpIntType (-32)
dumpType (LLPrimInt (IWord 1)) = dumpIntType (-64)
dumpType (LLPrimInt size)    = dumpIntType (fromIntegral $ intSizeOf size)
dumpType (LLPrimFloat64)     =
              P'.defaultValue { PbType.tag  = PbTypeTag.FLOAT64 }
dumpType (LLNamedType nm) =
              P'.defaultValue { PbType.tag  = PbTypeTag.NAMED
                              , PbType.name = Just $ u8fromString nm }
dumpType (LLStructType types) =
              P'.defaultValue { PbType.tag  = PbTypeTag.STRUCT
                              ,  type_parts = fromList $ fmap dumpType types }
dumpType (LLCoroType a b) =
              P'.defaultValue { PbType.tag  = PbTypeTag.CORO
                              ,  type_parts = fromList $ fmap dumpType [a,b] }
dumpType (LLPtrType ty) =
              P'.defaultValue { PbType.tag = PbTypeTag.PTR
                              , type_parts = fromList $ fmap dumpType [ty] }
dumpType (LLArrayType ty) =
              P'.defaultValue { PbType.tag = PbTypeTag.ARRAY
                              , type_parts = fromList $ fmap dumpType [ty] }
dumpType (LLProcType s t cc) =
              P'.defaultValue { PbType.tag = PbTypeTag.PROC
                              , PbType.procty = Just $ dumpProcType (s, t, cc) }
dumpProcType (ss, t, cc) =
    ProcType.ProcType {
          arg_types = fromList (map dumpType ss)
        , ProcType.ret_type  = dumpType t
        , calling_convention = Just $ u8fromString (stringOfCC cc)
    }
      where stringOfCC FastCC = "fastcc"
            stringOfCC CCC    = "ccc"

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

dumpMemRegion :: AllocMemRegion -> PbMemRegion.MemRegion
dumpMemRegion amr = case amr of
    MemRegionStack      -> PbMemRegion.MEM_REGION_STACK
    MemRegionGlobalHeap -> PbMemRegion.MEM_REGION_GLOBAL_HEAP

dumpAllocate :: AllocInfo TypeLL -> PbAllocInfo
dumpAllocate (AllocInfo typ region typename maybe_tag maybe_array_size allocsite zeroinit) =
    P'.defaultValue { PbAllocInfo.mem_region = dumpMemRegion region
                    , PbAllocInfo.type'      = dumpType      typ
                    , PbAllocInfo.type_name  = u8fromString  typename
                    , PbAllocInfo.ctor_repr  = fmap (dumpCtorRepr "dumpAllocate") maybe_tag
                    , PbAllocInfo.array_size = fmap dumpVar  maybe_array_size
                    , PbAllocInfo.alloc_site = u8fromString  allocsite
                    , PbAllocInfo.zero_init  = needsZeroInit zeroinit
                    }
     where needsZeroInit DoZeroInit = True
           needsZeroInit NoZeroInit = False

-- ||||||||||||||||||||||||||| CFGs |||||||||||||||||||||||||||||{{{
-- dumpBlock :: Map.Map BlockId (Maybe Int) -> ILBlock -> PbBlock.Block
dumpBlock predmap (Block (id, phis) mids illast) =
    P'.defaultValue { PbBlock.block_id = dumpBlockId id
                    , PbBlock.phis     = fromList $ map dumpVar phis
                    , PbBlock.middle   = fromList $ map dumpMiddle mids
                    , PbBlock.last     = dumpLast illast
                    , PbBlock.num_preds= fmap intToInt32 (Map.lookup id predmap)
                    } -- num_preds needed for LLVM to initialize the phi nodes.

dumpMiddle :: ILMiddle -> PbBlockMiddle.BlockMiddle
dumpMiddle (ILLetVal id letable maygc) =
    P'.defaultValue { let_val = Just (dumpLetVal id letable maygc) }
dumpMiddle (ILGCRootKill v continuationMayGC) =
    P'.defaultValue { gcroot_kill = Just $ P'.defaultValue {
           root_kill_root = (dumpVar v)
         , root_kill_null = continuationMayGC
      } }
dumpMiddle (ILGCRootInit src root) =
    P'.defaultValue { gcroot_init = Just $ P'.defaultValue {
           root_init_src  = (dumpVar src)
         , root_init_root = (dumpVar root)
    } }
dumpMiddle (ILRebindId id var) =
    P'.defaultValue { rebind = Just $
         P'.defaultValue { from_id = dumpIdent id , to_var  = dumpVar var } }
dumpMiddle ts@(ILTupleStore {}) =
    P'.defaultValue { tuple_store = Just $ dumpTupleStore ts }

dumpTupleStore (ILTupleStore vs v r) =
   P'.defaultValue { stored_vars = fromList $ map dumpVar vs
                   , storage     = dumpVar v
                   , storage_indir = case r of
                                       MemRegionStack      -> False
                                       MemRegionGlobalHeap -> True
    }
dumpTupleStore other = error $ "dumpTupleStore called on non-tuple-store value: " ++ show other

dumpLetVal :: Ident -> Letable TypeLL -> MayGC -> PbLetVal.LetVal
dumpLetVal id letable maygc =
    P'.defaultValue { let_val_id = dumpIdent id
                    , let_expr   = dumpExpr maygc letable
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
dumpLast (ILCase var arms def) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_CASE
                    , PbTerminator.scase  = Just $ dumpSwitch var arms def }

dumpSwitch var arms def =
    let (ctors, ids) = Prelude.unzip arms in
    P'.defaultValue { PbSwitch.ctors   = fromList (map (dumpCtorIdWithRepr "dumpSwitch") ctors)
                    , PbSwitch.blocks  = fromList (map dumpBlockId ids)
                    , PbSwitch.defCase = fmap dumpBlockId def
                    , PbSwitch.var     = dumpVar var
                    , PbSwitch.ctor_by = Just $ u8fromString $ determineHowToFindObjectCtor ctors
                    }

determineHowToFindObjectCtor ctors = go "INDIR" ctors
  where go how [] = how
        go how ((_, CR_Transparent):ctors) = go how     ctors
        go how ((_, CR_Default _  ):ctors) = go how     ctors
        go _   ((_, CR_Tagged  _  ):_) = "MASK3"
        go _   ((_, CR_Nullary _  ):_) = "MASK3"
        go _   ((_, CR_Value   _  ):_) = "VALUE"
        go _   ((_, CR_TransparentU):_) = "VALUE"

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||| Literals ||||||||||||||||||||||||||||{{{
dumpLiteral ty lit =
  case lit of
    LitBool  b -> P'.defaultValue { PbLetable.bool_value = Just b
                                  , PbLetable.tag   = IL_BOOL
                                  , PbLetable.type' = Just $ dumpType ty }
    LitText  t -> P'.defaultValue { PbLetable.string_value = Just $ textToPUtf8 t
                                  , PbLetable.tag   = IL_TEXT
                                  , PbLetable.type' = Just $ dumpType ty  }
    LitInt int -> P'.defaultValue { PbLetable.tag   = IL_INT
                                  , PbLetable.type' = Just $ dumpType ty
                                  , PbLetable.pb_int = Just $ mkPbInt ty int
                                  }
    LitFloat f -> P'.defaultValue { PbLetable.tag   = IL_FLOAT
                                  , PbLetable.type' = Just $ dumpType ty
                                  , PbLetable.dval  = Just $ litFloatValue f
                                  }

mkPbInt ty int = PBInt.PBInt { clean = u8fromString (show $ litIntValue int)
                             , bits  = intToInt32 (fixnumTypeSize ty) }

fixnumTypeSize (LLPrimInt (IWord 0)) = (-32)
fixnumTypeSize (LLPrimInt (IWord 1)) = (-64)
fixnumTypeSize (LLPrimInt isb) = intSizeOf isb
fixnumTypeSize other = error $ "Expected int literal to have LLPrimInt type; had " ++ show other
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- |||||||||||||||||||||||| Expressions |||||||||||||||||||||||||{{{
dumpExpr :: MayGC -> Letable TypeLL -> PbLetable.Letable
dumpExpr _ (ILAlloc    {}) = error "ILAlloc should have been translated away!"
dumpExpr _ (ILBitcast t v) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar v]
                    , PbLetable.tag   = IL_BITCAST
                    , PbLetable.type' = Just $ dumpType t  }
dumpExpr _ (ILLiteral ty lit) = dumpLiteral ty lit
dumpExpr _ x@(ILKillProcess _ msg) =
    P'.defaultValue { PbLetable.string_value = Just $ textToPUtf8 msg
                    , PbLetable.tag   = IL_KILL_PROCESS
                    , PbLetable.type' = Just $ dumpType (typeOf x)  }
dumpExpr _ x@(ILObjectCopy from to) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar from, dumpVar to]
                    , PbLetable.tag   = IL_OBJECT_COPY
                    , PbLetable.type' = Just $ dumpType (typeOf x)  }
dumpExpr _ x@(ILTuple [] _allocsrc) =
    P'.defaultValue { PbLetable.tag   = IL_UNIT
                    , PbLetable.type' = Just $ dumpType (typeOf x) }

dumpExpr _ (ILTuple vs allocsrc) =
        error $ "ProtobufIL.hs: ILTuple " ++ show vs
            ++ "\n should have been eliminated!\n" ++ show allocsrc

dumpExpr _ (ILOccurrence t v occ) =
    P'.defaultValue { PbLetable.tag   = IL_OCCURRENCE
                    , PbLetable.occ   = Just $ dumpOccurrence v occ
                    , PbLetable.type' = Just $ dumpType t }

dumpExpr _ (ILAllocate info) =
    P'.defaultValue { PbLetable.tag   = IL_ALLOCATE
                    , PbLetable.type' = Just $ dumpType (allocType info)
                    , PbLetable.alloc_info = Just $ dumpAllocate info }

dumpExpr _  (ILAllocArray (LLArrayType elt_ty) size) =
    P'.defaultValue { PbLetable.parts = fromList []
                    , PbLetable.tag   = IL_ALLOCATE
                    , PbLetable.type' = Just $ dumpType elt_ty
                    , PbLetable.alloc_info = Just $ dumpAllocate
                       (AllocInfo elt_ty MemRegionGlobalHeap "xarrayx"
                                  Nothing (Just size)  "...array..." NoZeroInit) }
dumpExpr _  (ILAllocArray nonArrayType _) =
         error $ "ProtobufIL.hs: Can't dump ILAllocArray with non-array type "
              ++ show nonArrayType

dumpExpr _ x@(ILDeref _ a) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar a]
                    , PbLetable.tag   = IL_DEREF
                    , PbLetable.type' = Just $ dumpType (typeOf x)  }

dumpExpr _ x@(ILStore v r) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [v, r])
                    , PbLetable.tag   = IL_STORE
                    , PbLetable.type' = Just $ dumpType (typeOf x)  }

dumpExpr _ x@(ILArrayRead _t (ArrayIndex b i rng sg)) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [b, i])
                    , PbLetable.tag   = IL_ARRAY_READ
                    , PbLetable.string_value = Just $ stringSG sg
                    , PbLetable.prim_op_name = Just $ u8fromString $ highlightFirstLine rng
                    , PbLetable.type' = Just $ dumpType (typeOf x)  }

dumpExpr _ x@(ILArrayPoke (ArrayIndex b i rng sg) v) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [b, i, v])
                    , PbLetable.tag   = IL_ARRAY_POKE
                    , PbLetable.string_value = Just $ stringSG sg
                    , PbLetable.prim_op_name = Just $ u8fromString $ highlightFirstLine rng
                    , PbLetable.type' = Just $ dumpType (typeOf x)  }

dumpExpr maygc (ILCall t base args)
        = dumpCall t (dumpVar base)          args maygc ccs
  where stringOfCC FastCC = "fastcc"
        stringOfCC CCC    = "ccc"
        ccs = stringOfCC $ extractCallConv (tidType base)

dumpExpr _ (ILCallPrim t (NamedPrim (TypedId _ (GlobalSymbol gs))) [arr])
        | gs == T.pack "prim_arrayLength"
        = dumpArrayLength t arr

dumpExpr maygc (ILCallPrim t (NamedPrim base) args)
        = dumpCall t (dumpGlobalSymbol base) args maygc "ccc"

dumpExpr _ (ILCallPrim t (PrimOp op _ty) args)
        = dumpCallPrimOp t op args

dumpExpr _ (ILCallPrim t (CoroPrim coroPrim argty retty) args)
        = dumpCallCoroOp t coroPrim argty retty args True

dumpExpr _ (ILCallPrim t (PrimIntTrunc _from to) args)
        = dumpCallPrimOp t (truncOp to) args
  where truncOp I1        = "trunc_i1"
        truncOp I8        = "trunc_i8"
        truncOp I32       = "trunc_i32"
        truncOp I64       = "trunc_i64"
        truncOp (IWord 0) = "trunc_w0"
        truncOp (IWord 1) = "trunc_w1"
        truncOp (IWord x) = error $ "Protobuf.hs: truncOp can't handle Word " ++ show x

dumpExpr _ (ILCallPrim ty PrimArrayLiteral args)
        = let (LLArrayType ety) = ty in
          P'.defaultValue {
                      PbLetable.tag       = IL_ARRAY_LITERAL
                    , PbLetable.type'     = Just $ dumpType ty
                    , PbLetable.elem_type = Just $ dumpType ety
                    , PbLetable.parts     = fromList (map dumpVar args)
          }

dumpExpr _ (ILAppCtor _ _cinfo _) = error $ "ProtobufIL.hs saw ILAppCtor, which"
                                       ++ " should have been translated away..."

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||||||| Calls ||||||||||||||||||||||||||{{{
dumpCall :: TypeLL -> TermVar -> [TypedId TypeLL] -> MayGC -> String -> PbLetable.Letable
dumpCall t base args maygc callConv =
    P'.defaultValue { PbLetable.tag   = IL_CALL
                    , PbLetable.parts = fromList $ base:(fmap dumpVar args)
                    , PbLetable.type' = Just $ dumpType t
                    , PbLetable.call_info = Just $ dumpCallInfo
                                ( --trace ("mayGC " ++ show (PbTermVar.name base) ++ "\t:\t" ++show maygc) $
                                 boolGC maygc) callConv Nothing
                    }

dumpCallInfo mayGC strCallConv pbCoroPrim =
    P'.defaultValue { PbCallInfo.coro_prim = pbCoroPrim
                    , PbCallInfo.call_may_trigger_gc = mayGC
                    , PbCallInfo.call_is_a_tail_call = False -- [1]
                    , PbCallInfo.call_conv = u8fromString strCallConv
                    }
-- [1] To be safe, a tail call must not pass any pointers into the caller's
--     stack frame, because the caller's stack frame would become
--     the callee's stack frame. Since we don't do that analysis yet,
--     we provide a conservative default. But note that we've already
--     eliminated tail *recursion*.

dumpCallPrimOp t op args = -- TODO actually use prim_op_size from C++ side.
    P'.defaultValue { PbLetable.tag   = IL_CALL_PRIMOP
                    , PbLetable.parts = fromList $ fmap dumpVar args
                    , PbLetable.prim_op_name = Just $ u8fromString op
                    , PbLetable.type' = Just $ dumpType t }

dumpCallCoroOp t coroPrim argty retty args mayGC =
    P'.defaultValue { PbLetable.tag   = IL_CALL
                    , PbLetable.parts = fromList $ fmap dumpVar args
                    , PbLetable.type' = Just $ dumpType t
                    , PbLetable.call_info = Just $
                                     dumpCallInfo mayGC "fastcc" pbCoroPrim
                    }
    where
        pbCoroPrim = Just $ P'.defaultValue {
                          PbCoroPrim.tag = coroFnTag coroPrim  ,
                          PbCoroPrim.ret_type = dumpType retty ,
                          PbCoroPrim.arg_type = dumpType argty }
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
dumpCtorInfo (LLCtorInfo cid repr tys) =
    P'.defaultValue { PbCtorInfo.ctor_id = dumpCtorIdWithRepr "dumpCtorInfo" (cid, repr)
                    , PbCtorInfo.ctor_struct_ty = if null tys
                            then Nothing
                            else Just $ dumpType (LLStructType tys)
                    }

dumpCtorIdWithRepr from (CtorId dtn dtcn _arity, repr) =
    P'.defaultValue { PbCtorId.ctor_type_name = u8fromString dtn
                    , PbCtorId.ctor_ctor_name = u8fromString dtcn
                    , PbCtorId.ctor_repr      = dumpCtorRepr from repr
                    }

dumpOccurrence var offsCtorInfos =
    let (offs, infos) = unzip offsCtorInfos in
    P'.defaultValue { PbOccurrence.occ_offset = fromList $ map intToInt32 offs
                    , PbOccurrence.occ_ctors  = fromList $ map dumpCtorInfo infos
                    , PbOccurrence.scrutinee  = dumpVar var
                    }

dumpCtorRepr _ (CR_Tagged 0) =
    P'.defaultValue { PbCtorRepr.tag = CR_DEFAULT
                    , PbCtorRepr.ctor_repr_tag = Just $ intToInt64 0
                    }

dumpCtorRepr _ (CR_Tagged _) = error $ "Runtime can't yet handle non-zero pointer tags."

dumpCtorRepr _ (CR_Default ciid) =
    P'.defaultValue { PbCtorRepr.tag = CR_DEFAULT
                    , PbCtorRepr.ctor_repr_tag = Just $ intToInt64 ciid
                    }

dumpCtorRepr _ (CR_Transparent) =
    P'.defaultValue { PbCtorRepr.tag = CR_TRANSPARENT
                    }

dumpCtorRepr _ (CR_TransparentU) =
    P'.defaultValue { PbCtorRepr.tag = CR_TRANSPARENT
                    }

dumpCtorRepr _ (CR_Nullary ciid) =
    P'.defaultValue { PbCtorRepr.tag = CR_NULLARY
                    , PbCtorRepr.ctor_repr_tag = Just $ intToInt64 ciid
                    }

dumpCtorRepr _ (CR_Value ciid) =
    P'.defaultValue { PbCtorRepr.tag = CR_VALUE
                    , PbCtorRepr.ctor_repr_tag = Just $ fromInteger ciid
                    }

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
             , Proc.lines = Just $ u8fromString (showSourceRange . annotRange $ CC.procAnnot p)
             , Proc.linkage = Foster.Bepb.Proc.Linkage.Internal
             , Proc.gcroots = fromList $ map dumpVar gcroots
             }
    preProcType proc =
        let retty = CC.procReturnType proc in
        let argtys = map tidType (CC.procVars proc) in
        (argtys, retty, FastCC)

    dumpDataTypeDecl :: DataType TypeLL -> Decl
    dumpDataTypeDecl datatype =
        let formal = dataTypeName datatype in
        Decl { Decl.name  = u8fromString (typeFormalName formal)
             , Decl.type' = dumpDataType formal (dataTypeCtors datatype)
             }

    dumpDecl (LLExternDecl s t) =
        Decl { Decl.name  = u8fromString s
             , Decl.type' = dumpType t
             }

    dumpDataType (TypeFormalAST dtName KindPointerSized) ctors =
        P'.defaultValue { PbType.tag  = PbTypeTag.DATATYPE
                        , PbType.name = Just $ u8fromString dtName
                        , PbType.ctor = fromList $ fmap dumpDataCtor ctors
                        }
     where
        dumpDataCtor (DataCtor ctorName _tyformals types _range) =
          PbDataCtor { PbDataCtor.name  = textToPUtf8 ctorName
                     , PbDataCtor.type' = fromList $ map dumpType types
                     }

    dumpDataType (TypeFormalAST _dtName KindAnySizeType) [DataCtor _nm [] [ty] _range] =
        dumpType ty

    dumpDataType (TypeFormalAST dtName KindAnySizeType) ctors =
            error $ "Don't yet know how to handle " ++ dtName ++ " : Type, with ctors..." ++ show ctors
