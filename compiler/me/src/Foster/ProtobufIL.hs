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
import Foster.Bepb.PbSwitch     as PbSwitch
import Foster.Bepb.PbCoroPrim   as PbCoroPrim
import Foster.Bepb.Module       as Module
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

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

dumpMemRegion :: AllocMemRegion -> PbMemRegion.MemRegion
dumpMemRegion amr = case amr of
    MemRegionStack      -> PbMemRegion.MEM_REGION_STACK
    MemRegionGlobalHeap -> PbMemRegion.MEM_REGION_GLOBAL_HEAP

dumpAllocate :: AllocInfo MonoType -> PbAllocInfo
dumpAllocate (AllocInfo typ region maybe_array_size allocsite) =
    P'.defaultValue { PbAllocInfo.mem_region = dumpMemRegion region
                    , PbAllocInfo.type'      = dumpType      typ
                    , PbAllocInfo.array_size = fmap dumpVar maybe_array_size
                    , PbAllocInfo.alloc_site = u8fromString allocsite
                    }

-- ||||||||||||||||||||||||||| CFGs |||||||||||||||||||||||||||||{{{
dumpBlock :: MoBlock -> PbBlock.Block
dumpBlock (MoBlock (id, phis) mids illast numPreds) =
    P'.defaultValue { PbBlock.block_id = dumpBlockId id
                    , PbBlock.phis     = fromList $ map dumpVar phis
                    , PbBlock.middle   = fromList $ map dumpMiddle mids
                    , PbBlock.last     = dumpLast illast
                    , PbBlock.num_preds= fmap intToInt32 numPreds
                    }

dumpMiddle :: MoMiddle -> PbBlockMiddle.BlockMiddle
dumpMiddle (MoLetVal id letable) =
    P'.defaultValue { let_val = Just (dumpLetVal id letable) }
dumpMiddle (MoClosures ids clos) =
    P'.defaultValue { let_clo = Just (dumpLetClosures ids clos) }
dumpMiddle (MoRebindId from to) =
    P'.defaultValue { rebind = Just $ dumpRebinding from to }
dumpMiddle (MoLetBitcast from to) =
    P'.defaultValue { bitcast = Just $ dumpRebinding from to }

dumpRebinding from to = P'.defaultValue { from_id = dumpIdent from
                                        , to_var  = dumpVar to }

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
dumpLast (MoBr blockid args) =
    P'.defaultValue { PbTerminator.tag    = BLOCK_BR
                    , PbTerminator.block  = Just $ dumpBlockId blockid
                    , PbTerminator.args   = fromList $ map dumpVar args }
dumpLast (MoCase var arms def occ) =
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
dumpExpr :: MonoLetable -> PbLetable.Letable

dumpExpr x@(MoText s) =
    P'.defaultValue { PbLetable.string_value = Just $ textToPUtf8 s
                    , PbLetable.tag   = IL_TEXT
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoBool b) =
    P'.defaultValue { PbLetable.bool_value = Just b
                    , PbLetable.tag   = IL_BOOL
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoTuple vs allocsrc) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar v | v <- vs]
                    , PbLetable.tag   = IL_TUPLE
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.alloc_info = Just $ dumpAllocate
                         (AllocInfo (tupStruct $ typeMo x)
                                    MemRegionGlobalHeap Nothing
                                    (showAllocationSource allocsrc)) }

dumpExpr   (MoOccurrence v occ) =
    P'.defaultValue { PbLetable.tag   = IL_OCCURRENCE
                    , PbLetable.occ   = Just $ dumpOccurrence v occ
                    , PbLetable.type' = Nothing } -- TODO use type here

--dumpExpr x@(MoAllocate info) = error $ "MoAllocate " ++ show info
--    P'.defaultValue { PbLetable.tag   = IL_ALLOCATE
--                    , PbLetable.type' = Just $ dumpType (typeMo x)
--                    , PbLetable.alloc_info = Just $ dumpAllocate info }

dumpExpr x@(MoAlloc a rgn) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar a]
                    , PbLetable.tag   = IL_ALLOC
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.alloc_info = Just $ dumpAllocate
                         (AllocInfo (typeMo x) rgn Nothing "...alloc...") }

dumpExpr  (MoAllocArray elt_ty size) =
    P'.defaultValue { PbLetable.parts = fromList []
                    , PbLetable.tag   = IL_ALLOCATE
                    , PbLetable.type' = Just $ dumpType elt_ty
                    , PbLetable.alloc_info = Just $ dumpAllocate
                       (AllocInfo elt_ty MemRegionGlobalHeap (Just size)
                                                           "...array...") }

dumpExpr x@(MoDeref a) =
    P'.defaultValue { PbLetable.parts = fromList [dumpVar a]
                    , PbLetable.tag   = IL_DEREF
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoStore a b) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [a, b])
                    , PbLetable.tag   = IL_STORE
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoArrayRead _t (ArrayIndex b i rng sg)) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [b, i])
                    , PbLetable.tag   = IL_ARRAY_READ
                    , PbLetable.string_value = Just $ stringSG sg
                    , PbLetable.prim_op_name = Just $ u8fromString $ highlightFirstLine rng
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoArrayPoke (ArrayIndex b i rng sg) v) =
    P'.defaultValue { PbLetable.parts = fromList (fmap dumpVar [b, i, v])
                    , PbLetable.tag   = IL_ARRAY_POKE
                    , PbLetable.string_value = Just $ stringSG sg
                    , PbLetable.prim_op_name = Just $ u8fromString $ highlightFirstLine rng
                    , PbLetable.type' = Just $ dumpType (typeMo x)  }

dumpExpr x@(MoInt _ty int) =
    P'.defaultValue { PbLetable.tag   = IL_INT
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.pb_int = Just $ PBInt.PBInt
                                 { clean = u8fromString (show $ litIntValue int)
                                 , bits  = intToInt32   (litIntMinBits int) }
                    }

dumpExpr x@(MoFloat _ty flt) =
    P'.defaultValue { PbLetable.tag   = IL_FLOAT
                    , PbLetable.type' = Just $ dumpType (typeMo x)
                    , PbLetable.dval  = Just $ litFloatValue flt
                    }

dumpExpr (MoCall t base args)
        = dumpCall t (dumpVar base)          args (mayTriggerGC base)

dumpExpr (MoCallPrim t (NamedPrim (TypedId _ (GlobalSymbol gs))) [arr])
        | gs == T.pack "prim_arrayLength"
        = dumpArrayLength t arr

dumpExpr (MoCallPrim t (NamedPrim base) args)
        = dumpCall t (dumpGlobalSymbol base) args (mayTriggerGC base)

dumpExpr (MoCallPrim t (PrimOp op _ty) args)
        = dumpCallPrimOp t op args

dumpExpr (MoCallPrim t (CoroPrim coroPrim argty retty) args)
        = dumpCallCoroOp t coroPrim argty retty args True

dumpExpr (MoCallPrim t (PrimIntTrunc _from to) args)
        = dumpCallPrimOp t ("trunc_i" ++ show tosize) args
        where tosize = intOfSize to

dumpExpr (MoAppCtor t cid args) = dumpAppCtor t cid args
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

dumpAppCtor t cid args =
    P'.defaultValue { PbLetable.tag     = IL_CTOR
                    , PbLetable.parts   = fromList $ fmap dumpVar args
                    , PbLetable.ctor_id = Just $ dumpCtorId cid
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

dumpClosureWithName (varid, MoClosure procid envid captvars allocsrc) =
    P'.defaultValue { varname  = dumpIdent varid
                    , proc_id  = textToPUtf8 (identPrefix procid)
                    , env_id   = dumpIdent envid
                    , env      = dumpExpr (MoTuple captvars $
                                               prefixAllocSrc "env of" allocsrc)
                    , allocsite = u8fromString $ showAllocationSource allocsrc }

dumpCtorId (CtorId s n _a i) =
    P'.defaultValue { PbCtorId.ctor_type_name = u8fromString s
                    , PbCtorId.ctor_ctor_name = u8fromString n
                    , PbCtorId.ctor_local_id  = intToInt32 i }

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
occType _ (k:offs) ((CtorInfo _ (DataCtor _ _ types)):infos) =
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

dumpMonoModuleToProtobuf :: MonoProgram -> FilePath -> IO ()
dumpMonoModuleToProtobuf m outpath = do
    L.writeFile outpath (messagePut $ dumpProgramToModule m)
  where
    dumpProgramToModule :: MonoProgram -> Module
    dumpProgramToModule (MoProgram procdefs decls datatypes (SourceLines lines))
        = Module { modulename = u8fromString $ "foo"
                 , procs      = fromList [dumpProc p | p <- Map.elems procdefs]
                 , val_decls  = fromList (map dumpDecl decls)
                 , typ_decls  = fromList (map dumpDataTypeDecl datatypes)
                 , modlines   = fmap textToPUtf8 lines
                 }
    dumpProc p
      = Proc { Proc.name  = dumpIdent $ moProcIdent p
             , in_args    = fromList $ [dumpIdent (tidIdent v) | v <- moProcVars p]
             , proctype   = dumpProcType (preProcType p)
             , Proc.blocks= fromList $ map dumpBlock (moProcBlocks p)
             , Proc.lines = Just $ u8fromString (showSourceRange $ moProcRange p)
             , Proc.linkage = Foster.Bepb.Proc.Linkage.Internal
             }
    preProcType proc =
        let retty = moProcReturnType proc in
        let argtys = TupleType (map tidType (moProcVars proc)) in
        (argtys, retty, FastCC)

    dumpDataTypeDecl datatype =
        let name = dataTypeName datatype in
        Decl { Decl.name  = u8fromString name
             , Decl.type' = dumpDataType name (dataTypeCtors datatype)
             }

    dumpDecl (MoDecl s t) =
        Decl { Decl.name  = u8fromString s
             , Decl.type' = dumpType t
             }

-- |||||||||||||||||||||||| Boilerplate |||||||||||||||||||||||||{{{
typeMo expr = case expr of
    MoText _                -> TyConApp "Text" []
    MoBool _                -> PrimInt I1
    MoInt t _               -> t
    MoFloat t _             -> t
    MoTuple vs _            -> TupleType (map tidType vs)
    MoOccurrence {}         -> error $ "ProtobufIL: No typeMo for MoOccurrence"
    MoCall     t  _ _       -> t
    MoCallPrim t  _ _       -> t
    MoAppCtor  t  _ _       -> t
    -- MoAllocate info         -> allocType info
    MoAllocArray elt_ty _   -> ArrayType elt_ty
    MoAlloc v _rgn          -> PtrType (tidType v)
    MoDeref v               -> pointedToTypeOfVar v
    MoStore _ _             -> TupleType []
    MoArrayRead t _         -> t
    MoArrayPoke {}          -> TupleType []

pointedToTypeOfVar v = case v of
    TypedId (PtrType t) _ -> t
    _ -> error $ "ProtobufIL.hs:pointedToTypeOfVar\n"
              ++ "Expected variable to be a pointer, but had " ++ show v

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

