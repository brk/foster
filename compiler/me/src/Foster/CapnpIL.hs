{-# LANGUAGE Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2016 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.CapnpIL (
  dumpILProgramToCapnp
) where

import Foster.Base
import Foster.Kind
import Foster.ILExpr hiding (Block)
import qualified Foster.ILExpr as IL
import qualified Foster.CloConv as CC(Proc(..))
import Foster.TypeLL
import Foster.Letable hiding (Letable)
import qualified Foster.Letable as IL

import qualified Data.ByteString as BS(writeFile)
import Data.Foldable(toList)
import Data.Map as Map(lookup)

import qualified FosterIL_capnp as FC
import           FosterIL_capnp
import Minuproto

import Data.ByteString.UTF8 as UTF8
import qualified Data.Text as T
import qualified Data.Text.Encoding as E

-----------------------------------------------------------------------
type CapnpText = (ByteString, ())

u8fromString :: String -> CapnpText
u8fromString s = (UTF8.fromString s, ())

u8fromText :: T.Text -> CapnpText
u8fromText t = (E.encodeUtf8 t, ())

stringSG SG_Static  = u8fromString "static"
stringSG SG_Dynamic = u8fromString "dynamic"
stringSG SG_Unsafe  = u8fromString "static"

dumpBlockId (str, lab) = u8fromString (str ++ "." ++ show lab)

dumpIdent :: Ident -> CapnpText
dumpIdent (GlobalSymbol name NoRename)  = u8fromText name
dumpIdent (GlobalSymbol _ (RenameTo name)) = u8fromText name
dumpIdent i@(Ident _name num) = if num < 0
                then error $ "cannot dump negative ident! " ++ show i
                else u8fromString $ show i

-----------------------------------------------------------------------

-- |||||||||||||||||||||||||||| Types |||||||||||||||||||||||||||{{{

defaultType_ tag =
    Type_ { tag_of_Type_ = tag,
            name_of_Type_   = StrictlyNone,
            procty_of_Type_ = StrictlyNone,
            typeparts_of_Type_ = [],
            carraysize_of_Type_ = [],
            ctor_of_Type_ = []
           }

dumpUnknownType =
  (defaultType_ Ptr) { typeparts_of_Type_ = [dumpIntType 999] }

dumpIntType sizeBits =
  (defaultType_ Primint) { carraysize_of_Type_ = [sizeBits] }

dumpType :: TypeLL -> FC.Type_
dumpType (LLPtrTypeUnknown)  = dumpUnknownType
dumpType (LLPrimInt IWd) = dumpIntType (-32)
dumpType (LLPrimInt IDw) = dumpIntType (-64)
dumpType (LLPrimInt size)    = dumpIntType (fromIntegral $ intSizeOf size)
dumpType (LLNamedType "Float64") = defaultType_ Float64
dumpType (LLNamedType "Float32") = defaultType_ Float32
dumpType (LLNamedType nm) =
  (defaultType_ Named) { name_of_Type_ = StrictlyJust $ u8fromString nm }
dumpType (LLStructType types) =
  (defaultType_ Struct) { typeparts_of_Type_ = fmap dumpType types }
dumpType (LLCoroType {}) = dumpType (LLNamedType "Foster$GenericCoro")
dumpType (LLPtrType ty) =
  (defaultType_ Ptr) { typeparts_of_Type_ = fmap dumpType [ty] }
dumpType (LLArrayType ty) =
  (defaultType_ Array) { typeparts_of_Type_ = fmap dumpType [ty] }
dumpType (LLProcType s t cc) =
  (defaultType_ Procty) { procty_of_Type_ = StrictlyJust (dumpProcType (s, t, cc)) }

dumpProcType (ss, t, cc) =
    ProcType {
          argtypes_of_ProcType = map dumpType ss
        , rettype_of_ProcType  = dumpType t
        , callingconvention_of_ProcType = StrictlyJust $ u8fromString (stringOfCC cc)
    }
      where stringOfCC FastCC = "fastcc"
            stringOfCC CCC    = "ccc"

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

strictMB (Just foo) = StrictlyJust foo
strictMB Nothing    = StrictlyNone

optList (Just foo) = [foo]
optList Nothing    = []

dumpMemRegion :: AllocMemRegion -> FC.PbAllocInfo_MemRegion
dumpMemRegion amr = case amr of
    MemRegionStack      -> Memregionstack
    MemRegionGlobalHeap -> Memregionglobalheap
    MemRegionGlobalData -> Memregionglobaldata

dumpAllocate :: AllocInfo TypeLL -> FC.PbAllocInfo
dumpAllocate (AllocInfo typ region typename maybe_tag maybe_array_size allocsite zeroinit) =
    PbAllocInfo     { memregion_of_PbAllocInfo = dumpMemRegion region
                    , type_of_PbAllocInfo      = dumpType      typ
                    , typename_of_PbAllocInfo  = u8fromString  typename
                    , ctorrepr_of_PbAllocInfo  = strictMB $ fmap (dumpCtorRepr "dumpAllocate") maybe_tag
                    , arraysize_of_PbAllocInfo = strictMB $ fmap dumpVar  maybe_array_size
                    , allocsite_of_PbAllocInfo = u8fromString  allocsite
                    , zeroinit_of_PbAllocInfo  = needsZeroInit zeroinit
                    }
     where needsZeroInit DoZeroInit = True
           needsZeroInit NoZeroInit = False

-- ||||||||||||||||||||||||||| CFGs |||||||||||||||||||||||||||||{{{
-- dumpBlock :: Map.Map BlockId (Maybe Int) -> ILBlock -> PbBlock.Block
dumpBlock predmap (IL.Block (id, phis) mids illast) =
         FC.Block   { blockid_of_Block  = dumpBlockId id
                    , phis_of_Block     = map dumpVar' phis
                    , middle_of_Block   = map dumpMiddle mids
                    , last_of_Block     = dumpLast illast
                    , numpreds_of_Block= optList $ fmap fromIntegral (Map.lookup id predmap)
                    } -- num_preds needed for LLVM to initialize the phi nodes.


defaultMiddle =     BlockMiddle {
          letval_of_BlockMiddle     = StrictlyNone
        , rebind_of_BlockMiddle     = StrictlyNone
        , gcrootkill_of_BlockMiddle = StrictlyNone
        , gcrootinit_of_BlockMiddle = StrictlyNone
        , tuplestore_of_BlockMiddle = StrictlyNone
    }

dumpMiddle :: ILMiddle -> FC.BlockMiddle
dumpMiddle (ILLetVal id letable maygc) =
    defaultMiddle { letval_of_BlockMiddle = StrictlyJust (dumpLetVal id letable maygc) }
dumpMiddle (ILGCRootKill v continuationMayGC) =
    defaultMiddle { gcrootkill_of_BlockMiddle = StrictlyJust $ RootKill {
           rootkillroot_of_RootKill = (dumpVar v)
         , rootkillnull_of_RootKill = continuationMayGC
      } }
dumpMiddle (ILGCRootInit src root) =
    defaultMiddle { gcrootinit_of_BlockMiddle = StrictlyJust $ RootInit {
           rootinitsrc_of_RootInit  = (dumpVar src)
         , rootinitroot_of_RootInit = (dumpVar root)
    } }
dumpMiddle (ILRebindId id var) =
    defaultMiddle { rebind_of_BlockMiddle = StrictlyJust $
         RebindId { fromid_of_RebindId = dumpIdent id , tovar_of_RebindId  = dumpVar var } }
dumpMiddle ts@(ILTupleStore {}) =
    defaultMiddle { tuplestore_of_BlockMiddle = StrictlyJust $ dumpTupleStore ts }

dumpTupleStore (ILTupleStore vs v r) =
    TupleStore { storedvars_of_TupleStore = map dumpVar vs
               , storage_of_TupleStore     = dumpVar v
               , storageindir_of_TupleStore = case r of
                                       MemRegionStack      -> False
                                       MemRegionGlobalHeap -> True
                                       MemRegionGlobalData -> error $ "should not tuple-store to global data!"
    }
dumpTupleStore other = error $ "dumpTupleStore called on non-tuple-store value: " ++ show other

dumpLetVal :: Ident -> IL.Letable TypeLL -> MayGC -> FC.LetVal
dumpLetVal id letable maygc =
  LetVal { letvalid_of_LetVal = dumpIdent id
         , letexpr_of_LetVal  = dumpExpr maygc letable
         }

defaultTerminator tag =     Terminator {
          tag_of_Terminator   = tag
        , var_of_Terminator   = StrictlyNone
        , block_of_Terminator = StrictlyNone
        , scase_of_Terminator = StrictlyNone
        , args_of_Terminator  = []
    }

dumpLast :: ILLast -> FC.Terminator
dumpLast ILRetVoid = defaultTerminator Blockretvoid
dumpLast (ILRet var) =
    (defaultTerminator Blockretval) { var_of_Terminator = StrictlyJust $ dumpVar var }
dumpLast (ILBr blockid args) =
    (defaultTerminator Blockbr) {
        block_of_Terminator = StrictlyJust $ dumpBlockId blockid,
        args_of_Terminator  = map dumpVar args }
dumpLast (ILCase var arms def) =
    (defaultTerminator Blockcase) {
        scase_of_Terminator = StrictlyJust $ dumpSwitch var arms def }

dumpSwitch var arms def =
    let (ctors, ids) = Prelude.unzip arms in
    PbSwitch { ctors_of_PbSwitch   = map (dumpCtorIdWithRepr "dumpSwitch") ctors
             , blocks_of_PbSwitch  = map dumpBlockId ids
             , defCase_of_PbSwitch = strictMB $ fmap dumpBlockId def
             , var_of_PbSwitch     = dumpVar var
             , ctorby_of_PbSwitch  = StrictlyJust $ u8fromString $ determineHowToFindObjectCtor ctors
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
defaultLetable ty tag =
    Letable {
          parts_of_Letable       = []
        , tag_of_Letable         = tag
        , type_of_Letable        = StrictlyJust (dumpType ty)
        , names_of_Letable       = []
        , pbint_of_Letable       = StrictlyNone
        , dval_of_Letable        = []
        , boolvalue_of_Letable   = []
        , bytesvalue_of_Letable  = StrictlyNone
        , stringvalue_of_Letable = StrictlyNone
        , allocinfo_of_Letable   = StrictlyNone
        , callinfo_of_Letable    = StrictlyNone
        , callasm_of_Letable     = StrictlyNone
        , occ_of_Letable         = StrictlyNone
        , primopname_of_Letable  = StrictlyNone
        , primopsize_of_Letable  = []
        , ctorinfo_of_Letable    = StrictlyNone
        , arraylit_of_Letable    = StrictlyNone
        , sourceloc_of_Letable   = StrictlyNone
    }

dumpLiteral ty lit =
  case lit of
    LitBool  b -> (defaultLetable ty Ilbool) { boolvalue_of_Letable = [b] }
    LitText  t -> (defaultLetable ty Iltext) {
                        stringvalue_of_Letable = StrictlyJust $ u8fromText t }
    LitInt int -> (defaultLetable ty Ilint) {
                            pbint_of_Letable = StrictlyJust $ mkPbInt ty int }
    LitFloat f -> (defaultLetable ty Ilfloat) {
                            dval_of_Letable = [litFloatValue f] }

    LitByteArray a -> (defaultLetable ty Ilbytearray) {
                                    bytesvalue_of_Letable = StrictlyJust $ a }

mkPbInt ty int = PBInt { clean_of_PBInt = u8fromString (show $ litIntValue int)
                       , bits_of_PBInt  = fromIntegral (fixnumTypeSize ty) }

fixnumTypeSize (LLPrimInt IWd) = (-32)
fixnumTypeSize (LLPrimInt IDw) = (-64)
fixnumTypeSize (LLPrimInt isb) = intSizeOf isb
fixnumTypeSize other = error $ "Expected int literal to have LLPrimInt type; had " ++ show other

isTraced ty = case ty of
  LLPtrType _ -> True
  LLPtrTypeUnknown -> True
  _ -> False

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

sourceLoc (MissingSourceRange msg) =
    SourceLocation 0 0 (u8fromString msg)
sourceLoc (SourceRange startline startcol _ _ _ mb_file) =
  let msg = case mb_file of
              Just f  -> f
              Nothing -> ""
  in
    SourceLocation (fromIntegral startline) (fromIntegral startcol) (u8fromString msg)

-- |||||||||||||||||||||||| Expressions |||||||||||||||||||||||||{{{
dumpExpr :: MayGC -> IL.Letable TypeLL -> FC.Letable
dumpExpr _ (ILAlloc    {}) = error "ILAlloc should have been translated away!"
dumpExpr _ (ILBitcast t v) =
    (defaultLetable t Ilbitcast) { parts_of_Letable = [dumpVar v] }
dumpExpr _ (ILLiteral ty lit) = dumpLiteral ty lit
dumpExpr _ x@(ILKillProcess _ msg) =
    (defaultLetable (typeOf x) Ilkillprocess) {
            stringvalue_of_Letable = StrictlyJust $ u8fromText msg }
dumpExpr _ x@(ILTuple _kindTODO [] _allocsrc) =
    (defaultLetable (typeOf x) Ilunit) { type_of_Letable = StrictlyNone }
dumpExpr _ x@(ILTuple KindAnySizeType vs _allocsrc) =
    (defaultLetable (typeOf x) Ilunboxedtuple) { parts_of_Letable = map dumpVar vs, type_of_Letable = StrictlyNone }
dumpExpr _ (ILTuple _kind vs allocsrc) =
        error $ "CapnpIL.hs: ILTuple " ++ show vs
            ++ "\n should have been eliminated!\n" ++ show allocsrc

dumpExpr _ (ILOccurrence t v occ) =
    (defaultLetable t Iloccurrence) { occ_of_Letable = StrictlyJust $ dumpOccurrence v occ }

dumpExpr _ (ILAllocate info sr) =
    (defaultLetable (allocType info) Ilallocate) {
        allocinfo_of_Letable = StrictlyJust $ dumpAllocate info,
        sourceloc_of_Letable = StrictlyJust $ sourceLoc sr  }

dumpExpr _  (ILAllocArray (LLArrayType elt_ty) size memregion zeroinit sr) =
    (defaultLetable  elt_ty Ilallocate) {
        allocinfo_of_Letable = StrictlyJust $ dumpAllocate
                       (AllocInfo elt_ty memregion "xarrayx"
                                  Nothing (Just size)  "...array..." zeroinit),
        sourceloc_of_Letable = StrictlyJust $ sourceLoc sr }

dumpExpr _  (ILAllocArray nonArrayType _ _ _ _sr) =
         error $ "CapnpIL.hs: Can't dump ILAllocArray with non-array type "
              ++ show nonArrayType

dumpExpr _ x@(ILDeref ty a) =
    (defaultLetable (typeOf x) Ilderef) { parts_of_Letable = [dumpVar a]
                                        , boolvalue_of_Letable = [isTraced ty]
                                        , type_of_Letable = StrictlyNone }

-- The boolvalue for Deref and Store is used to determine whether loads/stores
-- should use LLVM's gcread/gcwrite primitives or regular, non-barriered ops.
dumpExpr _ x@(ILStore v r) =
    (defaultLetable (typeOf x) Ilstore) { parts_of_Letable = map dumpVar [v, r]
                                        , boolvalue_of_Letable = [isTraced (tidType v)]
                                        , type_of_Letable = StrictlyNone }

dumpExpr _ x@(ILArrayRead _t (ArrayIndex b i rng sg)) =
    (defaultLetable (typeOf x) Ilarrayread) {
          parts_of_Letable = map dumpVar [b, i]
        , stringvalue_of_Letable = StrictlyJust $ stringSG sg
        , primopname_of_Letable = StrictlyJust $ u8fromString $ highlightFirstLine rng }

dumpExpr _ x@(ILArrayPoke (ArrayIndex b i rng sg) v) =
    (defaultLetable (typeOf x) Ilarraypoke) {
          parts_of_Letable = map dumpVar [b, i, v]
        , stringvalue_of_Letable = StrictlyJust $ stringSG sg
        , primopname_of_Letable = StrictlyJust $ u8fromString $ highlightFirstLine rng }

dumpExpr _ _x@(ILArrayLit ty@(LLArrayType ety) arr vals) =
      (defaultLetable ty Ilarrayliteral) {
        parts_of_Letable = [dumpVar arr]
      , arraylit_of_Letable = StrictlyJust $ pbArrayLit ety vals
      }

dumpExpr _ (ILArrayLit otherty _arr _vals) =
    error $ "dumpExpr saw array literal with non-array type " ++ show otherty


dumpExpr maygc (ILCall t base args)
        = dumpCall t (dumpVar base)          args maygc ccs
  where stringOfCC FastCC = "fastcc"
        stringOfCC CCC    = "ccc"
        ccs = stringOfCC $ extractCallConv (tidType base)

dumpExpr _ (ILCallPrim t (NamedPrim (TypedId _ (GlobalSymbol gs _))) [arr])
        | gs == T.pack "prim_arrayLength"
        = dumpArrayLength t arr

dumpExpr _ (ILCallPrim t (PrimInlineAsm fty contents constraints sideeffects) args)
        =
    let (d, r, cc) = case fty of
         LLPtrType (LLStructType [LLProcType (_:d) r cc, _]) -> (d,r,cc)
         _ -> error $ "dumpExpr for inline asm expected fn type on inline asm"
       in
    (defaultLetable t Ilcall) { parts_of_Letable = map dumpVar args,
        callasm_of_Letable = StrictlyJust $     PbCallAsm {
              hassideeffects_of_PbCallAsm = sideeffects
            , asmcontents_of_PbCallAsm = u8fromString (T.unpack contents)
            , constraints_of_PbCallAsm = u8fromString (T.unpack constraints)
            , asmproctype_of_PbCallAsm = dumpProcType (d, r, cc)
        } }

dumpExpr maygc (ILCallPrim t (NamedPrim base) args)
        = dumpCall t (dumpGlobalSymbol base) args maygc "ccc"

dumpExpr _ (ILCallPrim t (LookupEffectHandler tag) _args)
        = (defaultLetable t Ilcallprimop) {
            primopname_of_Letable = StrictlyJust $ u8fromString "lookup_handler_for_effect",
            primopsize_of_Letable = [fromIntegral tag]
        }

dumpExpr _ (ILCallPrim t (PrimOp op _ty) args)
        = dumpCallPrimOp t op args

dumpExpr _ (ILCallPrim t (CoroPrim coroPrim argty retty) args)
        = dumpCallCoroOp t coroPrim argty retty args True

dumpExpr _ (ILCallPrim t (PrimIntTrunc _from to) args)
        = dumpCallPrimOp t (truncOp to) args
  where truncOp I1  = "trunc_i1"
        truncOp I8  = "trunc_i8"
        truncOp I16 = "trunc_i16"
        truncOp I32 = "trunc_i32"
        truncOp I64 = "trunc_i64"
        truncOp IWd = "trunc_w0"
        truncOp IDw = "trunc_w1"

dumpExpr _ (ILAppCtor _ _cinfo _ _sr) = error $ "CapnpIL.hs saw ILAppCtor, which"
                                       ++ " should have been translated away..."

-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||||||||||| Calls ||||||||||||||||||||||||||{{{
dumpCall :: TypeLL -> TermVar -> [TypedId TypeLL] -> MayGC -> String -> FC.Letable
dumpCall t base args maygc callConv =
    (defaultLetable t Ilcall) {
        parts_of_Letable = base : map dumpVar args,
        callinfo_of_Letable = StrictlyJust $ dumpCallInfo (boolGC maygc) callConv Nothing
    }


dumpCallInfo mayGC strCallConv pbCoroPrim =
    PbCallInfo {
          coroprim_of_PbCallInfo = strictMB $ pbCoroPrim
        , callmaytriggergc_of_PbCallInfo = mayGC
        , callisatailcall_of_PbCallInfo = False -- [1]
        , callconv_of_PbCallInfo = u8fromString strCallConv
    }
-- [1] To be safe, a tail call must not pass any pointers into the caller's
--     stack frame, because the caller's stack frame would become
--     the callee's stack frame. Since we don't do that analysis yet,
--     we provide a conservative default. But note that we've already
--     eliminated tail *recursion*.

dumpCallPrimOp t op args = -- TODO actually use prim_op_size from C++ side.
    (defaultLetable t Ilcallprimop) {
        parts_of_Letable = map dumpVar args,
        primopname_of_Letable = StrictlyJust $ u8fromString op
    }

dumpCallCoroOp t coroPrim argty retty args mayGC =
    (defaultLetable t Ilcall) {
        parts_of_Letable = map dumpVar args,
        callinfo_of_Letable = StrictlyJust $ dumpCallInfo mayGC callConv pbCoroPrim
    }
    where
        callConv = case coroPrim of
                     CoroIsDead -> "ccc"
                     _          -> "fastcc"
        pbCoroPrim = Just $     PbCoroPrim {
                                  tag_of_PbCoroPrim = coroFnTag coroPrim
                                , rettype_of_PbCoroPrim = dumpType retty
                                , argtype_of_PbCoroPrim = dumpType argty
                            }
        coroFnTag CoroInvoke = Ilcoroinvoke
        coroFnTag CoroCreate = Ilcorocreate
        coroFnTag CoroParent = Ilcoroparent
        coroFnTag CoroYield  = Ilcoroyield
        coroFnTag CoroIsDead = Ilcoroisdead

dumpArrayLength t arr =
    (defaultLetable t Ilarraylength) { parts_of_Letable = [dumpVar arr] }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

-- ||||||||||||||||||||| Other Expressions ||||||||||||||||||||||{{{
dumpCtorInfo (LLCtorInfo cid repr tys _) =
    PbCtorInfo {
          ctorid_of_PbCtorInfo = dumpCtorIdWithRepr "dumpCtorInfo" (cid, repr)
        , ctorstructty_of_PbCtorInfo =  if null tys
                            then StrictlyNone
                            else StrictlyJust $ dumpType (LLStructType tys)
    }

dumpCtorIdWithRepr from (CtorId dtn dtcn _arity, repr) =
    PbCtorId {
          ctortypename_of_PbCtorId = u8fromString dtn
        , ctorctorname_of_PbCtorId = u8fromString dtcn
        , ctorrepr_of_PbCtorId = dumpCtorRepr from repr
    }

dumpOccurrence var offsCtorInfos =
    let (offs, infos) = unzip offsCtorInfos in
    PbOccurrence {
          scrutinee_of_PbOccurrence = dumpVar var
        , occoffset_of_PbOccurrence = map fromIntegral offs
        , occctors_of_PbOccurrence  = map dumpCtorInfo infos
    }

dumpCtorRepr _ (CR_Tagged 0) =
    PbCtorRepr {
          tag_of_PbCtorRepr         = Crdefault
        , ctorreprtag_of_PbCtorRepr = [0]
        , isboxed_of_PbCtorRepr     = []
    }
dumpCtorRepr _ (CR_Tagged _) = error $ "Runtime can't yet handle non-zero pointer tags."

dumpCtorRepr _ (CR_Default ciid) =
    PbCtorRepr {
          tag_of_PbCtorRepr         = Crdefault
        , ctorreprtag_of_PbCtorRepr = [fromIntegral ciid]
        , isboxed_of_PbCtorRepr     = []
    }
dumpCtorRepr _ (CR_Transparent) =
    PbCtorRepr {
          tag_of_PbCtorRepr         = Crtransparent
        , ctorreprtag_of_PbCtorRepr = []
        , isboxed_of_PbCtorRepr     = []
    }

dumpCtorRepr _ (CR_TransparentU) =
    PbCtorRepr {
          tag_of_PbCtorRepr         = Crtransparent
        , ctorreprtag_of_PbCtorRepr = []
        , isboxed_of_PbCtorRepr     = [False]
    }

dumpCtorRepr _ (CR_Nullary ciid) =
    PbCtorRepr {
          tag_of_PbCtorRepr         = Crnullary
        , ctorreprtag_of_PbCtorRepr = [fromIntegral ciid]
        , isboxed_of_PbCtorRepr     = []
    }

dumpCtorRepr _ (CR_Value ciid) =
    PbCtorRepr {
          tag_of_PbCtorRepr         = Crvalue
        , ctorreprtag_of_PbCtorRepr = [fromIntegral ciid]
        , isboxed_of_PbCtorRepr     = []
    }

-----------------------------------------------------------------------

pbArrayLit ety vals =
  PbArrayLiteral {
    elemtype_of_PbArrayLiteral = dumpType ety
  , entries_of_PbArrayLiteral = map dumpArrayValue vals
  }
 where
  dumpArrayValue (Right var) = PbArrayEntry { var_of_PbArrayEntry = StrictlyJust $ dumpVar var
                                            , lit_of_PbArrayEntry = StrictlyNone }
  dumpArrayValue (Left lit)  = PbArrayEntry { var_of_PbArrayEntry = StrictlyNone,
                                              lit_of_PbArrayEntry = StrictlyJust $ dumpLiteral ety lit }

-----------------------------------------------------------------------
dumpVar (TypedId t i) = dumpMoVar t i False
dumpVar' (TypedId t i) = dumpMoVar t i True
-- Most uses of variables don't need explicit types during LLVM codegen
-- with a few exceptions for root slots and phi arguments.
-- By eliding types for most varaibles we save ~20% file size
-- for some programs.

dumpGlobalSymbol base =
    TermVar {
          tag_of_TermVar  = Ilglobalsymbol
        , name_of_TermVar = dumpIdent (tidIdent base)
        , typ_of_TermVar  = StrictlyJust $ dumpType (tidType base)
    }

dumpMoVar t i@(GlobalSymbol {}) _ = dumpGlobalSymbol (TypedId t i)
dumpMoVar t i useType =
    TermVar {
          tag_of_TermVar  = Ilvar
        , name_of_TermVar = dumpIdent i
        , typ_of_TermVar  = if useType
                             then StrictlyJust $ dumpType t
                             else StrictlyNone
    }
dumpVarIdent i =
    TermVar {
          tag_of_TermVar  = Ilvar
        , name_of_TermVar = dumpIdent i
        , typ_of_TermVar  = StrictlyNone
    }
-- }}}||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||||

dumpILProgramToCapnp :: ILProgram -> FilePath -> IO ()
dumpILProgramToCapnp m outpath = do
    bytes <- srModule (dumpProgramToModule m)
    BS.writeFile outpath bytes

dumpProgramToModule :: ILProgram -> Module
dumpProgramToModule (ILProgram procdefs vals extern_decls datatypes (SourceLines lines))
    = Module {
          modulename_of_Module     = u8fromString $ "foo539hmm"
        , procs_of_Module          = map dumpProc procdefs
        , items_of_Module          = map dumpItem vals
        , externvaldecls_of_Module = map dumpDecl extern_decls
        , typdecls_of_Module       = map dumpDataTypeDecl datatypes
        , modlines_of_Module       = map u8fromText (toList lines)
    }
  where
    dumpProc (ILProcDef p predmap gcroots)
      = Proc {
              proctype_of_Proc = dumpProcType (preProcType p)
            , inargs_of_Proc   = [dumpIdent (tidIdent v) | v <- CC.procVars p]
            , name_of_Proc     = dumpIdent $ CC.procIdent p
            , blocks_of_Proc   = map (dumpBlock predmap) (CC.procBlocks p)
            , lines_of_Proc    = StrictlyJust $ u8fromString (showSourceRange . rangeOf $ CC.procAnnot p)
            , linkage_of_Proc  = Internal
            , gcroots_of_Proc  = map dumpVar' gcroots
        }
    preProcType proc =
        let retty = CC.procReturnType proc in
        let argtys = map tidType (CC.procVars proc) in
        (argtys, retty, FastCC)

    dumpItem :: ToplevelBinding TypeLL -> PbToplevelItem
    dumpItem (TopBindArray id _ty@(LLArrayType ety) lits) =
      PbToplevelItem {
          name_of_PbToplevelItem = dumpIdent id
        , arr_of_PbToplevelItem = StrictlyJust $ pbArrayLit ety (map Left lits)
        , lit_of_PbToplevelItem = StrictlyNone
        }

    dumpItem (TopBindArray _id otherty _lits) =
        error $ "dumpItem saw top-level array with non-array type " ++ show otherty

    dumpItem (TopBindLiteral id ty lit) =
      PbToplevelItem {
          name_of_PbToplevelItem = dumpIdent id
        , lit_of_PbToplevelItem = StrictlyJust $ dumpLiteral ty lit
        , arr_of_PbToplevelItem = StrictlyNone
        }

    dumpItem (TopBindTuple id refty@(LLPtrType unboxedty) ids) =
      PbToplevelItem {
          name_of_PbToplevelItem = dumpIdent id
        , lit_of_PbToplevelItem = StrictlyJust $
              (defaultLetable unboxedty Ilunboxedtuple) { parts_of_Letable = map dumpVarIdent ids }
              -- hacky detail: we use the presence of the type field to mean "static/global"
        , arr_of_PbToplevelItem = StrictlyNone
        }

    dumpItem (TopBindAppCtor id ty (cid, repr) ids) =
      PbToplevelItem {
          name_of_PbToplevelItem = dumpIdent id
        , lit_of_PbToplevelItem = StrictlyJust $
              (defaultLetable ty Ilglobalappctor) { parts_of_Letable = map dumpVarIdent ids
                                                  , ctorinfo_of_Letable = StrictlyJust $ 
                        PbCtorInfo {
                              ctorid_of_PbCtorInfo = dumpCtorIdWithRepr "dumpCtorInfo" (cid, repr)
                            , ctorstructty_of_PbCtorInfo = StrictlyNone
                        }
              }
        , arr_of_PbToplevelItem = StrictlyNone
      }

    dumpDataTypeDecl :: DataType TypeLL -> Decl
    dumpDataTypeDecl datatype =
        let formal = dataTypeName datatype in
        Decl { name_of_Decl = u8fromString (typeFormalName formal)
             , type_of_Decl = dumpDataType formal (dataTypeCtors datatype)
             , isForeign_of_Decl = False
             }

    dumpDecl (LLExternDecl s t NotForeign) =
        Decl { name_of_Decl = u8fromString s
             , type_of_Decl = dumpType t
             , isForeign_of_Decl = False
             }

    dumpDecl (LLExternDecl _x t (IsForeign s)) =
        Decl { name_of_Decl = u8fromString s
             , type_of_Decl = dumpType t
             , isForeign_of_Decl = True
             }

    dumpDataType (TypeFormal dtName _sr KindEffect) _ctors =
        Type_ {
              tag_of_Type_ = Datatype
            , name_of_Type_ = StrictlyJust $ u8fromString dtName
            , procty_of_Type_ = StrictlyNone
            , typeparts_of_Type_ = []
            , carraysize_of_Type_ = []
            , ctor_of_Type_ = []
        }

    dumpDataType (TypeFormal dtName _sr KindPointerSized) ctors =
        Type_ {
              tag_of_Type_ = Datatype
            , name_of_Type_ = StrictlyJust $ u8fromString dtName
            , procty_of_Type_ = StrictlyNone
            , typeparts_of_Type_ = []
            , carraysize_of_Type_ = []
            , ctor_of_Type_ = map dumpDataCtor ctors
        }
     where
        dumpDataCtor (DataCtor ctorName _tyformals types _repr _lone _range) =
          PbDataCtor { name_of_PbDataCtor = u8fromText ctorName
                     , type_of_PbDataCtor = map dumpType types
                     }

    dumpDataType (TypeFormal _dtName _sr KindAnySizeType) [DataCtor _nm [] [ty] _repr _lone _range] =
        dumpType ty

    dumpDataType (TypeFormal _dtName _sr KindAnySizeType) [DataCtor _nm []  tys _repr _lone _range] =
        dumpType (LLStructType tys)

    dumpDataType (TypeFormal dtName _sr kind) ctors =
            error $ "CapnpIL.hs: Don't yet know how to handle " ++ dtName ++ " : " ++ show kind ++ " , with ctors..." ++ show ctors



