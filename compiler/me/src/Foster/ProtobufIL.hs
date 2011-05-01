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
import Foster.TypeAST

import Data.Maybe(isJust)

import qualified Data.Text as T
import qualified Data.ByteString.Lazy as L(writeFile)
import Data.ByteString.Lazy.UTF8 as UTF8
import Data.Sequence as Seq

import Text.ProtocolBuffers(messagePut)

import Foster.Bepb.ProcType as ProcType
import Foster.Bepb.Type.Tag as PbTypeTag
import Foster.Bepb.Type     as PbType
import Foster.Bepb.Closure  as Closure
import Foster.Bepb.Proc     as Proc
import Foster.Bepb.PBIf     as PBIf
import Foster.Bepb.PBInt    as PBInt
import Foster.Bepb.Expr     as PbExpr
import Foster.Bepb.CoroPrim as PbCoroPrim
import Foster.Bepb.Module   as Module
import Foster.Bepb.Expr.Tag

import qualified Text.ProtocolBuffers.Header as P'

-- Simple conversions

textToPUtf8 :: T.Text -> P'.Utf8
textToPUtf8 t = u8fromString $ T.unpack t

-- uToString :: P'.Utf8 -> String

u8fromString :: String -> P'.Utf8
u8fromString s = P'.Utf8 (UTF8.fromString s)

intToInt32 :: Int -> P'.Int32
intToInt32 i = (fromInteger (toInteger i))

-----------------------------------------------------------------------

identFullString :: Ident -> String
identFullString = show

-- Primitive values have minimal C-level name mangling, at the moment...
dumpIdent :: Ident -> P'.Utf8
dumpIdent i = let p = identPrefix i in
              if (isJust $ lookup p rootContextPairs) || identNum i < 0
                then u8fromString $ identPrefix i
                else u8fromString $ identFullString i

-----------------------------------------------------------------------

tagForClosedVars Nothing  = PbTypeTag.PROC
tagForClosedVars (Just _) = PbTypeTag.CLOSURE

dumpType :: TypeAST -> PbType.Type
dumpType (NamedTypeAST s)     = P'.defaultValue { PbType.tag  = PbTypeTag.LLVM_NAMED
                                                , PbType.name = Just $ u8fromString s }
dumpType (TupleTypeAST types) = P'.defaultValue { PbType.tag  = PbTypeTag.TUPLE
                                                ,  type_parts = fromList $ fmap dumpType types }
dumpType x@(FnTypeAST s t cs) = P'.defaultValue { PbType.tag  = tagForClosedVars cs
                                                , PbType.procty = Just $ dumpProcType x
                                                }
dumpType x@(CoroType a b)     = P'.defaultValue { PbType.tag  = PbTypeTag.CORO
                                                ,  type_parts = fromList $ fmap dumpType [a,b] }

dumpType x@(ForAll tyvars ty) = let tyVarName tv = case tv of
                                                    BoundTyVar nm -> u8fromString nm
                                                    SkolemTyVar s u -> error $ "dumpType (Forall ...) saw skolem var " ++ s
                                in
                                P'.defaultValue { PbType.tag  = PbTypeTag.FORALL_TY
                                                ,  type_parts = fromList $ fmap dumpType [ty]
                                                , tyvar_names = fromList $ fmap tyVarName tyvars }
dumpType x@(T_TyVar (BoundTyVar s)) =
                                P'.defaultValue { PbType.tag  = PbTypeTag.TYPE_VARIABLE
                                                , PbType.name = Just $ u8fromString s
                                                }

dumpType x@(PtrTypeAST ty) =    P'.defaultValue { PbType.tag = PbTypeTag.PTR
                                                , type_parts = fromList $ fmap dumpType [ty]
                                                }
dumpType other = error $ "dumpType saw unknown type " ++ show other

defaultCallingConvFor Nothing = "coldcc"
defaultCallingConvFor (Just _) = "fastcc"

dumpProcType (FnTypeAST s t cs) =
    let args = case s of
                TupleTypeAST types -> [dumpType x | x <- types]
                otherwise          -> [dumpType s]
    in
    ProcType.ProcType {
          arg_types = fromList args
        , ProcType.ret_type  = dumpType t
        , calling_convention = Just $ u8fromString (defaultCallingConvFor cs)
    }
dumpProcType other = error $ "dumpProcType called with non-FnTypeAST node! " ++ show other

-----------------------------------------------------------------------
-----------------------------------------------------------------------

dumpExpr :: ILExpr -> PbExpr.Expr

dumpExpr (ILCall t base args) = dumpCall t base args

dumpExpr x@(ILBool b) =
    P'.defaultValue { bool_value   = Just b
                    , PbExpr.tag   = IL_BOOL
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr (ILVar (AnnVar t i)) =
    P'.defaultValue { PbExpr.name  = Just $ dumpIdent i
                    , PbExpr.tag   = IL_VAR
                    , PbExpr.type' = Just $ dumpType t  }

dumpExpr x@(ILTuple vs) =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr $ ILVar v | v <- vs]
                    , PbExpr.tag   = IL_TUPLE
                    , PbExpr.type' = Just $ dumpType (typeIL x)  }

dumpExpr x@(ILSubscript t a b ) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [ILVar a, b])
                    , PbExpr.tag   = IL_SUBSCRIPT
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

dumpExpr x@(ILTyApp overallTy (ILVar (AnnVar _ (Ident corofn _)))
                    (TupleTypeAST [argty, retty]))
          | corofn == "coro_invoke" || corofn == "coro_create" =
    P'.defaultValue { PbExpr.tag   = coroFnTag corofn
                    , PbExpr.coro_prim = Just $ P'.defaultValue    {
                              PbCoroPrim.ret_type = dumpType retty ,
                              PbCoroPrim.arg_type = dumpType argty }
                    }

dumpExpr x@(ILTyApp overallTy baseExpr argType) =
    error $ "Unable to dump type application node " ++ show x
          ++ " (should handle substitution before codegen)."

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

coroFnTag "coro_invoke" = IL_CORO_INVOKE
coroFnTag "coro_create" = IL_CORO_CREATE
coroFnTag "coro_yield"  = IL_CORO_YIELD
coroFnTag other = error $ "Unknown coro primitive: " ++ other

unzipLetVals :: ILExpr -> (ILExpr, [P'.Utf8], [ILExpr])
unzipLetVals (ILLetVal x a b) =
        let (e, nms, vals) = unzipLetVals b in
        ( e , (dumpIdent x):nms , a:vals )
unzipLetVals e = (e, [], [])

dumpClosureWithName (varid, ILClosure procid captvars) =
    Closure { varname  = dumpIdent varid
            , procid   = u8fromString (identPrefix procid)
            , varnames = fromList (fmap (dumpIdent.avarIdent) captvars) }

-----------------------------------------------------------------------

dumpCall t base args =
    P'.defaultValue { PbExpr.parts = fromList $ fmap (\v -> dumpExpr (ILVar v)) (base : args)
                    , PbExpr.tag   = IL_CALL
                    , PbExpr.type' = Just $ dumpType t }

dumpIf x@(ILIf t v b c) =
        PBIf { test_expr = dumpExpr (ILVar v), then_expr = dumpExpr b, else_expr = dumpExpr c }
dumpIf other = error $ "dumpIf called with non-ILIf node: " ++ show other

dumpInt cleanText activeBits =
        PBInt.PBInt { clean = u8fromString cleanText
                    , bits  = intToInt32   activeBits }

dumpVar (AnnVar t ident) =
    P'.defaultValue { PbExpr.name  = Just $ dumpIdent ident
                    , PbExpr.tag   = IL_VAR
                    , PbExpr.type' = Just $ dumpType t  }


dumpProc p =
    Proc { Proc.name  = dumpIdent (ilProcIdent p)
         , in_args    = fromList $ [dumpIdent (avarIdent v) | v <- (ilProcVars p)]
         , proctype   = dumpProcType (procType p)
         , Proc.body  = Just $ dumpExpr (ilProcBody p)
         }

-----------------------------------------------------------------------

dumpProgramToModule :: ILProgram -> Module
dumpProgramToModule (ILProgram procdefs) =
    Module   { modulename = u8fromString $ "foo"
             , procs      = fromList [dumpProc p | p <- procdefs]
             }

dumpModuleToProtobufIL :: ILProgram -> FilePath -> IO ()
dumpModuleToProtobufIL mod outpath = do
    let llmod = dumpProgramToModule mod
    L.writeFile outpath (messagePut llmod)
    return ()

