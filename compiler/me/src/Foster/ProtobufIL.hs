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
import Foster.ExprAST
import Foster.TypeAST

import Debug.Trace(trace)

import Data.Traversable(fmapDefault)
import Data.Sequence(length, index, Seq, empty, fromList)
import Data.Maybe(fromMaybe, fromJust, isJust)
import Data.Foldable(toList)
import Data.Char(toLower)

import Control.Exception(assert)
import qualified Data.Text as T
import qualified Data.ByteString.Lazy as L(writeFile)
import Data.ByteString.Lazy.UTF8 as UTF8
import Data.Sequence as Seq

import Text.ProtocolBuffers(isSet,getVal,messagePut)
import Text.ProtocolBuffers.Basic(uToString)

import Foster.Bepb.ProcType as ProcType
import Foster.Bepb.Type.Tag as PbTypeTag
import Foster.Bepb.Type     as PbType
import Foster.Bepb.Proto    as Proto
import Foster.Bepb.Closure  as Closure
import Foster.Bepb.Proc     as Proc
import Foster.Bepb.PBIf     as PBIf
import Foster.Bepb.PBInt    as PBInt
import Foster.Bepb.Expr     as PbExpr
import Foster.Bepb.Module   as Module
import Foster.Bepb.Expr.Tag
import qualified Foster.Bepb.SourceRange as Pb
import qualified Foster.Bepb.SourceLocation as Pb

import qualified Text.ProtocolBuffers.Header as P'

-- String conversions

textToPUtf8 :: T.Text -> P'.Utf8
textToPUtf8 t = u8fromString $ T.unpack t

-- uToString :: P'.Utf8 -> String

u8fromString :: String -> P'.Utf8
u8fromString s = P'.Utf8 (UTF8.fromString s)

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
dumpType (MissingTypeAST s)   = error $ "dumpType MissingTypeAST " ++ s
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
        , ret_type  = dumpType t
        , calling_convention = Just $ u8fromString (defaultCallingConvFor cs)
    }

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

dumpExpr x@(ILTuple es) =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr e | e <- es]
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

dumpExpr x@(ILTyApp overallTy baseExpr argType) =
    P'.defaultValue { PbExpr.ty_app_arg_type = Just $ dumpType argType
                    , PbExpr.parts = fromList (fmap dumpExpr [baseExpr])
                    , PbExpr.tag   = IL_TY_APP
                    , PbExpr.type' = Just $ dumpType overallTy }

dumpExpr x@(ILClosures ty closures expr) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [expr])
                    , PbExpr.tag   = IL_CLOSURES
                    , PbExpr.closures = fromList (fmap dumpClosureWithName closures)
                    , PbExpr.type' = Just $ dumpType (typeIL expr) }

dumpExpr (ILLetVal t x a b) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [a, b])
                    , PbExpr.tag   = IL_LETVAL
                    , PbExpr.name  = Just $ dumpIdent $ avarIdent x
                    , PbExpr.type' = Just $ dumpType t }

dumpClosureWithName (varid, ILClosure procid idents) =
    Closure { varname  = dumpIdent varid
            , procid   = u8fromString (identPrefix procid)
            , varnames = fromList (fmap dumpIdent idents) }

-----------------------------------------------------------------------
intToInt32 :: Int -> P'.Int32
intToInt32 i = (fromInteger (toInteger i))

dumpSourceLocation (ESourceLocation line col) =
    Pb.SourceLocation (intToInt32 line) (intToInt32 col)

dumpRange :: ESourceRange -> Maybe Pb.SourceRange
dumpRange (EMissingSourceRange s) = Nothing
dumpRange range =
    Just (Pb.SourceRange (fmap u8fromString $ sourceRangeFile  range)
                        (dumpSourceLocation $ sourceRangeBegin range)
                  (Just (dumpSourceLocation $ sourceRangeEnd   range)))
-----------------------------------------------------------------------

dumpCall t base args =
    P'.defaultValue { PbExpr.parts = fromList $ fmap (\v -> dumpExpr (ILVar v)) (base : args)
                    , PbExpr.tag   = IL_CALL
                    , PbExpr.type' = Just $ dumpType t }

dumpIf x@(ILIf t v b c) =
        PBIf { test_expr = dumpExpr (ILVar v), then_expr = dumpExpr b, else_expr = dumpExpr c }

dumpInt cleanText activeBits =
        PBInt.PBInt { clean = u8fromString cleanText
                    , bits  = intToInt32   activeBits }

dumpProto p@(ILPrototype t ident formals callconv) =
    Proto { Proto.name  = dumpIdent ident
          , in_args     = fromList $ [dumpIdent (avarIdent v) | v <- formals]
          , proctype    = dumpProcType (procTypeFromILProto p)
          , Proto.range = Nothing }

dumpVar (AnnVar t ident) =
    P'.defaultValue { PbExpr.name  = Just $ dumpIdent ident
                    , PbExpr.tag   = IL_VAR
                    , PbExpr.type' = Just $ dumpType t  }


dumpProc (ILProcDef proto body) =
    Proc { Proc.proto = dumpProto proto
         , Proc.body  = dumpExpr body
         }

-----------------------------------------------------------------------

dumpProgramToModule :: ILProgram -> Module
dumpProgramToModule (ILProgram procdefs) =
    Module   { modulename = u8fromString $ "foo"
             , protos     = fromList []
             , procs      = fromList [dumpProc p | p <- procdefs]
             }

dumpModuleToProtobufIL :: ILProgram -> FilePath -> IO ()
dumpModuleToProtobufIL mod outpath = do
    let llmod = dumpProgramToModule mod
    L.writeFile outpath (messagePut llmod)
    return ()

