-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufLL (
  dumpModuleToProtobufLL
) where

import Foster.Base
import Foster.LLExpr
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
dumpIdent :: Ident -> String
dumpIdent i = let p = identPrefix i in
              if (isJust $ lookup p rootContextPairs) || identNum i < 0
                then identPrefix i
                else identFullString i

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

dumpExpr :: LLExpr -> PbExpr.Expr

dumpExpr (LLCall t base args) = dumpCall t base args

dumpExpr x@(LLBool b) =
    P'.defaultValue { bool_value   = Just b
                    , PbExpr.tag   = LL_BOOL
                    , PbExpr.type' = Just $ dumpType (typeLL x)  }

dumpExpr (LLVar (AnnVar t i)) =
    P'.defaultValue { PbExpr.name  = Just $ u8fromString (dumpIdent i)
                    , PbExpr.tag   = LL_VAR
                    , PbExpr.type' = Just $ dumpType t  }

dumpExpr x@(LLSeq a b) = dumpSeqOf (unbuildSeqsLL x) (typeLL x)

dumpExpr x@(LLTuple es) =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr e | e <- es]
                    , PbExpr.tag   = LL_TUPLE
                    , PbExpr.type' = Just $ dumpType (typeLL x)  }

dumpExpr x@(LLSubscript t a b ) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [LLVar a, b])
                    , PbExpr.tag   = LL_SUBSCRIPT
                    , PbExpr.type' = Just $ dumpType (typeLL x)  }

dumpExpr x@(LLInt ty int) =
    P'.defaultValue { PbExpr.pb_int = Just $ dumpInt (show $ litIntValue int)
                                                     (litIntMinBits int)
                    , PbExpr.tag   = LL_INT
                    , PbExpr.type' = Just $ dumpType (typeLL x)  }

dumpExpr x@(LLIf t a b c) =
    P'.defaultValue { pb_if        = Just (dumpIf $ x)
                    , PbExpr.tag   = LL_IF
                    , PbExpr.type' = Just $ dumpType (typeLL x) }

dumpExpr x@(LLTyApp overallTy baseExpr argType) =
    P'.defaultValue { PbExpr.ty_app_arg_type = Just $ dumpType argType
                    , PbExpr.parts = fromList (fmap dumpExpr [baseExpr])
                    , PbExpr.tag   = LL_TY_APP
                    , PbExpr.type' = Just $ dumpType overallTy }

dumpExpr x@(LLClosures ty closures expr) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [expr])
                    , PbExpr.tag   = LL_CLOSURES
                    , PbExpr.closures = fromList (fmap dumpClosureWithName closures)
                    , PbExpr.type' = Just $ dumpType (typeLL expr) }

dumpExpr (LLLetVal t x a b) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [a, b])
                    , PbExpr.tag   = LL_LETVAL
                    , PbExpr.name  = Just $ u8fromString (dumpIdent $ avarIdent x)
                    , PbExpr.type' = Just $ dumpType t }

dumpClosureWithName (varid, LLClosure procid idents) =
    Closure { varname  = u8fromString (dumpIdent   varid)
            , procid   = u8fromString (identPrefix procid)
            , varnames = fromList (fmap u8fromString (fmap dumpIdent idents)) }

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

dumpSeqOf exprs ty =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr e | e <- exprs]
                    , PbExpr.tag   = LL_SEQ
                    , PbExpr.type' = Just $ dumpType ty  }

dumpCall t base args =
    P'.defaultValue { PbExpr.parts = fromList $ fmap (\v -> dumpExpr (LLVar v)) (base : args)
                    , PbExpr.tag   = LL_CALL
                    , PbExpr.type' = Just $ dumpType t }

dumpIf x@(LLIf t a b c) =
        PBIf { test_expr = dumpExpr a, then_expr = dumpExpr b, else_expr = dumpExpr c }

dumpInt cleanText activeBits =
        PBInt.PBInt { clean = u8fromString cleanText
                    , bits  = intToInt32   activeBits }

dumpProto p@(LLPrototype t ident formals callconv) =
    Proto { Proto.name  = u8fromString (dumpIdent ident)
          , in_args     = fromList $ [dumpVar e | e <- formals]
          , proctype    = dumpProcType (procTypeFromLLProto p)
          , Proto.range = Nothing }

dumpVar (AnnVar t ident) =
    P'.defaultValue { PbExpr.name  = Just $ u8fromString (dumpIdent ident)
                    , PbExpr.tag   = LL_VAR
                    , PbExpr.type' = Just $ dumpType t  }


dumpProc (LLProcDef proto body) =
    Proc { Proc.proto = dumpProto proto
         , Proc.body  = dumpExpr body
         }

-----------------------------------------------------------------------

dumpProgramToModule :: LLProgram -> Module
dumpProgramToModule (LLProgram procdefs) =
    Module   { modulename = u8fromString $ "foo"
             , protos     = fromList []
             , procs      = fromList [dumpProc p | p <- procdefs]
             }

dumpModuleToProtobufLL :: LLProgram -> FilePath -> IO ()
dumpModuleToProtobufLL mod outpath = do
    let llmod = dumpProgramToModule mod
    L.writeFile outpath (messagePut llmod)
    return ()

