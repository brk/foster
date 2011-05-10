-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufFE (
    parseSourceModule
) where

import Foster.Base
import Foster.ExprAST
import Foster.TypeAST

import Data.Traversable(fmapDefault)
import Data.Sequence as Seq
import Data.Sequence(length)
import Data.Maybe(fromMaybe, fromJust, isJust)
import Data.Foldable(toList)

import Control.Exception(assert)
import qualified Data.Text as T
import Data.ByteString.Lazy.UTF8 as UTF8

import Text.ProtocolBuffers(isSet,getVal)
import Text.ProtocolBuffers.Basic(uToString)

import Foster.Fepb.FnType   as PbFnType
import Foster.Fepb.Type.Tag as PbTypeTag
import Foster.Fepb.Type     as PbType
import Foster.Fepb.Proto    as Proto
import Foster.Fepb.PBIf     as PBIf
import Foster.Fepb.Expr     as PbExpr
import Foster.Fepb.SourceModule as SourceModule
import Foster.Fepb.Expr.Tag(Tag(PB_INT, BOOL, VAR, TUPLE, COMPILES, -- MODULE, TY_APP,
                                      IF, FN, LET, PROTO, CALL, SEQ, SUBSCRIPT))
import qualified Foster.Fepb.SourceRange as Pb
import qualified Foster.Fepb.SourceLocation as Pb

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

---------

-- hprotoc cheat sheet:
--
-- required string name         => (name person)
-- required int32 id            => (Person.id person)
-- optional string email        => (getVal person email)
-- optional PhoneType type      => (getVal phone_number type')
-----------------------------------------------------------------------

part :: Int -> Seq PbExpr.Expr -> SourceLines -> ExprAST
part i parts lines = parseExpr (index parts i) lines

parseBool pbexpr lines =
        let range = parseRange pbexpr lines in
        E_BoolAST range $ fromMaybe False (PbExpr.bool_value pbexpr)

parseCall pbexpr lines =
        let range = parseRange pbexpr lines in
        case map (\x -> parseExpr x lines) $ toList (PbExpr.parts pbexpr) of
                --[base, arg] -> CallAST range base arg
                (base:args) -> E_CallAST range base args
                _ -> error "call needs a base!"

parseCompiles pbexpr lines =
    let numChildren = Seq.length $ PbExpr.parts pbexpr in
    case numChildren of
        1 -> E_CompilesAST (part 0 (PbExpr.parts pbexpr) lines)      CS_NotChecked
        _ -> E_CompilesAST (E_VarAST (VarAST Nothing "parse error")) CS_WouldNotCompile

parseFn pbexpr lines = let range = parseRange pbexpr lines in
                       let parts = PbExpr.parts pbexpr in
                       let (name, retty, formals) = parseProtoP (index parts 0) lines in
                       assert ((Data.Sequence.length parts) == 2) $
                       FnAST range name retty formals
                             (part 1 parts lines)
                             False -- assume closure until proven otherwise
  where
     parseProtoP :: PbExpr.Expr -> SourceLines -> (String, TypeAST, [AnnVar])
     parseProtoP pbexpr lines =
         case PbExpr.proto pbexpr of
             Nothing     -> error "Need a Proto in the protocol buffer to parse a PrototypeAST!"
             Just proto  ->
                 let args = Proto.in_args proto in
                 let vars = map (\x -> getFormal x lines) $ toList args in
                 let name = uToString $ Proto.name proto in
                 let retTy = case Proto.result proto of
                                 Just t  -> parseType t
                                 Nothing -> error ("Prototype " ++ name ++ " missing required type annotation!") in
                    (name, retTy, vars)

parseFnAST pbexpr lines = E_FnAST (parseFn pbexpr lines)

parseIf pbexpr lines =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif =
               (E_IfAST (parseExpr (PBIf.test_expr pbif) lines)
                        (parseExpr (PBIf.then_expr pbif) lines)
                        (parseExpr (PBIf.else_expr pbif) lines))

parseInt :: PbExpr.Expr -> SourceLines -> ExprAST
parseInt pbexpr lines =
        let range = parseRange pbexpr lines in
        E_IntAST range (uToString $ getVal pbexpr PbExpr.int_text)

parseLet pbexpr lines =
    let range = parseRange pbexpr lines in
    let parts = PbExpr.parts pbexpr in
    let (E_VarAST var) = part 0 parts lines in
    (E_LetAST range var
              (part 1 parts lines)
              (part 2 parts lines)
              (Just $ getType pbexpr))

parseSeq pbexpr lines =
    let exprs = map (\x -> parseExpr x lines) $ toList (PbExpr.parts pbexpr) in
    buildSeqs exprs

-- | Convert a list of ExprASTs to a right-leaning "list" of SeqAST nodes.
buildSeqs :: [ExprAST] -> ExprAST
buildSeqs []    = E_TupleAST []
buildSeqs [a]   = a
buildSeqs [a,b] = E_SeqAST a b
buildSeqs (a:b) = E_SeqAST a (buildSeqs b)

parseSubscript pbexpr lines =
    let parts = PbExpr.parts pbexpr in
    E_SubscriptAST (part 0 parts lines) (part 1 parts lines)

parseTuple pbexpr lines =
    E_TupleAST (map (\x -> parseExpr x lines) $ toList $ PbExpr.parts pbexpr)


parseEVar pbexpr lines = E_VarAST (parseVar pbexpr lines)

parseVar pbexpr lines =  VarAST (fmap parseType (PbExpr.type' pbexpr))
                                (uToString (fromJust $ PbExpr.name pbexpr))

toplevel :: FnAST -> FnAST
toplevel (FnAST a b c d e False) = FnAST a b c d e True
toplevel (FnAST _ _ _ _ _ True ) =
        error $ "Broken invariant: top-level functions " ++
                "should not have their top-level bit set before we do it!"

parseModule :: PbExpr.Expr -> SourceLines -> ModuleAST FnAST
parseModule pbexpr lines =
    ModuleAST [toplevel (parseFn e lines) | e <- toList $ PbExpr.parts pbexpr]
              lines


getVarName :: ExprAST -> String
getVarName (E_VarAST v) = evarName v
getVarName x = error $ "getVarName given a non-variable! " ++ show x

getType :: PbExpr.Expr -> TypeAST
getType e = case PbExpr.type' e of
                Just t -> parseType t
                Nothing -> error $ "ProtobufUtils.getType " ++ show (PbExpr.tag e)

getFormal :: PbExpr.Expr -> SourceLines ->  AnnVar
getFormal e lines = case PbExpr.tag e of
            VAR -> let v = parseVar e lines in
                   let i = (Ident (evarName v) (54321)) in
                   case evarMaybeType v of
                       Just t  -> (AnnVar t i)
                       Nothing -> --(AnnVar (MissingTypeAST $ "ProtobufUtils.getFormal " ++ (evarName v)) i)
                                  error $ "Missing annotation on variable " ++ show v
            _   -> error "getVar must be given a var!"

sourceRangeFromPBRange :: Pb.SourceRange -> SourceLines -> ESourceRange
sourceRangeFromPBRange pbrange lines =
    ESourceRange
        (parseSourceLocation (Pb.begin pbrange))
        (parseSourceLocation (fromJust $ Pb.end   pbrange))
        lines
        (fmap uToString (Pb.file_path pbrange))

getString :: Maybe P'.Utf8 -> String
getString Nothing  = ""
getString (Just u) = uToString u

parseSourceLocation :: Pb.SourceLocation -> ESourceLocation
parseSourceLocation sr = -- This may fail for files of more than 2^29 lines...
    ESourceLocation (fromIntegral $ Pb.line sr) (fromIntegral $ Pb.column sr)

parseRange :: PbExpr.Expr -> SourceLines ->  ESourceRange
parseRange pbexpr lines = case PbExpr.range pbexpr of
                        Nothing   -> EMissingSourceRange (show $ PbExpr.tag pbexpr)
                        (Just r)  -> sourceRangeFromPBRange r lines

parseExpr :: PbExpr.Expr -> SourceLines -> ExprAST
parseExpr pbexpr lines =
    let range = parseRange pbexpr in
    let fn = case PbExpr.tag pbexpr of
                PB_INT  -> parseInt
                IF      -> parseIf
                BOOL    -> parseBool
                VAR     -> parseEVar
                Foster.Fepb.Expr.Tag.TUPLE   -> parseTuple
                Foster.Fepb.Expr.Tag.FN      -> parseFnAST
                PROTO   -> error $ "parseExpr cannot parse a standalone proto!" ++ (show $ PbExpr.tag pbexpr) ++ "\n"
                CALL      -> parseCall
                SEQ       -> parseSeq
                LET       -> parseLet
                COMPILES  -> parseCompiles
                SUBSCRIPT -> parseSubscript
                otherwise -> error $ "parseExpr saw unknown tag: " ++ (show $ PbExpr.tag pbexpr) ++ "\n"
        in
   fn pbexpr lines

parseSourceModule :: SourceModule -> ModuleAST FnAST
parseSourceModule sm =
    let lines = sourceLines sm in
    parseModule (SourceModule.expr sm) lines

sourceLines :: SourceModule -> SourceLines
sourceLines sm = SourceLines (fmapDefault (\x -> T.pack (uToString x)) (SourceModule.line sm))

parseType :: Type -> TypeAST
parseType t = case PbType.tag t of
                PbTypeTag.LLVM_NAMED -> NamedTypeAST $ uToString (fromJust $ PbType.name t)
                PbTypeTag.REF -> error "Ref types not yet implemented"
                PbTypeTag.FN -> parseFnTy . fromJust $ PbType.fnty t
                PbTypeTag.TUPLE -> TupleTypeAST [parseType p | p <- toList $ PbType.type_parts t]
                PbTypeTag.TYPE_VARIABLE -> error "Type variable parsing not yet implemented."
                PbTypeTag.CORO -> error "Parsing for CORO type not yet implemented"
                PbTypeTag.CARRAY -> error "Parsing for CARRAY type not yet implemented"
                PbTypeTag.FORALL_TY -> error "Parsing for FORALL_TY type not yet implemented"

parseFnTy :: FnType -> TypeAST
parseFnTy fty = FnTypeAST (TupleTypeAST [parseType x | x <- toList $ PbFnType.arg_types fty])
                          (parseType $ PbFnType.ret_type fty)
                          (case PbFnType.is_closure fty of
                            Nothing  -> Nothing
                            (Just b) -> Just [])
