-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufUtils (
  parseSourceModule
) where

import Foster.ExprAST
import Foster.TypeAST

import Data.Sequence(length, index, Seq)
import Data.Maybe(fromMaybe, fromJust)
import Data.Foldable(toList)
import Data.Char(toLower)

import Control.Exception(assert)
import qualified Data.Text as T

import Text.ProtocolBuffers(isSet,getVal)
import Text.ProtocolBuffers.Basic(uToString)

import Foster.Pb.FnType   as PbFnType
import Foster.Pb.Type.Tag as PbTypeTag
import Foster.Pb.Type     as PbType
import Foster.Pb.Proto    as Proto
import Foster.Pb.PBIf     as PBIf
import Foster.Pb.PBInt    as PBInt
import Foster.Pb.Expr     as PbExpr
import Foster.Pb.SourceModule as SourceModule
import Foster.Pb.Expr.Tag(Tag(PB_INT, BOOL, VAR, TUPLE, MODULE, FN, PROTO, CALL, SEQ, SUBSCRIPT))
import qualified Foster.Pb.SourceRange as Pb

-- hprotoc cheat sheet:
--
-- required string name         => (name person)
-- required int32 id            => (Person.id person)
-- optional string email        => (getVal person email)
-- optional PhoneType type      => (getVal phone_number type')
-----------------------------------------------------------------------

part :: Int -> Seq Expr -> ExprAST
part i parts = parseExpr $ index parts i

parseBool pbexpr = BoolAST $ fromMaybe False (PbExpr.bool_value pbexpr)

parseCall pbexpr =
        case map parseExpr $ toList (PbExpr.parts pbexpr) of
                [base, arg] -> CallAST base arg
                (base:args) -> CallAST base (TupleAST args False)
                _ -> error "call needs a base!"

compileStatus :: Maybe String -> CompilesStatus
compileStatus Nothing                   = CS_NotChecked
compileStatus (Just "kWouldCompile")    = CS_WouldCompile
compileStatus (Just "kWouldNotCompile") = CS_WouldNotCompile
compileStatus (Just x                 ) = error $ "Unable to interpret compiles status " ++ x

parseCompiles pbexpr =  CompilesAST (part 0 $ PbExpr.parts pbexpr)
                                    (compileStatus $ fmap uToString $ PbExpr.compiles_status pbexpr)

parseFn pbexpr = let parts = PbExpr.parts pbexpr in
                 assert ((Data.Sequence.length parts) == 2) $
                 FnAST (parseProtoP $ index parts 0)
                                     (part 1 parts)

parseFnAST pbexpr = E_FnAST $ parseFn pbexpr

parseIf pbexpr =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif =
                IfAST (parseExpr $ PBIf.test_expr pbif)
                      (parseExpr $ PBIf.then_expr pbif)
                      (parseExpr $ PBIf.else_expr pbif)

parseInt :: Expr -> ExprAST
parseInt pbexpr =
        if (isSet pbexpr PbExpr.pb_int)
                then parseFromPBInt (getVal pbexpr PbExpr.pb_int)
                else error "must have int to parse from int!"

splitString :: String -> String -> [String]
splitString needle haystack =
        let textParts = T.split (T.pack needle) (T.pack haystack) in
        map T.unpack textParts

onlyHexDigitsIn :: String -> Bool
onlyHexDigitsIn str =
        Prelude.all (\x -> (toLower x) `Prelude.elem` "0123456789abcdef") str

parseFromPBInt :: PBInt -> ExprAST
parseFromPBInt pbint =
        let text = uToString $ PBInt.originalText pbint in
        let (clean, base) = extractCleanBase text in
        assert (base `Prelude.elem` [2, 8, 10, 16]) $
        assert (onlyHexDigitsIn clean) $
        mkIntASTFromClean clean text base

-- Given "raw" integer text like "123`456_10",
-- return ("123456", 10)
extractCleanBase :: String -> (String, Int)
extractCleanBase text =
        let noticks = Prelude.filter (/= '`') text in
        case splitString "_" noticks of
            [first, base] -> (first, read base)
            otherwise     -> (noticks, 10)

mkIntASTFromClean :: String -> String -> Int -> ExprAST
mkIntASTFromClean clean text base =
        let bitsPerDigit = ceiling $ (log $ fromIntegral base) / (log 2) in
        let conservativeBitsNeeded = bitsPerDigit * (Prelude.length clean) + 2 in
        let activeBits = toInteger conservativeBitsNeeded in
        IntAST activeBits text clean base

parseSeq pbexpr = let exprs = map parseExpr $ toList (PbExpr.parts pbexpr) in
                  buildSeqs exprs

-- | Convert a list of ExprASTs to a right-leaning "list" of SeqAST nodes.
buildSeqs :: [ExprAST] -> ExprAST
buildSeqs []    = error "(buildSeqs []): no skip yet, so no expr to return!"
buildSeqs [a]   = a
buildSeqs [a,b] = SeqAST a b
buildSeqs (a:b) = SeqAST a (buildSeqs b)

parseSubscript pbexpr = let parts = PbExpr.parts pbexpr in
                        SubscriptAST (part 0 parts) (part 1 parts)

parseTuple pbexpr =
        TupleAST (map parseExpr $ toList (PbExpr.parts pbexpr))
                 (fromMaybe False $ PbExpr.is_closure_environment pbexpr)

parseVar :: Expr -> ExprAST
parseVar pbexpr = VarAST (fmap parseType (PbExpr.type' pbexpr))
                       $ uToString (fromJust $ PbExpr.name pbexpr)

parseModule :: Expr -> ModuleAST
parseModule pbexpr = ModuleAST [parseFn e | e <- toList $ PbExpr.parts pbexpr]

emptyRange :: ESourceRange
emptyRange = ESourceRange e e "<no file>"
                    where e = (ESourceLocation (-1::Int) (-1::Int))

parseProtoP :: Expr -> PrototypeAST
parseProtoP pbexpr =
    case PbExpr.proto pbexpr of
                Nothing  -> error "Need a proto to parse a proto!"
                Just proto  -> parseProtoPP proto (getType pbexpr)

parseProto :: Expr -> ExprAST
parseProto pbexpr = E_PrototypeAST (parseProtoP pbexpr)

getVarName :: ExprAST -> String
getVarName (VarAST mt s) = s

-- used?
getVar :: Expr -> ExprAST
getVar e = case PbExpr.tag e of
            VAR -> parseVar e
            _   -> error "getVar must be given a var!"

getType :: Expr -> TypeAST
getType e = case PbExpr.type' e of
                Just t -> parseType t
                Nothing -> MissingTypeAST "ProtobufUtils.getType"

getFormal :: Expr -> AnnVar
getFormal e = case PbExpr.tag e of
            VAR -> case parseVar e of
                    (VarAST mt v) ->
                        case mt of
                            Just t  -> (AnnVar t v)
                            Nothing -> (AnnVar (MissingTypeAST "ProtobufUtils.getFormal") v)
            _   -> error "getVar must be given a var!"

parseProtoPP :: Proto -> TypeAST ->  PrototypeAST
parseProtoPP proto retTy =
    let args = Proto.in_args proto in
    let vars = map getFormal $ toList args in
    let name = uToString $ Proto.name proto in
    PrototypeAST retTy name vars

sourceRangeFromPBRange :: Pb.SourceRange -> ESourceRange
sourceRangeFromPBRange pbrange = error "no"

parseExpr :: Expr -> ExprAST
parseExpr pbexpr =
    let range = case PbExpr.range pbexpr of
                    Nothing   -> emptyRange
                    (Just r)  -> sourceRangeFromPBRange r in
    let fn = case PbExpr.tag pbexpr of
                PB_INT  -> parseInt
                BOOL    -> parseBool
                VAR     -> parseVar
                Foster.Pb.Expr.Tag.TUPLE   -> parseTuple
                Foster.Pb.Expr.Tag.FN      -> parseFnAST
                PROTO     -> parseProto
                CALL      -> parseCall
                SEQ       -> parseSeq
                SUBSCRIPT -> parseSubscript
                otherwise -> error $ "Unknown tag: " ++ (show $ PbExpr.tag pbexpr) ++ "\n"
        in
   fn pbexpr

parseSourceModule :: SourceModule -> ModuleAST
parseSourceModule sm =
    parseModule (SourceModule.expr sm)


parseType :: Type -> TypeAST
parseType t = case PbType.tag t of
                PbTypeTag.LLVM_NAMED -> NamedTypeAST $ uToString (fromJust $ PbType.name t)
                PbTypeTag.REF -> error "Ref types not yet implemented"
                PbTypeTag.FN -> parseFnTy . fromJust $ PbType.fnty t
                PbTypeTag.TUPLE -> TupleTypeAST [parseType p | p <- toList $ PbType.tuple_parts t]
                PbTypeTag.TYPE_VARIABLE -> error "Type variable parsing not yet implemented."

parseFnTy :: FnType -> TypeAST
parseFnTy fty = FnTypeAST (parseType $ PbFnType.ret_type fty)
                          (TupleTypeAST [parseType x | x <- toList $ PbFnType.arg_types fty])
