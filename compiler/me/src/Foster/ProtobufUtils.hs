-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufUtils (
    parseSourceModule
  , dumpModuleToProtobuf
  , typeAST
  , unbuildSeqsA
  , childrenOfA
) where

import Foster.ExprAST
import Foster.TypeAST

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

import Foster.Pb.FnType   as PbFnType
import Foster.Pb.Type.Tag as PbTypeTag
import Foster.Pb.Type     as PbType
import Foster.Pb.Proto    as Proto
import Foster.Pb.PBIf     as PBIf
import Foster.Pb.PBInt    as PBInt
import Foster.Pb.Expr     as PbExpr
import Foster.Pb.SourceModule as SourceModule
import Foster.Pb.Expr.Tag(Tag(PB_INT, BOOL, VAR, TUPLE, COMPILES, MODULE, IF, FN, PROTO, CALL, SEQ, SUBSCRIPT))
import qualified Foster.Pb.SourceRange as Pb
import qualified Foster.Pb.SourceLocation as Pb

import qualified Text.ProtocolBuffers.Header as P'

-- hprotoc cheat sheet:
--
-- required string name         => (name person)
-- required int32 id            => (Person.id person)
-- optional string email        => (getVal person email)
-- optional PhoneType type      => (getVal phone_number type')
-----------------------------------------------------------------------

part :: Int -> Seq Expr -> SourceLines -> ExprAST
part i parts lines = parseExpr (index parts i) lines

parseBool pbexpr lines = BoolAST $ fromMaybe False (PbExpr.bool_value pbexpr)

parseCall pbexpr lines =
        let range = parseRange pbexpr lines in
        case map (\x -> parseExpr x lines) $ toList (PbExpr.parts pbexpr) of
                --[base, arg] -> CallAST range base arg
                (base:args) -> E_CallAST range (CallAST base (TupleAST args False))
                _ -> error "call needs a base!"

compileStatus :: Maybe String -> CompilesStatus
compileStatus Nothing                   = CS_NotChecked
compileStatus (Just "kNotChecked")      = CS_NotChecked
compileStatus (Just "kWouldCompile")    = CS_WouldCompile
compileStatus (Just "kWouldNotCompile") = CS_WouldNotCompile
compileStatus (Just x                 ) = error $ "Unable to interpret compiles status " ++ x

parseCompiles pbexpr lines =  CompilesAST (part 0 (PbExpr.parts pbexpr) lines)
                                    (compileStatus $ fmap uToString $ PbExpr.compiles_status pbexpr)

parseFn pbexpr lines = let parts = PbExpr.parts pbexpr in
                       assert ((Data.Sequence.length parts) == 2) $
                       FnAST (parseProtoP (index parts 0)
                                          lines)
                             (part 1 parts lines)
                             (case PbExpr.is_closure pbexpr of
                                            Nothing    -> Nothing
                                            Just False -> Nothing
                                            Just True  -> Just [])

parseFnAST pbexpr lines = E_FnAST $ parseFn pbexpr lines

parseIf pbexpr lines =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif =
                IfAST (parseExpr (PBIf.test_expr pbif) lines)
                      (parseExpr (PBIf.then_expr pbif) lines)
                      (parseExpr (PBIf.else_expr pbif) lines)

parseInt :: Expr -> SourceLines -> ExprAST
parseInt pbexpr lines =
        if (isSet pbexpr PbExpr.pb_int)
                then (parseFromPBInt (getVal pbexpr PbExpr.pb_int) lines)
                else error "must have int to parse from int!"

splitString :: String -> String -> [String]
splitString needle haystack =
        let textParts = T.split (T.pack needle) (T.pack haystack) in
        map T.unpack textParts

onlyHexDigitsIn :: String -> Bool
onlyHexDigitsIn str =
        Prelude.all (\x -> (toLower x) `Prelude.elem` "0123456789abcdef") str

parseFromPBInt :: PBInt -> SourceLines -> ExprAST
parseFromPBInt pbint lines =
        let text = uToString $ PBInt.originalText pbint in
        let (clean, base) = extractCleanBase text in
        assert (base `Prelude.elem` [2, 8, 10, 16]) $
        assert (onlyHexDigitsIn clean) $
        mkIntASTFromClean clean text base lines

-- Given "raw" integer text like "123`456_10",
-- return ("123456", 10)
extractCleanBase :: String -> (String, Int)
extractCleanBase text =
        let noticks = Prelude.filter (/= '`') text in
        case splitString "_" noticks of
            [first, base] -> (first, read base)
            otherwise     -> (noticks, 10)

mkIntASTFromClean :: String -> String -> Int -> SourceLines -> ExprAST
mkIntASTFromClean clean text base lines =
        let bitsPerDigit = ceiling $ (log $ fromIntegral base) / (log 2) in
        let conservativeBitsNeeded = bitsPerDigit * (Prelude.length clean) + 2 in
        let activeBits = toInteger conservativeBitsNeeded in
        IntAST (LiteralInt activeBits text clean base)

parseSeq pbexpr lines =
    let exprs = map (\x -> parseExpr x lines) $ toList (PbExpr.parts pbexpr) in
    buildSeqs exprs

-- | Convert a list of ExprASTs to a right-leaning "list" of SeqAST nodes.
buildSeqs :: [ExprAST] -> ExprAST
buildSeqs []    = IntAST (LiteralInt 1 "0" "0" 10)
                  --error "(buildSeqs []): no skip yet, so no expr to return!"
buildSeqs [a]   = a
buildSeqs [a,b] = SeqAST a b
buildSeqs (a:b) = SeqAST a (buildSeqs b)

parseSubscript pbexpr lines =
    let parts = PbExpr.parts pbexpr in
    SubscriptAST (part 0 parts lines) (part 1 parts lines)

parseTuple pbexpr lines =
    let exprs = map (\x -> parseExpr x lines) $ toList $ PbExpr.parts pbexpr in
    TupleAST exprs (fromMaybe False $ PbExpr.is_closure_environment pbexpr)

parseVar pbexpr lines = VarAST (fmap parseType (PbExpr.type' pbexpr))
                               (uToString (fromJust $ PbExpr.name pbexpr))

parseModule :: Expr -> SourceLines -> ModuleAST FnAST
parseModule pbexpr lines = ModuleAST [parseFn e lines | e <- toList $ PbExpr.parts pbexpr] lines


parseProtoP :: Expr -> SourceLines -> PrototypeAST
parseProtoP pbexpr lines =
    case PbExpr.proto pbexpr of
                Nothing     -> error "Need a Proto in the protocol buffer to parse a PrototypeAST!"
                Just proto  -> parseProtoPP proto lines

parseProtoPP :: Proto -> SourceLines -> PrototypeAST
parseProtoPP proto lines =
    let args = Proto.in_args proto in
    let vars = map (\x -> getFormal x lines) $ toList args in
    let name = uToString $ Proto.name proto in
    let retTy = case Proto.result proto of
                    Just t  -> parseType t
                    Nothing -> MissingTypeAST $ "ProtobufUtils.parseProtoPP " ++ name in
    PrototypeAST retTy name vars

getVarName :: ExprAST -> String
getVarName (VarAST mt s) = s

getType :: Expr -> TypeAST
getType e = case PbExpr.type' e of
                Just t -> parseType t
                Nothing -> MissingTypeAST $ "ProtobufUtils.getType " ++ show (PbExpr.tag e)

getFormal :: Expr -> SourceLines ->  AnnVar
getFormal e lines = case PbExpr.tag e of
            VAR -> case parseVar e lines of
                    (VarAST mt v) ->
                        case mt of
                            Just t  -> (AnnVar t v)
                            Nothing -> (AnnVar (MissingTypeAST $ "ProtobufUtils.getFormal " ++ v) v)
            _   -> error "getVar must be given a var!"

sourceRangeFromPBRange :: Pb.SourceRange -> SourceLines -> ESourceRange
sourceRangeFromPBRange pbrange lines =
    ESourceRange
        (parseSourceLocation (Pb.begin pbrange))
        (parseSourceLocation (fromJust $ Pb.end   pbrange))
        lines

getString :: Maybe P'.Utf8 -> String
getString Nothing  = ""
getString (Just u) = uToString u

parseSourceLocation :: Pb.SourceLocation -> ESourceLocation
parseSourceLocation sr = -- This may fail for files of more than 2^29 lines...
    ESourceLocation (fromIntegral $ Pb.line sr) (fromIntegral $ Pb.column sr)

parseRange :: Expr -> SourceLines ->  ESourceRange
parseRange pbexpr lines = case PbExpr.range pbexpr of
                        Nothing   -> EMissingSourceRange
                        (Just r)  -> sourceRangeFromPBRange r lines

parseExpr :: Expr -> SourceLines -> ExprAST
parseExpr pbexpr lines =
    let range = parseRange pbexpr in
    let fn = case PbExpr.tag pbexpr of
                PB_INT  -> parseInt
                IF      -> parseIf
                BOOL    -> parseBool
                VAR     -> parseVar
                Foster.Pb.Expr.Tag.TUPLE   -> parseTuple
                Foster.Pb.Expr.Tag.FN      -> parseFnAST
                PROTO   -> error $ "parseExpr cannot parse a standalone proto!" ++ (show $ PbExpr.tag pbexpr) ++ "\n"
                CALL      -> parseCall
                SEQ       -> parseSeq
                COMPILES  -> parseCompiles
                SUBSCRIPT -> parseSubscript
                otherwise -> error $ "parseExpr saw unknown tag: " ++ (show $ PbExpr.tag pbexpr) ++ "\n"
        in
   fn pbexpr lines

parseSourceModule :: SourceModule -> ModuleAST FnAST
parseSourceModule sm =
    parseModule (SourceModule.expr sm) (sourceLines sm)

sourceLines :: SourceModule -> SourceLines
sourceLines sm = SourceLines (fmapDefault (\x -> T.pack (uToString x)) (SourceModule.line sm))

parseType :: Type -> TypeAST
parseType t = case PbType.tag t of
                PbTypeTag.LLVM_NAMED -> NamedTypeAST $ uToString (fromJust $ PbType.name t)
                PbTypeTag.REF -> error "Ref types not yet implemented"
                PbTypeTag.FN -> parseFnTy . fromJust $ PbType.fnty t
                PbTypeTag.TUPLE -> TupleTypeAST [parseType p | p <- toList $ PbType.type_parts t]
                PbTypeTag.TYPE_VARIABLE -> error "Type variable parsing not yet implemented."

parseFnTy :: FnType -> TypeAST
parseFnTy fty = FnTypeAST (TupleTypeAST [parseType x | x <- toList $ PbFnType.arg_types fty])
                          (parseType $ PbFnType.ret_type fty)
                          (case PbFnType.is_closure fty of
                            Nothing  -> Nothing
                            (Just b) -> Just [])

-----------------------------------------------------------------------

typeAST :: AnnExpr -> TypeAST
typeAST (AnnBool _)          = fosBoolType
typeAST (AnnInt t _)         = t
typeAST (AnnTuple es b)      = TupleTypeAST [typeAST e | e <- es]
typeAST (E_AnnFn annFn)      = annFnType annFn
typeAST (AnnCall r t b a)    = t
typeAST (AnnCompiles c)      = fosBoolType
typeAST (AnnIf t a b c)      = t
typeAST (AnnSeq a b)         = typeAST b
typeAST (AnnSubscript t _ _) = t
typeAST (E_AnnVar (AnnVar t s)) = t

-----------------------------------------------------------------------

childrenOfA :: AnnExpr -> [AnnExpr]
childrenOfA e =
    case e of
        AnnBool         b                    -> []
        AnnCall  r t b a                     -> [b, a]
        AnnCompiles   c                      -> []
        AnnIf      t  a b c                  -> [a, b, c]
        AnnInt t _                           -> []
        E_AnnFn annFn                        -> [annFnBody annFn]
        AnnSeq      a b                      -> unbuildSeqsA e
        AnnSubscript t a b                   -> [a, b]
        AnnTuple     es b                    -> es
        E_AnnVar      v                      -> []

-----------------------------------------------------------------------

u8fromString :: String -> P'.Utf8
u8fromString s = P'.Utf8 (UTF8.fromString s)

-----------------------------------------------------------------------

dumpType :: TypeAST -> PbType.Type
dumpType (MissingTypeAST s)   = error $ "dumpType MissingTypeAST " ++ s
dumpType (NamedTypeAST s)     = P'.defaultValue { PbType.tag  = PbTypeTag.LLVM_NAMED
                                                , PbType.name = Just $ u8fromString s }
dumpType (TupleTypeAST types) = P'.defaultValue { PbType.tag  = PbTypeTag.TUPLE
                                                ,  type_parts = fromList $ fmap dumpType types }
dumpType x@(FnTypeAST s t cs) = P'.defaultValue { PbType.tag  = PbTypeTag.FN
                                                , PbType.fnty = Just $ dumpFnTy x
                                                }
dumpType x@(CoroType a b)     = P'.defaultValue { PbType.tag  = PbTypeTag.CORO
                                                ,  type_parts = fromList $ fmap dumpType [a,b] }


dumpFnTy (FnTypeAST s t cs) =
    let args = case s of
                TupleTypeAST types -> [dumpType x | x <- types]
                otherwise          -> [dumpType s]
    in
    PbFnType.FnType {
          arg_types = fromList args
        , ret_type  = dumpType t
        , PbFnType.is_closure = Just $ isJust cs
        , calling_convention = Just $ u8fromString "ccc" -- TODO fix
    }

-----------------------------------------------------------------------
-----------------------------------------------------------------------

dumpExprProto fnTy proto@(AnnPrototype t s es) =
    P'.defaultValue { PbExpr.proto = Just $ dumpProto proto
                    , PbExpr.tag   = PROTO
                    , PbExpr.type' = Just $ dumpType fnTy }


dumpExpr :: AnnExpr -> Expr

dumpExpr x@(E_AnnFn (AnnFn fnTy p b cs)) =
    P'.defaultValue { PbExpr.is_closure = Just (isJust cs)
                    , PbExpr.parts = fromList $ [dumpExprProto fnTy p, dumpExpr b]
                    , PbExpr.tag   = Foster.Pb.Expr.Tag.FN
                    , PbExpr.type' = Just $ dumpType fnTy }

dumpExpr (AnnCall r t base (AnnTuple args _)) = dumpCall t base args
dumpExpr (AnnCall r t base arg)               = dumpCall t base [arg]

dumpExpr x@(AnnBool b) =
    P'.defaultValue { bool_value   = Just b
                    , PbExpr.tag   = BOOL
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr (E_AnnVar var@(AnnVar t v)) = dumpVar var

dumpExpr x@(AnnSeq a b) = dumpSeqOf (unbuildSeqsA x) (typeAST x)

dumpExpr x@(AnnTuple es b) =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr e | e <- es]
                    , is_closure_environment = Just b
                    , PbExpr.tag   = Foster.Pb.Expr.Tag.TUPLE
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr x@(AnnSubscript t a b ) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [a,b])
                    , PbExpr.tag   = SUBSCRIPT
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr (AnnCompiles CS_WouldCompile)    = dumpExpr (AnnBool True)
dumpExpr (AnnCompiles CS_WouldNotCompile) = dumpExpr (AnnBool False)
dumpExpr (AnnCompiles CS_NotChecked) = error "dumpExpr (AnnCompiles CS_NotChecked)"

dumpExpr x@(AnnInt ty int) =
    P'.defaultValue { PbExpr.pb_int = Just $ dumpInt (litIntText int)
                    , PbExpr.tag   = PB_INT
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr x@(AnnIf t a b c) =
    P'.defaultValue { pb_if        = Just (dumpIf $ x)
                    , PbExpr.tag   = IF
                    , PbExpr.type' = Just $ dumpType (typeAST x) }

-----------------------------------------------------------------------
dumpSeqOf exprs ty =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr e | e <- exprs]
                    , PbExpr.tag   = SEQ
                    , PbExpr.type' = Just $ dumpType ty  }

dumpCall t base args =
    P'.defaultValue { PbExpr.parts = fromList $ fmap dumpExpr (base : args)
                    , PbExpr.tag   = CALL
                    , PbExpr.type' = Just $ dumpType t }

dumpIf x@(AnnIf t a b c) =
        PBIf { test_expr = dumpExpr a, then_expr = dumpExpr b, else_expr = dumpExpr c }

dumpInt origText = PBInt.PBInt { originalText = u8fromString origText }

dumpProto (AnnPrototype t s es) =
    Proto { Proto.name = u8fromString s
          , in_args    = fromList $ [dumpVar e | e <- es]
          , result     = Just (dumpType t) }

dumpVar (AnnVar t v) =
    P'.defaultValue { PbExpr.name  = Just $ u8fromString v
                    , PbExpr.tag   = VAR
                    , PbExpr.type' = Just $ dumpType t  }

dumpModule :: ModuleAST AnnFn -> Expr
dumpModule mod = P'.defaultValue {
      parts = fromList [dumpExpr (E_AnnFn f) | f <- moduleASTfunctions mod]
    , PbExpr.tag   = MODULE }

-----------------------------------------------------------------------

dumpSourceModule :: ModuleAST AnnFn -> SourceModule
dumpSourceModule mod = SourceModule { line = Data.Sequence.empty , expr = (dumpModule mod) }

dumpModuleToProtobuf :: ModuleAST AnnFn -> FilePath -> IO ()
dumpModuleToProtobuf mod outpath = do
    let expr = dumpSourceModule mod
    L.writeFile outpath (messagePut expr)
    return ()

