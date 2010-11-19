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

import Data.Sequence(length, index, Seq, empty, fromList)
import Data.Maybe(fromMaybe, fromJust)
import Data.Foldable(toList)
import Data.Char(toLower)

import Control.Exception(assert)
import qualified Data.Text as T
import qualified Data.ByteString.Lazy as L(writeFile)
import Data.ByteString.Lazy.UTF8 as UTF8

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
import Foster.Pb.Expr.Tag(Tag(PB_INT, BOOL, VAR, TUPLE, MODULE, IF, FN, PROTO, CALL, SEQ, SUBSCRIPT))
import qualified Foster.Pb.SourceRange as Pb

import qualified Text.ProtocolBuffers.Header as P'

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

parseModule :: Expr -> ModuleAST FnAST
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

parseSourceModule :: SourceModule -> ModuleAST FnAST
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

-----------------------------------------------------------------------

typeAST :: AnnExpr -> TypeAST
typeAST (AnnBool _)          = fosBoolType
typeAST (AnnInt t _ _ _ _)   = t
typeAST (AnnTuple es b)      = TupleTypeAST [typeAST e | e <- es]
typeAST (E_AnnFn (AnnFn (AnnPrototype rt s vs) e))
                             = FnTypeAST (normalizeTypes [t | (AnnVar t v) <- vs]) rt
typeAST (AnnCall t b a)      = t
typeAST (AnnCompiles c)      = fosBoolType
typeAST (AnnIf t a b c)      = t
typeAST (AnnSeq a b)         = typeAST b
typeAST (AnnSubscript t _ _) = t
typeAST (E_AnnPrototype t p) = t
typeAST (E_AnnVar (AnnVar t s)) = t

-----------------------------------------------------------------------

childrenOfA :: AnnExpr -> [AnnExpr]
childrenOfA e =
    case e of
        AnnBool         b                    -> []
        AnnCall    t b a                     -> [b, a]
        AnnCompiles   c                      -> []
        AnnIf      t  a b c                  -> [a, b, c]
        AnnInt t i s1 s2 i2                  -> []
        E_AnnFn (AnnFn p b)                  -> [E_AnnPrototype t p, b] where t = fnTypeFrom p b
        AnnSeq      a b                      -> unbuildSeqsA e
        AnnSubscript t a b                   -> [a, b]
        E_AnnPrototype t' (AnnPrototype t s es) -> [E_AnnVar v | v <- es]
        AnnTuple     es b                    -> es
        E_AnnVar      v                      -> []


fnTypeFrom :: AnnPrototype -> AnnExpr -> TypeAST
fnTypeFrom p b =
    let intype = normalizeTypes [avarType v | v <- annProtoVars p] in
    let outtype = typeAST b in
    FnTypeAST intype outtype

-----------------------------------------------------------------------

u8fromString :: String -> P'.Utf8
u8fromString s = P'.Utf8 (UTF8.fromString s)

-----------------------------------------------------------------------

dumpType :: TypeAST -> PbType.Type
dumpType (MissingTypeAST s)   = error $ "dumpType MissingTypeAST " ++ s
dumpType (TypeUnitAST)        = dumpType (NamedTypeAST "i32")
dumpType (NamedTypeAST s)     = P'.defaultValue { PbType.tag  = PbTypeTag.LLVM_NAMED
                                                , PbType.name = Just $ u8fromString s }
dumpType (TupleTypeAST types) = P'.defaultValue { PbType.tag  = PbTypeTag.TUPLE
                                                , tuple_parts = fromList $ fmap dumpType types }
dumpType x@(FnTypeAST s t)    = P'.defaultValue { PbType.tag  = PbTypeTag.FN
                                                , PbType.fnty = Just $ dumpFnTy x}

dumpFnTy (FnTypeAST s t) =
    let args = case s of
                TypeUnitAST        -> []
                TupleTypeAST types -> [dumpType x | x <- types]
                otherwise          -> [dumpType s]
    in
    PbFnType.FnType {
          arg_types = fromList args
        , ret_type  = dumpType t
        , PbFnType.is_closure = Just False -- TODO fix!
        , calling_convention = Just $ u8fromString "fastcc" -- TODO fix
    }

-----------------------------------------------------------------------
-----------------------------------------------------------------------

dumpExpr :: AnnExpr -> Expr

dumpExpr x@(E_AnnFn (AnnFn p b)) =
    P'.defaultValue { -- PbExpr.is_closure = Just b
                      PbExpr.parts = fromList $ fmap dumpExpr (childrenOfA x)
                    , PbExpr.tag   = Foster.Pb.Expr.Tag.FN
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr (AnnCall t base (AnnTuple args _)) = dumpCall t base args
dumpExpr (AnnCall t base arg)               = dumpCall t base [arg]

dumpExpr x@(E_AnnPrototype t' proto@(AnnPrototype t s es)) =
    P'.defaultValue { PbExpr.proto = Just $ dumpProto proto
                    , PbExpr.tag   = PROTO
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr x@(AnnBool b) =
    P'.defaultValue { bool_value   = Just b
                    , PbExpr.tag   = BOOL
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr (E_AnnVar var@(AnnVar t v)) = dumpVar var

dumpExpr x@(AnnSeq a b) =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr e | e <- unbuildSeqsA x]
                    , PbExpr.tag   = SEQ
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

--dumpExpr x@(AnnTuple [] False) = dumpExpr (AnnInt (NamedTypeAST "i32") 0 "0" "0" 10)
--dumpExpr x@(AnnTuple [e] False) = dumpExpr e
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

dumpExpr x@(AnnInt ty i t c base) =
    P'.defaultValue { PbExpr.pb_int = Just $ dumpInt (aintText x)
                    , PbExpr.tag   = PB_INT
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr x@(AnnIf t a b c) =
    P'.defaultValue { pb_if        = Just (dumpIf $ x)
                    , PbExpr.tag   = IF
                    , PbExpr.type' = Just $ dumpType (typeAST x) }

-----------------------------------------------------------------------

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
      parts = fromList [dumpExpr (E_AnnFn f) | f <- moduleASTFunctions mod]
    , PbExpr.tag   = MODULE }

-----------------------------------------------------------------------

dumpSourceModule :: ModuleAST AnnFn -> SourceModule
dumpSourceModule mod = SourceModule { line = Data.Sequence.empty , expr = (dumpModule mod) }

dumpModuleToProtobuf :: ModuleAST AnnFn -> FilePath -> IO ()
dumpModuleToProtobuf mod outpath = do
    let expr = dumpSourceModule mod
    L.writeFile outpath (messagePut expr)
    return ()

