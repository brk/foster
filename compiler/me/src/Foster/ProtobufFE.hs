-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufFE (
    parseSourceModule
  , dumpModuleToProtobuf
) where

import Foster.Base
import Foster.ExprAST
import Foster.TypeAST

import Data.Traversable(fmapDefault)
import Data.Sequence(length, index, Seq, empty, fromList)
import Data.Maybe(fromMaybe, fromJust, isJust)
import Data.Foldable(toList)

import Control.Exception(assert)
import qualified Data.Text as T
import qualified Data.ByteString.Lazy as L(writeFile)
import Data.ByteString.Lazy.UTF8 as UTF8
import Data.Sequence as Seq

import Text.ProtocolBuffers(isSet,getVal,messagePut)
import Text.ProtocolBuffers.Basic(uToString)

import Foster.Fepb.FnType   as PbFnType
import Foster.Fepb.Type.Tag as PbTypeTag
import Foster.Fepb.Type     as PbType
import Foster.Fepb.Proto    as Proto
import Foster.Fepb.PBIf     as PBIf
import Foster.Fepb.PBInt    as PBInt
import Foster.Fepb.Expr     as PbExpr
import Foster.Fepb.SourceModule as SourceModule
import Foster.Fepb.Expr.Tag(Tag(PB_INT, BOOL, VAR, TUPLE, COMPILES, MODULE,
                              TY_APP, IF, FN, PROTO, CALL, SEQ, SUBSCRIPT))
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
                (base:args) -> E_CallAST range (CallAST base (E_TupleAST args False))
                _ -> error "call needs a base!"

parseCompiles pbexpr lines =
    let numChildren = Seq.length $ PbExpr.parts pbexpr in
    case numChildren of
        1 -> E_CompilesAST (part 0 (PbExpr.parts pbexpr) lines) CS_NotChecked
        _ -> E_CompilesAST (E_VarAST Nothing "parse error")     CS_WouldNotCompile

parseFn pbexpr lines = let parts = PbExpr.parts pbexpr in
                       assert ((Data.Sequence.length parts) == 2) $
                       FnAST (parseProtoP (index parts 0)
                                          lines)
                             (part 1 parts lines)
                             (Just []) -- assume closure until proven otherwise

parseFnAST pbexpr lines = E_FnAST $ parseFn pbexpr lines

parseIf pbexpr lines =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif = E_IfAST $
                 IfAST (parseExpr (PBIf.test_expr pbif) lines)
                       (parseExpr (PBIf.then_expr pbif) lines)
                       (parseExpr (PBIf.else_expr pbif) lines)

parseInt :: PbExpr.Expr -> SourceLines -> ExprAST
parseInt pbexpr lines =
        let range = parseRange pbexpr lines in
        E_IntAST range (uToString $ getVal pbexpr PbExpr.int_text)

parseSeq pbexpr lines =
    let exprs = map (\x -> parseExpr x lines) $ toList (PbExpr.parts pbexpr) in
    buildSeqs exprs

-- | Convert a list of ExprASTs to a right-leaning "list" of SeqAST nodes.
buildSeqs :: [ExprAST] -> ExprAST
buildSeqs []    = E_TupleAST [] False
buildSeqs [a]   = a
buildSeqs [a,b] = E_SeqAST a b
buildSeqs (a:b) = E_SeqAST a (buildSeqs b)

parseSubscript pbexpr lines =
    let parts = PbExpr.parts pbexpr in
    E_SubscriptAST (part 0 parts lines) (part 1 parts lines)

parseTuple pbexpr lines =
    let exprs = map (\x -> parseExpr x lines) $ toList $ PbExpr.parts pbexpr in
    E_TupleAST exprs (fromMaybe False $ PbExpr.is_closure_environment pbexpr)

parseVar pbexpr lines = E_VarAST (fmap parseType (PbExpr.type' pbexpr))
                                 (uToString (fromJust $ PbExpr.name pbexpr))

toplevel :: FnAST -> FnAST
toplevel (FnAST a b (Just [])) = FnAST a b Nothing

parseModule :: PbExpr.Expr -> SourceLines -> ModuleAST FnAST
parseModule pbexpr lines =
    ModuleAST [toplevel (parseFn e lines) | e <- toList $ PbExpr.parts pbexpr]
              lines


parseProtoP :: PbExpr.Expr -> SourceLines -> PrototypeAST
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
getVarName (E_VarAST mt s) = s

getType :: PbExpr.Expr -> TypeAST
getType e = case PbExpr.type' e of
                Just t -> parseType t
                Nothing -> MissingTypeAST $ "ProtobufUtils.getType " ++ show (PbExpr.tag e)

getFormal :: PbExpr.Expr -> SourceLines ->  AnnVar
getFormal e lines = case PbExpr.tag e of
            VAR -> case parseVar e lines of
                    (E_VarAST mt v) ->
                        let i = (Ident v (54321)) in
                        case mt of
                            Just t  -> (AnnVar t i)
                            Nothing -> (AnnVar (MissingTypeAST $ "ProtobufUtils.getFormal " ++ v) i)
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
                VAR     -> parseVar
                Foster.Fepb.Expr.Tag.TUPLE   -> parseTuple
                Foster.Fepb.Expr.Tag.FN      -> parseFnAST
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

parseFnTy :: FnType -> TypeAST
parseFnTy fty = FnTypeAST (TupleTypeAST [parseType x | x <- toList $ PbFnType.arg_types fty])
                          (parseType $ PbFnType.ret_type fty)
                          (case PbFnType.is_closure fty of
                            Nothing  -> Nothing
                            (Just b) -> Just [])


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
dumpType other = error $ "dumpType saw unknown type " ++ show other

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


dumpExpr :: AnnExpr -> PbExpr.Expr

dumpExpr x@(E_AnnFn (AnnFn fnTy p b cs)) =
    P'.defaultValue { PbExpr.parts = fromList $ [dumpExprProto fnTy p, dumpExpr b]
                    , PbExpr.tag   = Foster.Fepb.Expr.Tag.FN
                    , PbExpr.type' = Just $ dumpType fnTy }

dumpExpr (AnnCall r t base (AnnTuple args _)) = dumpCall r t base args
dumpExpr (AnnCall r t base arg)               = dumpCall r t base [arg]

dumpExpr x@(AnnBool b) =
    P'.defaultValue { bool_value   = Just b
                    , PbExpr.tag   = BOOL
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr (E_AnnVar var@(AnnVar t v)) = dumpVar var

dumpExpr x@(AnnSeq a b) = dumpSeqOf (unbuildSeqsA x) (typeAST x)

dumpExpr x@(AnnTuple es b) =
    P'.defaultValue { PbExpr.parts = fromList [dumpExpr e | e <- es]
                    , is_closure_environment = Just b
                    , PbExpr.tag   = Foster.Fepb.Expr.Tag.TUPLE
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr x@(AnnSubscript t a b ) =
    P'.defaultValue { PbExpr.parts = fromList (fmap dumpExpr [a,b])
                    , PbExpr.tag   = SUBSCRIPT
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr (AnnCompiles CS_WouldCompile _)    = dumpExpr (AnnBool True)
dumpExpr (AnnCompiles CS_WouldNotCompile _) = dumpExpr (AnnBool False)
dumpExpr (AnnCompiles CS_NotChecked _) = error "dumpExpr (AnnCompiles CS_NotChecked)"

dumpExpr x@(AnnInt ty int) =
    P'.defaultValue { PbExpr.int_text = Just $ u8fromString $ litIntText int
                    , PbExpr.tag   = PB_INT
                    , PbExpr.type' = Just $ dumpType (typeAST x)  }

dumpExpr x@(AnnIf t a b c) =
    P'.defaultValue { pb_if        = Just (dumpIf $ x)
                    , PbExpr.tag   = IF
                    , PbExpr.type' = Just $ dumpType (typeAST x) }

dumpExpr x@(E_AnnTyApp overallTy baseExpr argType) =
    P'.defaultValue { PbExpr.ty_app_arg_type = Just $ dumpType argType
                    , PbExpr.parts = fromList (fmap dumpExpr [baseExpr])
                    , PbExpr.tag   = TY_APP
                    , PbExpr.type' = Just $ dumpType overallTy }

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
                    , PbExpr.tag   = SEQ
                    , PbExpr.type' = Just $ dumpType ty  }

dumpCall range t base args =
    P'.defaultValue { PbExpr.parts = fromList $ fmap dumpExpr (base : args)
                    , PbExpr.tag   = CALL
                    , PbExpr.type' = Just $ dumpType t
                    , PbExpr.range = dumpRange range }

dumpIf x@(AnnIf t a b c) =
        PBIf { test_expr = dumpExpr a, then_expr = dumpExpr b, else_expr = dumpExpr c }

dumpInt origText = PBInt.PBInt { originalText = u8fromString origText }

dumpProto (AnnPrototype t ident es) =
    Proto { Proto.name = u8fromString (dumpIdent ident)
          , in_args    = fromList $ [dumpVar e | e <- es]
          , result     = Just (dumpType t) }

dumpVar (AnnVar t ident) =
    P'.defaultValue { PbExpr.name  = Just $ u8fromString (dumpIdent ident)
                    , PbExpr.tag   = VAR
                    , PbExpr.type' = Just $ dumpType t  }

dumpModule :: ModuleAST AnnFn -> PbExpr.Expr
dumpModule mod = P'.defaultValue {
      parts = fromList [dumpExpr (E_AnnFn f) | f <- moduleASTfunctions mod]
    , PbExpr.tag   = MODULE }

-----------------------------------------------------------------------

dumpSourceModule :: ModuleAST AnnFn -> SourceModule
dumpSourceModule mod =
    let (SourceLines seq) = moduleASTsourceLines mod in -- seq :: Seq T.Text
    SourceModule { line = fmap textToPUtf8 seq , expr = (dumpModule mod) }

dumpModuleToProtobuf :: ModuleAST AnnFn -> FilePath -> IO ()
dumpModuleToProtobuf mod outpath = do
    let expr = dumpSourceModule mod
    L.writeFile outpath (messagePut expr)
    return ()

