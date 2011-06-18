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
import Data.Maybe(fromMaybe, isJust)
import Data.Foldable(toList)

import Control.Exception(assert)
import qualified Data.Text as T
import Data.ByteString.Lazy.UTF8 as UTF8

import Text.ProtocolBuffers(isSet,getVal)
import Text.ProtocolBuffers.Basic(uToString)

import Foster.Fepb.FnType   as PbFnType
import Foster.Fepb.Type.Tag as PbTypeTag
import Foster.Fepb.Type     as PbType
import Foster.Fepb.Formal   as PbFormal
import Foster.Fepb.TermBinding    as PbTermBinding
import Foster.Fepb.PBLet    as PBLet
import Foster.Fepb.Defn     as Defn
import Foster.Fepb.Decl     as Decl
import Foster.Fepb.PBIf     as PBIf
import Foster.Fepb.PBCase   as PBCase
import Foster.Fepb.Expr     as PbExpr
import Foster.Fepb.SourceModule as SourceModule
import Foster.Fepb.Expr.Tag(Tag(IF, LET, VAR, SEQ, UNTIL,
                                BOOL, CALL, TY_APP,-- MODULE,
                                ALLOC, DEREF, STORE, TUPLE, PB_INT,
                                CASE_EXPR, COMPILES, VAL_ABS, SUBSCRIPT,
                                PAT_WILDCARD, PAT_INT, PAT_BOOL,
                                PAT_VARIABLE, PAT_TUPLE))
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
              if (isJust $ lookup p rootContextDecls) || identNum i < 0
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

getName desc (Just s) = uToString s
getName desc Nothing  = error "Missing required name in " ++ desc ++ "!"

part :: Int -> Seq PbExpr.Expr -> SourceLines -> ExprAST
part i parts lines = parseExpr (index parts i) lines

parseBool pbexpr lines =
        let range = parseRange pbexpr lines in
        E_BoolAST range $ fromMaybe False (PbExpr.bool_value pbexpr)

parseCall pbexpr lines =
        let range = parseRange pbexpr lines in
        case map (\x -> parseExpr x lines) $ toList (PbExpr.parts pbexpr) of
                (base:args) -> E_CallAST range base (filterUnit args)
                    where filterUnit [E_TupleAST []] = []
                          filterUnit args = args
                _ -> error "call needs a base!"

parseCompiles pbexpr lines =
    let numChildren = Seq.length $ PbExpr.parts pbexpr in
    case numChildren of
        1 -> E_CompilesAST (part 0 (PbExpr.parts pbexpr) lines) CS_NotChecked
        _ -> E_CompilesAST (E_VarAST (EMissingSourceRange "parseCompiles")
                           (VarAST Nothing "parse error")) CS_WouldNotCompile

parseFn pbexpr lines = let range = parseRange pbexpr lines in
                       let parts = PbExpr.parts pbexpr in
                       let name  = getName "fn" $ PbExpr.name pbexpr in
                       let formals = toList $ PbExpr.formals pbexpr in
                       let mretty = parseReturnType name pbexpr in
                       assert ((Data.Sequence.length parts) == 1) $
                       FnAST range name mretty (map parseFormal formals)
                             (part 0 parts lines)
                             False -- assume closure until proven otherwise
  where
     parseFormal (Formal u t) = AnnVar (parseType t) (Ident (uToString u) 0)
     parseReturnType name pbexpr = fmap parseType (PbExpr.result_type pbexpr)

parseValAbs pbexpr lines =
  E_FnAST (parseFn pbexpr lines)

parseIf pbexpr lines =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif =
               (E_IfAST (parseExpr (PBIf.test_expr pbif) lines)
                        (parseExpr (PBIf.then_expr pbif) lines)
                        (parseExpr (PBIf.else_expr pbif) lines))

parseUntil pbexpr lines =
     E_UntilAST (part 0 (PbExpr.parts pbexpr) lines)
                (part 1 (PbExpr.parts pbexpr) lines)

parseInt :: PbExpr.Expr -> SourceLines -> ExprAST
parseInt pbexpr lines =
        let range = parseRange pbexpr lines in
        E_IntAST range (uToString $ getVal pbexpr PbExpr.int_text)

parseLet pbexpr lines =
    parsePBLet (parseRange pbexpr lines)
               (fromMaybe (error "Protobuf node tagged LET without PbLet field!")
                          (PbExpr.pb_let pbexpr))
               (fmap parseType $ PbExpr.type' pbexpr)
               lines
      where parseBinding lines (PbTermBinding.TermBinding u e) =
                (Foster.ExprAST.TermBinding (VarAST Nothing (uToString u)) (parseExpr e lines))
            parsePBLet range pblet mty lines =
                let bindings = map (parseBinding lines) (toList $ PBLet.binding pblet) in
                (buildLets range bindings (parseExpr (PBLet.body pblet) lines) mty)
            buildLets range bindings expr mty =
                case bindings of
                   []     -> error "parseLet requires at least one binding!" -- TODO show range
                   (b:[]) -> E_LetAST range b expr mty
                   (b:bs) -> E_LetAST range b (buildLets range bs expr mty) Nothing

parseSeq pbexpr lines =
    let exprs = map (\x -> parseExpr x lines) $ toList (PbExpr.parts pbexpr) in
    buildSeqs exprs

-- | Convert a list of ExprASTs to a right-leaning "list" of SeqAST nodes.
buildSeqs :: [ExprAST] -> ExprAST
buildSeqs []    = E_TupleAST []
buildSeqs [a]   = a
buildSeqs [a,b] = E_SeqAST a b
buildSeqs (a:b) = E_SeqAST a (buildSeqs b)

parseAlloc pbexpr lines =
    let range = parseRange pbexpr lines in
    let parts = PbExpr.parts pbexpr in
    E_AllocAST range (part 0 parts lines)

parseStore pbexpr lines =
    let range = parseRange pbexpr lines in
    let parts = PbExpr.parts pbexpr in
    E_StoreAST range (part 0 parts lines) (part 1 parts lines)

parseDeref pbexpr lines =
    let range = parseRange pbexpr lines in
    let parts = PbExpr.parts pbexpr in
    E_DerefAST range (part 0 parts lines)

parseSubscript pbexpr lines =
    let range = parseRange pbexpr lines in
    let parts = PbExpr.parts pbexpr in
    E_SubscriptAST (part 0 parts lines) (part 1 parts lines) range

parseTuple pbexpr lines =
    E_TupleAST (map (\x -> parseExpr x lines) $ toList $ PbExpr.parts pbexpr)

parseTyApp pbexpr lines =
    let range = parseRange pbexpr lines in
    E_TyApp range
            (part 0 (PbExpr.parts pbexpr) lines)
            (parseType $ case PbExpr.ty_app_arg_type pbexpr of
                                Nothing -> error "TyApp missing arg type!"
                                Just ty -> ty)

parseEVar pbexpr lines =
    let range = parseRange pbexpr lines in
    E_VarAST range (parseVar pbexpr lines)

parseVar pbexpr lines = VarAST (fmap parseType (PbExpr.type' pbexpr))
                               (getName "var" $ PbExpr.name pbexpr)

parsePattern :: PbExpr.Expr -> SourceLines -> EPattern
parsePattern pbexpr lines =
  let range = parseRange pbexpr lines in
  let parts = PbExpr.parts pbexpr in
  case PbExpr.tag pbexpr of
    PAT_WILDCARD -> EP_Wildcard range
    PAT_TUPLE    -> EP_Tuple range (map (\x -> parsePattern x lines)
                                     (toList $ PbExpr.parts pbexpr))
    _ -> case (PbExpr.tag pbexpr, part 0 parts lines) of
           (PAT_BOOL, E_BoolAST _ bv) -> EP_Bool range bv
           (PAT_INT,   E_IntAST _ iv) -> EP_Int  range iv
           (PAT_VARIABLE, E_VarAST _ v)-> EP_Variable range v

           otherwise -> error $ "parsePattern called with non-matching tag/arg!"
                                ++ " " ++ show (PbExpr.tag pbexpr)


parseCaseExpr pbexpr lines =
  let range = parseRange pbexpr lines in
  case PbExpr.pb_case pbexpr of
    Nothing -> error "must have if to parse from if!"
    Just pbcase ->
      (E_Case range
              (parseExpr (PBCase.scrutinee pbcase) lines)
       (Prelude.zip (toList $ fmap (\p -> parsePattern p lines) (PBCase.pattern pbcase))
                    (toList $ fmap (\e -> parseExpr    e lines) (PBCase.branch  pbcase))))

toplevel :: FnAST -> FnAST
toplevel (FnAST a b c d e False) = FnAST a b c d e True
toplevel (FnAST _ _ _ _ _ True ) =
        error $ "Broken invariant: top-level functions " ++
                "should not have their top-level bit set before we do it!"

parseModule name decls defns lines =
    ModuleAST [toplevel (parseFn e lines)  | (Defn nm e) <- defns]
              [(uToString nm, parseType t) | (Decl nm t) <- decls]
              lines

getVarName :: ExprAST -> String
getVarName (E_VarAST rng v) = evarName v
getVarName x = error $ "getVarName given a non-variable! " ++ show x

getFormal :: PbExpr.Expr -> SourceLines ->  AnnVar
getFormal e lines = case PbExpr.tag e of
            VAR -> let v = parseVar e lines in
                   let i = (Ident (evarName v) (54321)) in
                   case evarMaybeType v of
                       Just t  -> (AnnVar t i)
                       Nothing -> error $ "Missing annotation on variable " ++ show v
            _   -> error "getVar must be given a var!"

sourceRangeFromPBRange :: Pb.SourceRange -> SourceLines -> ESourceRange
sourceRangeFromPBRange pbrange lines =
    ESourceRange
        (parseSourceLocation (Pb.begin pbrange))
        (parseSourceLocation (Pb.end   pbrange))
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
                UNTIL   -> parseUntil
                BOOL    -> parseBool
                VAR     -> parseEVar
                Foster.Fepb.Expr.Tag.TUPLE   -> parseTuple
                Foster.Fepb.Expr.Tag.VAL_ABS -> parseValAbs
                CALL      -> parseCall
                SEQ       -> parseSeq
                LET       -> parseLet
                ALLOC     -> parseAlloc
                DEREF     -> parseDeref
                STORE     -> parseStore
                TY_APP    -> parseTyApp
                CASE_EXPR -> parseCaseExpr
                COMPILES  -> parseCompiles
                SUBSCRIPT -> parseSubscript
                PAT_WILDCARD -> error "parseExpr called on pattern!"
                PAT_VARIABLE -> error "parseExpr called on pattern!"
                PAT_BOOL     -> error "parseExpr called on pattern!"
                PAT_INT      -> error "parseExpr called on pattern!"
                PAT_TUPLE    -> error "parseExpr called on pattern!"

                --otherwise -> error $ "parseExpr saw unknown tag: " ++ (show $ PbExpr.tag pbexpr) ++ "\n"
        in
   fn pbexpr lines

parseSourceModule :: SourceModule -> ModuleAST FnAST TypeAST
parseSourceModule sm =
    let lines = sourceLines sm in
    parseModule (uToString $ SourceModule.name sm)
                (toList    $ SourceModule.decl sm)
                (toList    $ SourceModule.defn sm) lines

sourceLines :: SourceModule -> SourceLines
sourceLines sm = SourceLines (fmapDefault (\x -> T.pack (uToString x)) (SourceModule.line sm))

parseType :: Type -> TypeAST
parseType t = case PbType.tag t of
                PbTypeTag.LLVM_NAMED -> NamedTypeAST $ (getName "type name" $ PbType.name t)
                PbTypeTag.REF -> error "Ref types not yet implemented"
                PbTypeTag.FN -> fromMaybe (error "Protobuf node tagged FN without fnty field!")
                                          (fmap parseFnTy $ PbType.fnty t)
                PbTypeTag.TUPLE -> TupleTypeAST [parseType p | p <- toList $ PbType.type_parts t]
                PbTypeTag.TYPE_VARIABLE -> error "Type variable parsing not yet implemented."
                PbTypeTag.CORO -> error "Parsing for CORO type not yet implemented"
                PbTypeTag.CARRAY -> error "Parsing for CARRAY type not yet implemented"
                PbTypeTag.FORALL_TY -> error "Parsing for FORALL_TY type not yet implemented"

parseCallConv Nothing         = FastCC
parseCallConv (Just "fastcc") = FastCC
parseCallConv (Just "ccc"   ) = CCC
parseCallConv (Just other   ) = error $ "Unknown call conv " ++ other

parseFnTy :: FnType -> TypeAST
parseFnTy fty = FnTypeAST (TupleTypeAST [parseType x | x <- toList $ PbFnType.arg_types fty])
                          (parseType $ PbFnType.ret_type fty)
                          (parseCallConv (fmap uToString $ PbFnType.calling_convention fty))
                          (if fromMaybe True $ PbFnType.is_closure fty
                            then Just []
                            else Nothing)
