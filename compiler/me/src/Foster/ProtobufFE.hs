-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufFE (parseWholeProgram) where

import Foster.Base
import Foster.Kind
import Foster.ExprAST
import Foster.ParsedType
import Foster.ProtobufUtils(pUtf8ToText)

import Data.Traversable(fmapDefault)
import Data.Sequence as Seq
import Data.Maybe(fromMaybe)
import Data.Foldable(toList)

import Control.Monad.State
import Data.Char(isLower)

import Text.ProtocolBuffers(isSet,getVal)
import Text.ProtocolBuffers.Basic(uToString)

import qualified Data.Text as T

import Foster.Fepb.FnType   as PbFnType
import Foster.Fepb.Type.Tag as PbTypeTag
import Foster.Fepb.Type     as PbType
import Foster.Fepb.Formal   as PbFormal
import Foster.Fepb.TypeFormal as PbTypeFormal
import Foster.Fepb.TermBinding    as PbTermBinding
import Foster.Fepb.Kind     as PbKind
import Foster.Fepb.Kind.Tag as PbKindTag
import Foster.Fepb.PBLet    as PBLet
import Foster.Fepb.Defn     as Defn
import Foster.Fepb.Decl     as Decl
import Foster.Fepb.DataType as DataType
import Foster.Fepb.DataCtor as DataCtor
import Foster.Fepb.PBIf     as PBIf
import Foster.Fepb.PBCase   as PBCase
import Foster.Fepb.Expr     as PbExpr
import Foster.Fepb.SourceModule as SourceModule
import Foster.Fepb.WholeProgram as WholeProgram
import Foster.Fepb.Expr.Tag(Tag(IF, LET, VAR, SEQ, UNTIL,
                                BOOL, CALL, TY_APP, STRING, -- MODULE,
                                ALLOC, DEREF, STORE, TUPLE, PB_INT,
                                CASE_EXPR, COMPILES, VAL_ABS, SUBSCRIPT,
                                PAT_WILDCARD, PAT_INT, PAT_BOOL, PAT_CTOR,
                                PAT_VARIABLE, PAT_TUPLE))
import qualified Foster.Fepb.SourceRange as Pb
import qualified Foster.Fepb.SourceLocation as Pb

-----------------------------------------------------------------------
-- hprotoc cheat sheet:
--
-- required string name         => (name person)
-- required int32 id            => (Person.id person)
-- optional string email        => (getVal person email)
-- optional PhoneType type      => (getVal phone_number type')
-----------------------------------------------------------------------

data FEState = FEState { feModuleLines :: SourceLines }
type FE a = State FEState a

getName _    (Just s) = pUtf8ToText s
getName desc Nothing  = error $ "Missing required name in " ++ desc ++ "!"

parseBool pbexpr range = do
    return $ E_BoolAST range $ fromMaybe False (PbExpr.bool_value pbexpr)

parseCall pbexpr rng = do
    (base:args) <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_CallAST rng base (argTuple rng args)
        where argTuple rng args = TupleAST (rangeSpanOf rng args) args

parseCompiles pbexpr range = do
    let numChildren = Seq.length $ PbExpr.parts pbexpr
    case numChildren of
        1 -> do [body] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
                return $ E_CompilesAST range (Just body)
        _ ->    return $ E_CompilesAST range (Nothing)

parseKind pbkind =
    case PbKind.tag pbkind of
        PbKindTag.KIND_TYPE ->  KindAnySizeType
        PbKindTag.KIND_BOXED -> KindPointerSized

parseTypeFormal :: TypeFormal -> TypeFormalAST
parseTypeFormal pbtyformal =
    let name = uToString $ PbTypeFormal.name pbtyformal in
    let kind = parseKind $ PbTypeFormal.kind pbtyformal in
    TypeFormalAST name kind

parseFn pbexpr = do range <- parseRange pbexpr
                    bodies <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
                    let body = case bodies of
                               [b] -> b
                               _ -> error $ "Can't parse fn without a body!"
                    let name  = getName "fn" $ PbExpr.string_value pbexpr
                    let formals = toList $ PbExpr.formals pbexpr
                    let mretty = parseReturnType pbexpr
                    let tyformals = map parseTypeFormal $
                                        toList $ PbExpr.type_formals pbexpr
                    return $ (FnAST range name tyformals mretty
                               (map parseFormal formals) body
                               False) -- assume closure until proven otherwise
  where
     parseFormal (Formal u t) = TypedId (parseType t) (Ident (pUtf8ToText u) 0)
     parseReturnType pbexpr = fmap parseType (PbExpr.result_type pbexpr)

parseValAbs pbexpr _range = do
  fn <- parseFn pbexpr
  return $ E_FnAST fn

parseIf pbexpr range =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif = do
               eif   <- parseExpr (PBIf.test_expr pbif)
               ethen <- parseExpr (PBIf.then_expr pbif)
               eelse <- parseExpr (PBIf.else_expr pbif)
               return (E_IfAST range eif ethen eelse)

parseUntil pbexpr range = do
    [a, b] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_UntilAST range a b

parseInt :: PbExpr.Expr -> SourceRange -> FE (ExprAST TypeP)
parseInt pbexpr range = do
    return $ E_IntAST range (uToString $ getVal pbexpr PbExpr.string_value)

-- String literals are parsed with leading and trailing " characters,
-- so we take tail . init to strip them off.
parseString :: PbExpr.Expr -> SourceRange -> FE (ExprAST TypeP)
parseString pbexpr range = do
    return $ E_StringAST range (T.init . T.tail . pUtf8ToText $
                                 getVal pbexpr PbExpr.string_value)

parseLet pbexpr range = do
    parsePBLet range
               (fromMaybe (error "Protobuf node tagged LET without PbLet field!")
                          (PbExpr.pb_let pbexpr))
      where parseBinding (PbTermBinding.TermBinding u e) = do
                body <- parseExpr e
                return (Foster.ExprAST.TermBinding (VarAST Nothing (pUtf8ToText u)) body)
            parsePBLet range pblet = do
                bindings <- mapM parseBinding (toList $ PBLet.binding pblet)
                body <- parseExpr (PBLet.body pblet)
                if PBLet.is_recursive pblet
                  then return $ E_LetRec  range bindings body
                  else return $ buildLets range bindings body
            buildLets range bindings expr =
                case bindings of
                   []     -> error "parseLet requires at least one binding!" -- TODO show range
                   (b:[]) -> E_LetAST range b expr
                   (b:bs) -> E_LetAST range b (buildLets range bs expr)

parseSeq pbexpr rng = do
    exprs <- mapM parseExpr $ toList (toList $ PbExpr.parts pbexpr)
    return $ buildSeqs exprs
      where
        -- Convert a list of ExprASTs to a right-leaning "list" of SeqAST nodes.
        buildSeqs :: [ExprAST t] -> (ExprAST t)
        buildSeqs []    = error $ "ProtobufFE.parseSeq can't parse empty seq!"
                                 ++ highlightFirstLine rng
        buildSeqs [a]   = a
        buildSeqs (a:b) = E_SeqAST (MissingSourceRange "buildSeqs") a (buildSeqs b)

parseAlloc pbexpr range = do
    [body] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_AllocAST range body

parseStore pbexpr range = do
    [a,b] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    case b of -- a >^ c[d]
        E_ArrayRead _ c d -> return $ E_ArrayPoke range a c d
        _                 -> return $ E_StoreAST range a b

parseDeref pbexpr range = do
    [body] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_DerefAST range body

parseSubscript pbexpr range = do
    [a,b] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_ArrayRead range a b

parseTuple pbexpr range = do
    exprs <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_TupleAST $ TupleAST range exprs

parseTyApp pbexpr range = do
    [body] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    let tys = map parseType (toList $ PbExpr.ty_app_arg_type pbexpr)
    return $ E_TyApp range  body (maybeTupleP tys)

    where maybeTupleP []    = Nothing
          maybeTupleP [arg] = Just $ arg
          maybeTupleP args  = Just $ TupleTypeP args

parseEVar pbexpr range = do return $ E_VarAST range (parseVar pbexpr)

parseVar pbexpr = do VarAST (fmap parseType (PbExpr.type' pbexpr))
                            (getName "var" $ PbExpr.string_value pbexpr)

parsePattern :: PbExpr.Expr -> FE (EPattern TypeP)
parsePattern pbexpr = do
  range <- parseRange pbexpr
  case PbExpr.tag pbexpr of
    PAT_WILDCARD -> do return $ EP_Wildcard range
    PAT_TUPLE    -> do pats <- mapM parsePattern (toList $ PbExpr.parts pbexpr)
                       return $ EP_Tuple range pats
    PAT_CTOR     -> do let name = getName "pat_ctor" $ PbExpr.string_value pbexpr
                       pats <- mapM parsePattern (toList $ PbExpr.parts pbexpr)
                       return $ EP_Ctor range pats name
    _ -> do [expr] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
            return $ case (PbExpr.tag pbexpr, expr) of
              (PAT_BOOL, E_BoolAST _ bv) -> EP_Bool range bv
              (PAT_INT,   E_IntAST _ iv) -> EP_Int  range iv
              (PAT_VARIABLE, E_VarAST _ v)-> EP_Variable range v

              _ -> error $ "parsePattern called with non-matching tag/arg!"
                        ++ " " ++ show (PbExpr.tag pbexpr)

parseCaseExpr pbexpr range = do
  case PbExpr.pb_case pbexpr of
    Nothing -> error "Unable to parse case expression without pb_case!"
    Just pbcase -> do
      expr <- parseExpr (PBCase.scrutinee pbcase)
      patterns    <- mapM parsePattern (toList $ PBCase.pattern pbcase)
      branchexprs <- mapM parseExpr    (toList $ PBCase.branch  pbcase)
      return $ E_Case range expr (Prelude.zip patterns branchexprs)

parseRange :: PbExpr.Expr -> FE SourceRange
parseRange pbexpr =
  case PbExpr.range pbexpr of
    Nothing   -> do return $ MissingSourceRange (show $ PbExpr.tag pbexpr)
    (Just r)  ->  do lines <- gets feModuleLines
                     return $ SourceRange
                       (parseSourceLocation (Pb.begin r))
                       (parseSourceLocation (Pb.end   r))
                       lines
                       (fmap uToString (Pb.file_path r))
 where
   parseSourceLocation :: Pb.SourceLocation -> ESourceLocation
   parseSourceLocation sr = -- This may fail for files of more than 2^29 lines.
       ESourceLocation (fromIntegral $ Pb.line sr) (fromIntegral $ Pb.column sr)

parseExpr :: PbExpr.Expr -> FE (ExprAST TypeP)
parseExpr pbexpr = do
    let fn = case PbExpr.tag pbexpr of
                STRING  -> parseString
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
                PAT_CTOR     -> error "parseExpr called on pattern!"
                PAT_BOOL     -> error "parseExpr called on pattern!"
                PAT_INT      -> error "parseExpr called on pattern!"
                PAT_TUPLE    -> error "parseExpr called on pattern!"

                --otherwise -> error $ "parseExpr saw unknown tag: " ++ (show $ PbExpr.tag pbexpr) ++ "\n"
    range <- parseRange pbexpr
    fn pbexpr range

parseDataType :: DataType.DataType -> FE (Foster.Base.DataType TypeP)
parseDataType dt = do
    ctors <- mapM parseDataCtor (Prelude.zip [0..] (toList $ DataType.ctor dt))
    let tyformals = map parseTypeFormal (toList $ DataType.tyformal dt)
    return $ Foster.Base.DataType (uToString $ DataType.name dt) tyformals ctors
 where
  parseDataCtor :: (Int, DataCtor.DataCtor) -> FE (Foster.Base.DataCtor TypeP)
  parseDataCtor (n, ct) = do
      let types = map parseType (toList $ DataCtor.type' ct)
      return $ Foster.Base.DataCtor (pUtf8ToText $ DataCtor.name ct) n types

parseModule _name decls defns datatypes = do
    lines <- gets feModuleLines
    funcs <- sequence $ [(parseFn e)  | (Defn _nm e) <- defns]
    dtypes <- mapM parseDataType datatypes
    return $ ModuleAST (map toplevel funcs)
                [(uToString nm, parseType t) | (Decl nm t) <- decls]
                dtypes
                lines
  where
    toplevel :: FnAST t -> FnAST t
    toplevel f | fnWasToplevel f =
            error $ "Broken invariant: top-level functions " ++
                    "should not have their top-level bit set before we do it!"
    toplevel f = f { fnWasToplevel = True }

parseSourceModule :: SourceModule -> ModuleAST FnAST TypeP
parseSourceModule sm =
    evalState
      (parseModule (uToString $ SourceModule.name sm)
                   (toList    $ SourceModule.decl sm)
                   (toList    $ SourceModule.defn sm)
                   (toList    $ SourceModule.data_type sm))
      (FEState (sourceLines sm))
  where
   sourceLines :: SourceModule -> SourceLines
   sourceLines sm = SourceLines (fmapDefault pUtf8ToText (SourceModule.line sm))

parseWholeProgram :: WholeProgram -> WholeProgramAST FnAST TypeP
parseWholeProgram pgm =
  let mods = map parseSourceModule (toList $ WholeProgram.modules pgm) in
  WholeProgramAST mods

parseNamedType :: String -> TypeP
parseNamedType "Int64" = PrimIntP I64
parseNamedType "Int32" = PrimIntP I32
parseNamedType "Int8"  = PrimIntP I8
parseNamedType "Bool"  = PrimIntP I1
parseNamedType other = TyConAppP other []

parseType :: Type -> TypeP
parseType t =
    case PbType.tag t of
         PbTypeTag.TYVAR ->
                let name@(c:_) = T.unpack (getName "type name" $ PbType.name t) in
                if Just True == PbType.is_placeholder t
                  then MetaPlaceholder name
                  else if isLower c then TyVarP (BoundTyVar name)
                                    else parseNamedType name
         PbTypeTag.FN -> fromMaybe (error "Protobuf node tagged FN without fnty field!")
                                   (fmap parseFnTy $ PbType.fnty t)
         PbTypeTag.TUPLE -> TupleTypeP [parseType p | p <- toList $ PbType.type_parts t]
         PbTypeTag.TYPE_TYP_APP ->
                 let (base:types) = [parseType p | p <- toList $ PbType.type_parts t] in
                 case base of
                   TyConAppP nm [] -> TyConAppP nm types
                   _ -> error $ "ProtobufFE.parseType -- expected base of TYPE_TYP_APP to be TyConAppAST"

         PbTypeTag.REF       -> error "Ref types not yet implemented"
         PbTypeTag.CORO      -> error "Parsing for CORO type not yet implemented"
         PbTypeTag.CARRAY    -> error "Parsing for CARRAY type not yet implemented"
         PbTypeTag.FORALL_TY -> let [ty] = toList $ PbType.type_parts t in
                                let tyformals = toList $ PbType.tyformals t in
                                ForAllP (map parseTypeFormal tyformals)
                                        (parseType ty)

parseFnTy :: FnType -> TypeP
parseFnTy fty =
  FnTypeP (TupleTypeP [parseType x | x <- toList $ PbFnType.arg_types fty])
            (parseType $ PbFnType.ret_type fty)
            (parseCallConv (fmap uToString $ PbFnType.calling_convention fty))
            (ftFuncIfClosureElseProc fty)
  where ftFuncIfClosureElseProc fty =
           if fromMaybe True $ PbFnType.is_closure fty then FT_Func else FT_Proc

        parseCallConv Nothing         = FastCC
        parseCallConv (Just "fastcc") = FastCC
        parseCallConv (Just "ccc"   ) = CCC
        parseCallConv (Just other   ) = error $ "Unknown call conv " ++ other

