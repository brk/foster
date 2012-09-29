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
import Foster.TypeAST(gFosterPrimOpsTable)
import Foster.ProtobufUtils(pUtf8ToText)

import Data.Traversable(fmapDefault)
import Data.Sequence as Seq
import Data.Maybe(fromMaybe)
import Data.Foldable(toList)
import qualified Data.Map as Map(lookup)

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
import qualified Foster.Fepb.TermBinding    as PbTermBinding
import Foster.Fepb.Kind     as PbKind
import Foster.Fepb.Kind.Tag as PbKindTag
import Foster.Fepb.PBLet    as PBLet
import Foster.Fepb.Defn     as Defn
import Foster.Fepb.Decl     as Decl
import Foster.Fepb.DataType as DataType
import Foster.Fepb.DataCtor as DataCtor
import Foster.Fepb.PBIf     as PBIf
import Foster.Fepb.PBCase   as PBCase
import Foster.Fepb.PBValAbs as PBValAbs
import Foster.Fepb.Expr     as PbExpr
import Foster.Fepb.SourceModule as SourceModule
import Foster.Fepb.WholeProgram as WholeProgram
import Foster.Fepb.Expr.Tag(Tag(IF, LET, VAR, SEQ, UNTIL,
                                BOOL, CALL, CALLPRIM, TY_APP, STRING, -- MODULE,
                                PB_INT, PB_RAT,
                                CASE_EXPR, COMPILES, VAL_ABS,
                                PAT_WILDCARD, PAT_NUM, PAT_BOOL, PAT_CTOR,
                                PAT_VARIABLE, PAT_TUPLE))
import qualified Foster.Fepb.SourceRange as Pb
import qualified Foster.Fepb.SourceLocation as Pb
import qualified Foster.Fepb.Formatting as PbFormatting
import Foster.Fepb.Formatting.Tag

import Foster.Primitives

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

parseBool pbexpr annot = do
    return $ E_BoolAST annot $ fromMaybe False (PbExpr.bool_value pbexpr)

parseCall pbexpr rng = do
    (base:args) <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_CallAST rng base args

parseCallPrim pbexpr annot = do
    args <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    let primname = getName "prim" $ PbExpr.string_value pbexpr
    case (T.unpack primname, args) of
      ("tuple",  _ ) -> return $ E_TupleAST annot args
      ("deref", [e]) -> return $ E_DerefAST annot e
      ("alloc",           [e]) -> return $ E_AllocAST annot e MemRegionGlobalHeap
      ("stackref-unsafe", [e]) -> return $ E_AllocAST annot e MemRegionStack
      ("subscript",       [a,b]) -> return $ E_ArrayRead annot (ArrayIndex a b (annotRange annot) SG_Dynamic)
      ("subscript-unsafe",[a,b]) -> return $ E_ArrayRead annot (ArrayIndex a b (annotRange annot) SG_Static)
      ("store",[a,b])-> case b of -- a>^ c[d]
                           E_ArrayRead _ ari -> return $ E_ArrayPoke annot ari a
                           _                 -> return $ E_StoreAST annot a b
      ("kill-entire-process",  [s@(E_StringAST {})]) ->
                                                return $ E_KillProcess annot s
      (name, args) ->
        case Map.lookup name gFosterPrimOpsTable of
          Just _ ->
            let emptyAnnot = ExprAnnot [] (MissingSourceRange "prim") [] in
            return $ E_CallAST annot (E_PrimAST emptyAnnot name) args
          Nothing ->
            error $ "ProtobufFE: unknown primitive/arg combo " ++ show primname

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

parseFn pbexpr = do annot <- parseAnnot pbexpr
                    bodies <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
                    let body = case bodies of
                               [b] -> b
                               _ -> error $ "Can't parse fn without a body!"
                    let name  = getName "fn" $ PbExpr.string_value pbexpr
                    let valabs = case PbExpr.pb_val_abs pbexpr of
                                   Just v -> v
                                   Nothing -> error "Can't parse fn without PBValAbs!"
                    let formals = toList $ PBValAbs.formals valabs
                    let tyformals = map parseTypeFormal $
                                        toList $ PBValAbs.type_formals valabs
                    return $ (FnAST annot name tyformals
                               (map parseFormal formals) body
                               False) -- assume closure until proven otherwise
  where
     parseFormal (Formal u t) = TypedId (parseType t) (Ident (pUtf8ToText u) 0)

parseValAbs pbexpr range = liftM (E_FnAST range) (parseFn pbexpr)

parseIf pbexpr annot =
        if (isSet pbexpr PbExpr.pb_if)
                then parseFromPBIf (getVal pbexpr PbExpr.pb_if)
                else error "must have if to parse from if!"
        where parseFromPBIf pbif = do
               eif   <- parseExpr (PBIf.test_expr pbif)
               ethen <- parseExpr (PBIf.then_expr pbif)
               eelse <- parseExpr (PBIf.else_expr pbif)
               return (E_IfAST annot eif ethen eelse)

parseUntil pbexpr range = do
    [a, b] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    return $ E_UntilAST range a b

parseInt :: PbExpr.Expr -> ExprAnnot -> FE (ExprAST TypeP)
parseInt pbexpr annot = do
    return $ E_IntAST annot (uToString $ getVal pbexpr PbExpr.string_value)

parseRat :: PbExpr.Expr -> ExprAnnot -> FE (ExprAST TypeP)
parseRat pbexpr annot = do
    return $ E_RatAST annot (uToString $ getVal pbexpr PbExpr.string_value)

-- String literals are parsed with leading and trailing " characters,
-- so we take tail . init to strip them off.
parseString :: PbExpr.Expr -> ExprAnnot -> FE (ExprAST TypeP)
parseString pbexpr annot = do
    return $ E_StringAST annot (T.init . T.tail . pUtf8ToText $
                                 getVal pbexpr PbExpr.string_value)

parseLet pbexpr annot = do
    parsePBLet annot
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

parseSeq pbexpr annot = do
    exprs <- mapM parseExpr $ toList (toList $ PbExpr.parts pbexpr)
    return $ buildSeqs exprs
      where
        -- Convert a list of ExprASTs to a right-leaning "list" of SeqAST nodes.
        buildSeqs :: [ExprAST t] -> (ExprAST t)
        buildSeqs []    = error $ "ProtobufFE.parseSeq can't parse empty seq!"
                                 ++ highlightFirstLine (annotRange annot)
        buildSeqs [a]   = a
        buildSeqs (a:b) = E_SeqAST (ExprAnnot [] (MissingSourceRange "buildSeqs") [])
                                   a (buildSeqs b)

parseTyApp pbexpr range = do
    [body] <- mapM parseExpr (toList $ PbExpr.parts pbexpr)
    let tys = map parseType (toList $ PbExpr.ty_app_arg_type pbexpr)
    return $ E_TyApp range  body tys

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
              (PAT_NUM,   E_IntAST _ iv) -> EP_Int  range iv
              (PAT_NUM,   other) -> error $ "Only int patterns supported for now..." ++ show other
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

parseAnnot :: PbExpr.Expr -> FE ExprAnnot
parseAnnot expr = do
  rng <- parseRange expr
  return $ ExprAnnot [] rng []

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

parseSourceLocation :: Pb.SourceLocation -> ESourceLocation
parseSourceLocation sr = -- This may fail for files of more than 2^29 lines.
    ESourceLocation (fromIntegral $ Pb.line sr) (fromIntegral $ Pb.column sr)

parseExpr :: PbExpr.Expr -> FE (ExprAST TypeP)
parseExpr pbexpr = do
    let fn = case PbExpr.tag pbexpr of
                STRING  -> parseString
                PB_INT  -> parseInt
                PB_RAT  -> parseRat
                IF      -> parseIf
                UNTIL   -> parseUntil
                BOOL    -> parseBool
                VAR     -> parseEVar
                Foster.Fepb.Expr.Tag.VAL_ABS -> parseValAbs
                CALL      -> parseCall
                CALLPRIM  -> parseCallPrim
                SEQ       -> parseSeq
                LET       -> parseLet
                TY_APP    -> parseTyApp
                CASE_EXPR -> parseCaseExpr
                COMPILES  -> parseCompiles
                PAT_WILDCARD -> error "parseExpr called on pattern!"
                PAT_VARIABLE -> error "parseExpr called on pattern!"
                PAT_CTOR     -> error "parseExpr called on pattern!"
                PAT_BOOL     -> error "parseExpr called on pattern!"
                PAT_NUM      -> error "parseExpr called on pattern!"
                PAT_TUPLE    -> error "parseExpr called on pattern!"

                --otherwise -> error $ "parseExpr saw unknown tag: " ++ (show $ PbExpr.tag pbexpr) ++ "\n"
    annot <- parseAnnot pbexpr
    fn pbexpr annot

parseDataType :: DataType.DataType -> FE (Foster.Base.DataType TypeP)
parseDataType dt = do
    let tyformals = map parseTypeFormal (toList $ DataType.tyformal dt)
    ctors <- mapM (parseDataCtor tyformals) $
                       Prelude.zip [0..] (toList $ DataType.ctor dt)
    return $ Foster.Base.DataType (uToString $ DataType.name dt) tyformals ctors
 where
  parseDataCtor :: [TypeFormalAST] -> (Int, DataCtor.DataCtor) -> FE (Foster.Base.DataCtor TypeP)
  parseDataCtor tyf (n, ct) = do
      let types = map parseType (toList $ DataCtor.type' ct)
      return $ Foster.Base.DataCtor (pUtf8ToText $ DataCtor.name ct) n tyf types

parseModule _name hash decls defns datatypes = do
    lines <- gets feModuleLines
    funcs <- sequence $ [(parseFn e)  | (Defn _nm e) <- defns]
    dtypes <- mapM parseDataType datatypes
    return $ ModuleAST hash (map toplevel funcs)
                [(uToString nm, parseType t) | (Decl nm t) <- decls]
                dtypes
                lines
                primitiveDataTypesP
  where
    toplevel :: FnAST t -> FnAST t
    toplevel f | fnWasToplevel f =
            error $ "Broken invariant: top-level functions " ++
                    "should not have their top-level bit set before we do it!"
    toplevel f = f { fnWasToplevel = True }

parseSourceModule :: SourceModule -> ModuleAST FnAST TypeP
parseSourceModule sm = resolveFormatting m where
   m =
     evalState
      (parseModule (uToString $ SourceModule.self_name sm)
                   (uToString $ SourceModule.hash sm)
                   (toList    $ SourceModule.decl sm)
                   (toList    $ SourceModule.defn sm)
                   (toList    $ SourceModule.data_type sm))
      (FEState (sourceLines sm))

   formatting = map p $ toList $ SourceModule.formatting sm

     where p pbf = (,) (parseSourceLocation $ PbFormatting.f_loc pbf) $
                    case PbFormatting.tag pbf of
                       NEWLINE -> BlankLine
                       NHIDDEN -> NonHidden
                       COMMENT -> Comment (case PbFormatting.comment pbf of
                                             Just u -> uToString u
                                             Nothing -> error $ "PbFormatting.COMMENT without comment?")

   sourceLines :: SourceModule -> SourceLines
   sourceLines sm = SourceLines (fmapDefault pUtf8ToText (SourceModule.line sm))

   resolveFormatting :: ModuleAST FnAST TypeP -> ModuleAST FnAST TypeP
   resolveFormatting m =
     m { moduleASTfunctions = evalState
                                (mapM attachFormattingFn (moduleASTfunctions m))
                                formatting }

   hiddens ps = Prelude.filter (\x -> case x of NonHidden -> False
                                                _         -> True) $
                               processNewlines (map snd ps)
      where
           processNewlines xs = drop1st xs
             where drop1st   [] = []
                   drop1st   (BlankLine:xs) =     keepuntil xs
                   drop1st   (x        :xs) = x : drop1st   xs
                   keepuntil (NonHidden:xs) =     drop1st   xs
                   keepuntil (x        :xs) = x : keepuntil xs
                   keepuntil [] = []

   getPreFormatting :: ExprAnnot -> State [(ESourceLocation, Formatting)]
                                          ExprAnnot
   getPreFormatting (ExprAnnot [] rng post) = do
     fs <- get
     let prefilter (_, NonHidden) = True
         prefilter (loc, _      ) = loc `beforeRangeStart` rng
     let (pre, rest) = span prefilter fs
     put rest
     return (ExprAnnot (hiddens pre) rng post)

   getPostFormatting :: ExprAnnot -> State [(ESourceLocation, Formatting)]
                                           ExprAnnot
   getPostFormatting (ExprAnnot pre0 rng []) = do
     fs <- get
     case fs of
       [] -> return (ExprAnnot pre0 rng [])
       ((_loc0, _):_) -> do
          let
              prefilter (_, NonHidden) = True
              prefilter (loc, _ ) = loc `beforeRangeEnd` rng

              onlyComments (_, Comment _) = True
              onlyComments (_, _)         = False

              (pre, rest0) = span prefilter fs
              (post, rest) = span onlyComments rest0
          put rest
          return (ExprAnnot (pre0 ++ hiddens pre) rng (map snd post))

   attachFormattingFn :: FnAST TypeP -> State [(ESourceLocation, Formatting)]
                                              (FnAST TypeP)
   attachFormattingFn fn = do
     a0 <- getPreFormatting  (fnAstAnnot fn)
     b  <- attachFormatting  (fnAstBody  fn)
     an <- getPostFormatting a0
     return $ fn { fnAstAnnot = an, fnAstBody = b }

    -- patterns have source ranges, not annotations.
   convertTermBinding (TermBinding evar expr) =
                liftM (TermBinding evar) (attachFormatting expr)

   attachFormatting :: ExprAST TypeP -> State [(ESourceLocation, Formatting)]
                                              (ExprAST TypeP)
   attachFormatting expr = do
     let q = attachFormatting
     a0 <- getPreFormatting (exprAnnot expr)
     let ana = getPostFormatting a0 -- "annotation action"
     case expr of
       E_StringAST    _ s        -> liftM2' E_StringAST   ana (return s)
       E_BoolAST      _ b        -> liftM2' E_BoolAST     ana (return b)
       E_IntAST       _ txt      -> liftM2' E_IntAST      ana (return txt)
       E_RatAST       _ txt      -> liftM2' E_RatAST      ana (return txt)
       E_VarAST       _ v        -> liftM2' E_VarAST      ana (return v)
       E_PrimAST      _ nm       -> liftM2' E_PrimAST     ana (return nm)

       E_KillProcess  _ e        -> liftM2' E_KillProcess ana (q e)
       E_CompilesAST  _ me       -> liftM2' E_CompilesAST ana (liftMaybeM q me)
       E_IfAST        _ a b c    -> liftM4' E_IfAST       ana (q a) (q b) (q c)
       E_UntilAST     _ a b      -> liftM3' E_UntilAST    ana (q a) (q b)
       E_SeqAST       _ a b      -> liftM3' E_SeqAST      ana (q a) (q b)
       E_AllocAST     _ a rgn    -> liftM3' E_AllocAST    ana (q a) (return rgn)
       E_DerefAST     _ a        -> liftM2' E_DerefAST    ana (q a)
       E_StoreAST     _ a b      -> liftM3' E_StoreAST    ana (q a) (q b)
       E_TyApp        _ a tys    -> liftM3' E_TyApp       ana (q a) (return tys)
       E_TupleAST     _ exprs    -> liftM2' E_TupleAST    ana (mapM q exprs)
       E_LetRec       _ bnz e    -> liftM3' E_LetRec      ana (mapM convertTermBinding bnz) (q e)
       E_LetAST       _ bnd e    -> liftM3' E_LetAST      ana (convertTermBinding bnd) (q e)
       E_CallAST      _ b exprs  -> liftM3' E_CallAST     ana (q b) (mapM q exprs)
       E_FnAST        _ fn       -> liftM2' E_FnAST       ana (attachFormattingFn fn)
       E_ArrayRead    _ (ArrayIndex a b rng2 s) -> do [x, y] <- mapM q [a, b]
                                                      an <- ana
                                                      return $ E_ArrayRead an (ArrayIndex x y rng2 s)
       E_ArrayPoke    _ (ArrayIndex a b rng2 s) c -> do [x, y, z] <- mapM q [a, b, c]
                                                        an <- ana
                                                        return $ E_ArrayPoke an (ArrayIndex x y rng2 s) z
       E_Case         _ e bs     -> do e' <- q e
                                       bs' <- mapM (\(pat, exp) -> do
                                                           exp' <- q exp
                                                           return (pat, exp' )) bs
                                       an <- ana
                                       return $ E_Case an e' bs'

   liftM2' f a b     = do b' <- b;                   a' <- a; return $ f a' b'
   liftM3' f a b c   = do b' <- b; c' <- c;          a' <- a; return $ f a' b' c'
   liftM4' f a b c d = do b' <- b; c' <- c; d' <- d; a' <- a; return $ f a' b' c' d'


   liftMaybeM :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
   liftMaybeM f m = case m of Nothing ->         return Nothing
                              Just t  -> f t >>= return.Just

parseWholeProgram :: WholeProgram -> WholeProgramAST FnAST TypeP
parseWholeProgram pgm =
  let mods = map parseSourceModule (toList $ WholeProgram.modules pgm) in
  WholeProgramAST mods

parseType :: Type -> TypeP
parseType t =
    case PbType.tag t of
         PbTypeTag.TYVAR ->
                let name@(c:_) = T.unpack (getName "type name" $ PbType.name t) in
                if Just True == PbType.is_placeholder t
                  then MetaPlaceholder name
                  else if isLower c then TyVarP (BoundTyVar name)
                                    else TyConAppP name []
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
  FnTypeP (map parseType (toList $ PbFnType.arg_types fty))
            (parseType $ PbFnType.ret_type fty)
            (parseCallConv (fmap uToString $ PbFnType.calling_convention fty))
            (ftFuncIfClosureElseProc fty)
  where ftFuncIfClosureElseProc fty =
           if fromMaybe True $ PbFnType.is_closure fty then FT_Func else FT_Proc

        parseCallConv Nothing         = FastCC
        parseCallConv (Just "fastcc") = FastCC
        parseCallConv (Just "ccc"   ) = CCC
        parseCallConv (Just other   ) = error $ "Unknown call conv " ++ other

