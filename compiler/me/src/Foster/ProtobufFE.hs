{-# Language Strict #-}
-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.ProtobufFE (cb_parseWholeProgram) where

import Foster.Base
import Foster.Kind
import Foster.ExprAST
import Foster.ParsedType
import Foster.TypeAST(gFosterPrimOpsTable)
import Foster.Tokens

import Data.CBOR

import Data.Foldable (toList)
import Data.List(groupBy, foldl')
import qualified Data.Sequence as Seq
import qualified Data.Map as Map(lookup)

import Data.Char(isLower, isPunctuation, isSymbol, isHexDigit, digitToInt, chr)
import Numeric(readHex)
import Data.Bits((.&.))

import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString.Char8 as BS

import Foster.Primitives

import Debug.Trace(trace)

import Control.Monad.State (evalState, get, put, liftM, State)
--------------------------------------------------------------------------------

cb_parseWholeProgram :: CBOR -> Bool -> WholeProgramAST (ExprSkel ExprAnnot) TypeP
cb_parseWholeProgram cbor standalone =
  case cbor of
    CBOR_Array cbmods ->
      let mods = map (cb_parseSourceModule standalone) cbmods in
      WholeProgramAST mods
    _ -> error "cb_parseWholeProgram expected an array of modules."

cb_parseSourceModule standalone cbor = case cbor of
  CBOR_Array [nm, _, _, CBOR_Array lines, _] ->
    cb_parseSourceModuleWithLines standalone sourcelines (cborText nm) cbor
      where sourcelines = SourceLines $ Seq.fromList $ map cborText lines
  _ -> error "cb_parseSourceModule"

-- Defer parsing to a separate function so that sourcelines is in scope for
-- the function's where-clause definitions.
cb_parseSourceModuleWithLines standalone lines sourceFile cbor = case cbor of
  CBOR_Array [_, hash, modtree, _, CBOR_Array hiddentokens] ->
      case modtree of
        CBOR_Array [tok, _, _, CBOR_Array (cbincludes:defn_decls)] | tok `tm` tok_MODULE ->
          let includes  = cb_parseIncludes cbincludes
              items = map cb_parse_ToplevelItem defn_decls
              primDTs = if standalone then [] else primitiveDataTypesP
              m = ModuleAST (T.unpack (cborText hash)) includes items lines primDTs
          in resolveFormatting hiddentokens m
        _ -> error $ "cb_parseSourceModule[1] failed"
  _ -> error $ "cb_parseSourceModule[2] failed"

 where
  tm (CBOR_UInt x) n = x == n
  tm other _n = error $ "tm expected CBOR_UInt, got " ++ show other

  cb_parse_ToplevelItem cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [x, t]] | tok `tm` tok_DECL ->
       ToplevelDecl (cb_parse_x_str x, cb_parse_t t, NotForeign)
    CBOR_Array [tok, _,_cbr, CBOR_Array [x, phrase]] | tok `tm` tok_DEFN ->
      case (cb_parse_x_str x, cb_parse_phrase phrase) of
        (name, E_FnAST annot fn) ->
                        ToplevelDefn (name, E_FnAST annot fn { fnAstName = T.pack name , fnWasToplevel = True })
        (name, expr) -> ToplevelDefn (name, expr)
    CBOR_Array [tok, _, cbr, CBOR_Array [tyformal_nm, mu_tyformals, mu_data_ctors]]
                                                      | tok `tm` tok_DATATYPE ->
       let tyf = (map cb_parse_tyformal  (unMu mu_tyformals)) in
       ToplevelData $ DataType (cb_parse_tyformal      tyformal_nm)
                                   tyf
                                   (map (cb_parse_data_ctor tyf) (unMu mu_data_ctors))
                                   False
                                   (cb_parse_range          cbr)
    CBOR_Array [tok, _, cbr, CBOR_Array [tyformal_nm, mu_tyformals, mu_effect_ctors]]
                                                      | tok `tm` tok_EFFECT ->
       let tyf = (map cb_parse_tyformal  (unMu mu_tyformals)) in
       ToplevelEffect $ EffectDecl (cb_parse_tyformal      tyformal_nm)
                                   tyf
                                   (map (cb_parse_effect_ctor tyf) (unMu mu_effect_ctors))
                                   (cb_parse_range          cbr)

    CBOR_Array [tok, _,_cbr, CBOR_Array [CBOR_Array (tag:_), x, t]] | tok `tm` tok_FOREIGN
                                                                   && tag `tm` tok_DECL ->
      let name = cb_parse_x_str x in
      ToplevelDecl (name, makeProcsWithin (cb_parse_t t), IsForeign name)
    CBOR_Array [tok, _,_cbr, CBOR_Array [CBOR_Array (tag:_), x, t, id]] | tok `tm` tok_FOREIGN
                                                                   && tag `tm` tok_DECL ->
      ToplevelDecl (cb_parse_id_str id, makeProcsWithin (cb_parse_t t), IsForeign (cb_parse_x_str x))

    CBOR_Array [tok, _, cbr, CBOR_Array [CBOR_Array (tag:_), tyformal_nm]] | tok `tm` tok_FOREIGN && tag `tm` _tok_TYPE ->
      ToplevelData $ DataType (cb_parse_tyformal tyformal_nm)
                              [] [] True
                              (cb_parse_range          cbr)

    _ -> error $ "cb_parseToplevelItem failed: " ++ show cbor

  -- ^(OF dctor tatom*);
  cb_parse_data_ctor tyf cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array (dctor : tatoms)] | tok `tm` tok_OF ->
      Foster.Base.DataCtor (cb_parse_dctor dctor) tyf (map cb_parse_tatom tatoms) Nothing (cb_parse_range cbr)
    _ -> error $ "cb_parse_data_ctor failed: " ++ show cbor

  cb_parse_dctor cbor = cb_parse_ctor cbor

  -- ^(OF dctor ^(MU tatom*) ^(MU t?));
  cb_parse_effect_ctor tyf cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array [dctor, mu_tatoms, mu_mb_t]] | tok `tm` tok_OF ->
      Foster.Base.EffectCtor
        (Foster.Base.DataCtor (cb_parse_dctor dctor) tyf (map cb_parse_tatom (unMu mu_tatoms))
                              Nothing (cb_parse_range cbr))
        (case unMu mu_mb_t of
          []  -> -- Default to unit type if no explicit annotation
                 -- has been provided.
                 TupleTypeP KindAnySizeType []
          [t] -> cb_parse_t t
          x -> error $ "cb_parse_effect_ctor (t?) failed: " ++ show x)
    _ -> error $ "cb_parse_effect_ctor failed: " ++ show cbor

  cb_parse_aid :: CBOR -> String
  cb_parse_aid cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [name]] | tok `tm` tok_TYPENAME -> cb_parse_typename name
    _ -> error $ "cb_parse_aid failed: " ++ show cbor

  cb_parse_id_str cbor = case cbor of
    CBOR_Array [_tok, name,_cbr, _] -> T.unpack (cborText name)
    _ -> error $ "cb_parse_id_str failed: " ++ show cbor
    
  cb_parse_x_str cbor = T.unpack (cb_parse_x_text cbor)
  cb_parse_x_VarAST cbor = case cb_parse_x cbor of
                             E_VarAST _ v -> v
                             _ -> error "cb_parse_x_VarAST shouldn't fail"
  cb_parse_x_text cbor = case cb_parse_x cbor of
                           E_VarAST _ (VarAST _ t) -> t
                           _ -> error "cb_parse_x_text shouldn't fail"

  cb_parse_x cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [name]] | tok `tm` tok_TERMNAME -> cb_parse_termname name
    _ -> error $ "cb_parse_x failed: " ++ show cbor

  cb_parse_VarAST cbor = case cbor of
    CBOR_Array [_tok, name,_cbr, CBOR_Array []] -> VarAST Nothing (cborText name)
    _ -> error $ "cb_parse_VarAST failed: " ++ show cbor

  cb_parse_termname cbor = case cbor of
    CBOR_Array [_tok, name,_cbr, CBOR_Array []] -> E_VarAST (annotOfCbor cbor) (VarAST Nothing (cborText name))
    _ -> error $ "cb_parse_termname failed: " ++ show cbor

  cb_parse_typename cbor = case cbor of
    CBOR_Array [_tok, name, _cbr, CBOR_Array []] -> T.unpack $ cborText name
    _ -> error $ "cb_parse_typename failed: " ++ show cbor

  -- TODO: rationals should not contain hex digits or a base specifier
  -- TOOD: e/E should only appear in rationals as exponent specifier
  cb_parse_lit_num int_ctor rat_ctor annot cbor =
   case cbor of
    CBOR_Array [_tok, num,_cbr, CBOR_Array []] ->
      let str = (T.unpack $ cborText num) in
      if '.' `elem` str
        then rat_ctor annot str
        else int_ctor annot str
    _ -> error $ "cb_parse_lit_num failed: " ++ show cbor

  _cb_parse_name cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [_id, _name]] | tok `tm` tok_QNAME -> error "name (cb_parse_id id) (cb_parse_name name)"
    _ -> error $ "cb_parse_name failed: "


  cb_parse_ctor cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [x]] | tok `tm` tok_CTOR ->
      cb_parse_x_text x
    _ -> error $ "cb_parse_ctor failed: " ++ show cbor ++ " ;; " ++ show sourceFile

  cb_parse_k :: CBOR -> Kind
  cb_parse_k cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [aid]] | tok `tm` tok_KIND_CONST ->
      case cb_parse_aid aid of
        "Type"   -> KindAnySizeType
        "Boxed"  -> KindPointerSized
        "Effect" -> KindEffect
        other -> error $ "cb_parse_k failed, unknown kind constant " ++ other
    _ -> error $ "cb_parse_k failed: " ++ show cbor

  cb_parse_idbinding cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [xid, e]] | tok `tm` tok_BINDING ->
      (,) (cb_parse_patbind xid) (cb_parse_e e)
    _ -> error $ "cb_parse_idbinding failed: " ++ show cbor


  cb_parse_pbinding cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [patbind, e]] | tok `tm` tok_BINDING ->
      (,) (cb_parse_patbind patbind) (cb_parse_e e)
    _ -> error $ "cb_parse_pbinding failed: " ++ show cbor

  cb_parse_patbind cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array []]    | tok `tm` tok_WILDCARD -> EP_Wildcard (cb_parse_range cbr)
    CBOR_Array [tok, _,_cbr, CBOR_Array [pat]] | tok `tm` tok_TUPLE    -> cb_parse_p pat
    CBOR_Array [tok, _, cbr, CBOR_Array pats]  | tok `tm` tok_TUPLE    -> EP_Tuple    (cb_parse_range cbr) (map cb_parse_p pats)
    CBOR_Array [tok, _, cbr, CBOR_Array pats]  | tok `tm` tok_OR       -> EP_Or       (cb_parse_range cbr) (map cb_parse_p pats)
    CBOR_Array [tok, _, cbr, CBOR_Array [var]] | tok `tm` tok_TERMNAME -> EP_Variable (cb_parse_range cbr) (cb_parse_VarAST var)
    _ -> error $ "cb_parse_patbind failed: " ++ show cbor ++ " ;; " ++ headName cbor


  headName (CBOR_Array ((CBOR_UInt x) : _)) = tokNameOf x
  headName _ = ""

  cb_parse_phrase :: CBOR -> ExprAST TypeP
  cb_parse_phrase cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [lvalue]] | tok `tm` tok_PHRASE -> cb_parse_lvalue lvalue
    CBOR_Array [tok, _, cbr, CBOR_Array lvalues]  | tok `tm` tok_PHRASE -> cb_parse_call (annotOfCbr cbr) (map cb_parse_lvalue lvalues)
    CBOR_Array [tok, _,_cbr, CBOR_Array (nopr : mu_mb_tyapp : lvalues)] | tok `tm` tok_PRIMAPP ->
      cb_parse_primapp (cb_parse_Text nopr) (unMu mu_mb_tyapp) (map cb_parse_lvalue lvalues) (annotOfCbor cbor)
    _ -> error $ "cb_parse_phrase failed: " ++ show cbor

  cb_parse_Text cbor = case cbor of
    CBOR_Array [_tok, txt, _cbr, CBOR_Array []] -> cborText txt
    _ -> error $ "cb_parse_Text failed: " ++ show cbor

  cb_parse_primapp nopr mb_tyapp_cbor exprs annot =
    let tys = case mb_tyapp_cbor of
                [] -> []
                [tyapp] -> cb_parse_tyapp tyapp
                other   -> error $ "cb_parse_primapp tyapp: " ++ show other in
    parseCallPrim' nopr tys exprs annot

  cb_parse_call annot baseargs =
    case baseargs of
      (E_VarAST _ v : args) | evarName v == T.pack "|>" ->
        case args of
          -- foo froz |> bar baz ~~~> bar baz (foo froz)
          [eexpr, E_CallAST _rng subbase subargs] | not (Prelude.null subargs)
                        -> E_CallAST annot subbase (subargs ++ [eexpr])
          -- foo |> bar !   ~~~> (bar !) foo
          -- foo |> bar     ~~~> (bar  ) foo
          [eexpr, rest] -> E_CallAST annot rest [eexpr]
          _ -> error $ "cb_parse_call given unexpected args input: " ++ show args
      (base : args) -> E_CallAST annot base args
      _ -> error "cb_parse_call with no callee??"

  cb_parse_lvalue cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array (atom : suffixes)] | tok `tm` tok_LVALUE ->
      foldl' cb_parse_suffix (cb_parse_atom atom) suffixes
    _ -> error $ "cb_parse_lvalue failed: " ++ show cbor

  cb_parse_tyapp cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array tys] | tok `tm` tok_VAL_TYPE_APP -> map cb_parse_t tys
    _ -> error $ "cb_parse_tyapp failed: " ++ show cbor

  cb_parse_p cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array (dctor : patoms)]| tok `tm` tok_CTOR ->
        EP_Ctor (cb_parse_range cbr) (map cb_parse_patom patoms) (cb_parse_dctor dctor)
    CBOR_Array [tok, _, cbr, CBOR_Array pats] | tok `tm` tok_OR -> EP_Or (cb_parse_range cbr) (map cb_parse_p pats)
    CBOR_Array [_tokMU, _,_cbr, CBOR_Array [patom]] ->
        cb_parse_patom patom
    _ -> error $ "cb_parse_p failed: " ++ show cbor

  cb_parse_pmatch cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array [p, e, stmts]] | tok `tm` tok_CASE ->
        CaseArm (cb_parse_p p) (cb_parse_stmts stmts) (Just $ cb_parse_e e) [] (cb_parse_range cbr)
    CBOR_Array [tok, _, cbr, CBOR_Array [p, stmts]]    | tok `tm` tok_CASE ->
        CaseArm (cb_parse_p p) (cb_parse_stmts stmts) Nothing               [] (cb_parse_range cbr)
    _ -> error $ "cb_parse_pmatch failed: " ++ show cbor


  cb_parse_suffix expr cbor =
   let annot = annotOfCbor cbor in
   case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array []]  | tok `tm` tok_DEREF        -> E_DerefAST annot expr
    CBOR_Array [tok, _,_cbr, CBOR_Array [e]] | tok `tm` tok_SUBSCRIPT    -> parseCallPrim' (T.pack "subscript") [] [expr, cb_parse_e e] annot
    CBOR_Array [tok, _,_cbr, CBOR_Array []]  | tok `tm` tok_VAL_APP      -> E_CallAST annot expr []
    CBOR_Array [tok, _,_cbr, CBOR_Array tys] | tok `tm` tok_VAL_TYPE_APP -> E_TyApp annot expr (map cb_parse_t tys)
    _ -> error $ "cb_parse_suffix failed: " ++ show cbor

  unMu (CBOR_Array [_, _, _, CBOR_Array cbors]) = cbors
  unMu cbor = error $ "unMu give non-array: " ++ show cbor

  unMu1 x = case unMu x of [v] -> v
                           vs -> error $ "unMu1 expected one, got " ++ show vs

  cb_parse_range cbr = case cbr of
    CBOR_Array [startline, startcol, endline, endcol] ->
      case (cb_int startline, cb_int startcol, cb_int endline, cb_int endcol) of
        (startline, startcol, endline, endcol) ->
          SourceRange startline startcol endline endcol lines Nothing
    _ -> error $ "cb_parse_range had unexpected input: " ++ show cbr

  annotOfCbr  cbr  = ExprAnnot [] (cb_parse_range cbr) []
  annotOfCbor cbor = case cbor of
    CBOR_Array [_, _, cbr, _] -> annotOfCbr cbr
    _ -> error "annotOfCbor expeted CBOR_Array"

  isHashMark (CBOR_Array [tok, _, _cbr, _]) = tok `tm` tok_HASH_MARK
  isHashMark _ = False

  cb_parse_atom cbor =
   let annot = annotOfCbor cbor in
   case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [bool]] | tok `tm` tok_BOOL     -> cb_parse_bool (E_BoolAST annot) bool
    CBOR_Array [tok, _,_cbr, CBOR_Array [num]]  | tok `tm` tok_LIT_NUM  -> cb_parse_lit_num E_IntAST E_RatAST annot num
    CBOR_Array [tok, _,_cbr, CBOR_Array [quo, chrs]] | tok `tm` tok_STRING -> cb_parse_str quo chrs
    CBOR_Array [tok, _,_cbr, CBOR_Array [name]] | tok `tm` tok_TERMNAME -> cb_parse_termname name
    CBOR_Array [tok, _,_cbr, CBOR_Array (e : pmatches)] | tok `tm` tok_CASE -> E_Case annot (cb_parse_e e) (map cb_parse_pmatch pmatches)
    CBOR_Array [tok, _,_cbr, CBOR_Array [stmts]] | tok `tm` tok_COMPILES -> E_CompilesAST annot (Just $ cb_parse_stmts stmts)
    {-CBOR_Array [tok, _,_cbr, CBOR_Array [mu_bindings, stmts]] | tok `tm` tok_LETS   ->
        let mkLet s cb = E_LetAST (annotOfCbor cb) (cb_parse_binding cb) s in
        foldl' mkLet (cb_parse_stmts stmts) (reverse $ unMu mu_bindings)
    CBOR_Array [tok, _,_cbr, CBOR_Array [mu_bindings, stmts]] | tok `tm` tok_LETREC ->
        E_LetRec annot (map cb_parse_binding (unMu mu_bindings)) (cb_parse_stmts stmts)-}
    CBOR_Array [tok, _,_cbr, CBOR_Array cbors] | tok `tm` tok_TUPLE ->
      case cbors of
        []           -> E_TupleAST annot KindPointerSized []
        [stmts]      -> cb_parse_stmts stmts
        (hash:stmts:rest) | isHashMark hash ->
                        E_TupleAST annot KindAnySizeType  (cb_parse_stmts stmts : map cb_parse_e rest)
        (stmts:rest) -> E_TupleAST annot KindPointerSized (cb_parse_stmts stmts : map cb_parse_e rest)
    CBOR_Array [tok, _,_cbr, CBOR_Array [stmts, thenstmts]] | tok `tm` tok_IF ->
        E_IfAST annot (cb_parse_stmts stmts) (cb_parse_stmts thenstmts) (E_TupleAST annot KindPointerSized [])
    CBOR_Array [tok, _,_cbr, CBOR_Array [stmts, thenstmts, elsestmts]] | tok `tm` tok_IF ->
        E_IfAST annot (cb_parse_stmts stmts) (cb_parse_stmts thenstmts) (cb_parse_stmts elsestmts)
    CBOR_Array [tok, _,_cbr, CBOR_Array [stmts, t]] | tok `tm` tok_TYANNOT ->
        E_TyCheck annot (cb_parse_stmts stmts) (cb_parse_t t)
    CBOR_Array [tok, _,_cbr, CBOR_Array [mu_formals, mu_tyformals]]        | tok `tm` tok_VAL_ABS ->
        let name = T.empty in -- typechecking maintains the pending binding stack, and will update the fn name
        E_FnAST annot (FnAST annot name (map cb_parse_tyformal $ unMu mu_tyformals)
                                        (map cb_parse_formal   $ unMu mu_formals)
                                        (E_TupleAST annot KindPointerSized []) False)
    CBOR_Array [tok, _,_cbr, CBOR_Array [mu_formals, mu_tyformals, stmts]] | tok `tm` tok_VAL_ABS ->
        let name = T.empty in -- typechecking maintains the pending binding stack, and will update the fn name
        E_FnAST annot (FnAST annot name (map cb_parse_tyformal $ unMu mu_tyformals)
                                        (map cb_parse_formal   $ unMu mu_formals)
                                        (cb_parse_stmts stmts) False)

    CBOR_Array [tok, _,_cbr, CBOR_Array [action, mu_matches, mu_xform]] | tok `tm` tok_HANDLE ->
        E_Handler annot (cb_parse_e action)
                        (map cb_parse_pmatch $ unMu mu_matches)
                        (case unMu mu_xform of
                          [] -> Nothing
                          [xform] -> Just (cb_parse_e xform))

    _ -> error $ "cb_parse_atom failed: " ++ show cbor

  similarStmts (StmtExpr {})    (StmtExpr {})    = True
  similarStmts (StmtLetBind {}) (StmtLetBind {}) = True
  similarStmts (StmtRecBind {}) (StmtRecBind {}) = True
  similarStmts _ _ = False

  cb_parse_stmts :: CBOR -> ExprAST TypeP
  cb_parse_stmts cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array (stmt_ : stmt_conts)] | tok `tm` tok_STMTS ->
      let rev_parts = reverse $ cb_parse_stmt_ stmt_ : (map cb_parse_stmt_cont stmt_conts) in
      -- Collect consecutive blocks of rec- vs non-rec bindings.
      let rev_pparts = groupBy similarStmts rev_parts in

      -- Construct groups of let-bindings.
     let go [] [] expr = expr
         go [] (block:rest) expr = go block rest expr
         go block@(StmtRecBind annot _:_) rest expr =
           go [] rest (E_LetRec annot [TermBinding v body | StmtRecBind _annot (EP_Variable _ v, body) <- block] expr)
         go (thing:block) rest expr =
           go block rest (letbind thing expr)
         letbind (StmtExpr    annot e)                        expr = E_SeqAST annot e expr
         letbind (StmtLetBind annot (EP_Variable _ v, bound)) expr = E_LetAST annot (TermBinding v bound) expr
         letbind (StmtLetBind annot (pat, bound))             expr = E_Case   annot bound [CaseArm pat expr Nothing [] (rangeOf annot)]
         letbind (StmtRecBind _ _) _xpr = error "shouldn't happen"
       in
      case rev_pparts of
        ((StmtExpr _ expr:exprs):rest) -> go exprs rest expr
        -- TODO or use value of last binding?
        ((stmt:stmts):rest) -> go (stmt:stmts) rest (E_TupleAST (annotOfParsedStmt stmt) KindPointerSized [])
        _ -> error $ "Expected more statements!"
    _ -> error $ "cb_parse_stmts " ++ show cbor

  cb_parse_stmt_cont cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [_semi, stmt_]] | tok `tm` tok_MU ->
      cb_parse_stmt_ stmt_
    _ -> error $ "cb_parse_stmt_cont " ++ show cbor

  cb_parse_stmt_ cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [_rec, idbinding]] | tok `tm` tok_ABINDING ->
      StmtRecBind (annotOfCbor cbor) $ cb_parse_idbinding idbinding
    CBOR_Array [tok, _,_cbr, CBOR_Array [       pbinding]] | tok `tm` tok_ABINDING ->
      StmtLetBind (annotOfCbor cbor) $ cb_parse_pbinding pbinding
    _ -> StmtExpr (annotOfCbor cbor) $ cb_parse_e cbor

  cb_parse_e :: CBOR -> ExprAST TypeP
  cb_parse_e cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [mu_mb_opr, mu_phrase, mu_mb_binops]] | tok `tm` tok_TERM ->
      let base0 = cb_parse_phrase (unMu1 mu_phrase) in
      let base1 = case unMu mu_mb_opr of
                    [] -> base0
                    oprs -> error $ "cb_parse_e opr: " ++ show oprs in
      parseBinopChain base1 (unMu mu_mb_binops)
    _ -> error $ "cb_parse_e failed: " ++ show cbor

  parseBinopChain :: ExprAST TypeP -> [CBOR] -> ExprAST TypeP
  parseBinopChain base [] = base
  parseBinopChain base binops =
    let isOperatorish c = isPunctuation c || isSymbol c
        ifEmpty txt tt = if T.null tt then txt else tt
        oprPrefix txt = ifEmpty txt $ T.takeWhile isOperatorish txt
        varoppair cbor = case cbor of
            CBOR_Array [_, cbtxt,_cbr, CBOR_Array []] ->
               let txt = cborText cbtxt in
               VarOpPair (E_VarAST (annotOfCbor cbor) (VarAST Nothing txt)) (oprPrefix txt)
            _ -> error $ "Unable to parse var " ++ show cbor in
    let pairs = pairwise varoppair cb_parse_phrase binops in
    go [base] [] pairs
      where
        combineRanges :: SourceRanged a => a -> a -> SourceRange
        combineRanges x y = case (rangeOf x, rangeOf y) of
                              (rx, ry) ->
                               if sourceRangeFile rx == sourceRangeFile ry
                                then SourceRange (sourceRangeStartLine rx)
                                                 (sourceRangeStartCol  rx)
                                                 (sourceRangeEndLine   ry)
                                                 (sourceRangeEndCol    ry)
                                                 (sourceRangeLines     rx)
                                                 (sourceRangeFile      ry)
                                else error $ "combineRanges needs ranges from same file"

        combine x vop y =
          let annot = (ExprAnnot [] (combineRanges x y) []) in
          case vop of
            (VarOpPair _ o) | o == T.pack ">^" -> parseCallPrim' (T.pack "store") [] [x,y] annot
            (VarOpPair op _) -> cb_parse_call annot [op, x, y]
        leftAssoc (y:x:args) (op:ops) pairs = go ((combine x op y):args) ops pairs
        leftAssoc _ _ _ = error "leftAssoc invariant violated"

        push args ops ((op,e):pairs) = go (e:args) (op:ops) pairs
        push _ _ _ = error "push invariant violated"

        -- Invariant: len args == len ops + 1
        go :: [ExprAST TypeP] -> [VarOpPair] -> [(VarOpPair, ExprAST TypeP)] -> ExprAST TypeP
        go [arg] [] [] = arg
        go args ops [] = leftAssoc args ops []
        go args [] pairs = push    args [] pairs
        go args ops@((VarOpPair _ preX):_) pairs@(((VarOpPair _ preY),_):_) =
          case precedence preX preY of
            OpPrecTighter -> leftAssoc args ops pairs
            _             -> push      args ops pairs

        precedence x y | x == T.pack "|>"
                      && y == T.pack "|>" = OpPrecTighter
        precedence x _ | x == T.pack "|>" = OpPrecLooser
        precedence _ y | y == T.pack "|>" = OpPrecTighter
        precedence x y =
          case lookup (x,y) defaultPrecedenceTable of
            Just p -> p
            Nothing -> OpPrecOther

        defaultPrecedenceTable =
             tighter ["*"]      ["+"]
          ++ tighter ["*", "+"] ["<", "<=", ">", ">="]
          ++ tighter ["*", "+",  "<", "<=", ">", ">="]      ["==", "!="]
          ++ leftassoc ["*", "/"]
          ++ leftassoc ["+", "-"]
          ++ nonassoc ["==", "!="]
          ++ nonassoc ["<", "<=", ">", ">="]

        tighter tops lops = [((T.pack top, T.pack lop), OpPrecTighter) | top <- tops, lop <- lops]
                         ++ [((T.pack lop, T.pack top), OpPrecLooser)  | top <- tops, lop <- lops]
        leftassoc ops = [((T.pack x, T.pack y), OpPrecTighter) | x <- ops, y <- ops]
        nonassoc  ops = [((T.pack x, T.pack y), OpPrecOther)   | x <- ops, y <- ops]

  pairwise :: (a -> b) -> (a -> c) -> [a] -> [ (b, c) ]
  pairwise _ _ [] = []
  pairwise f g (a:b:rest) = (f a, g b):pairwise f g rest
  pairwise _ _ _ = error "pairwise given list of odd length"

  cb_parse_patom cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array []]   | tok `tm` tok_WILDCARD -> EP_Wildcard (cb_parse_range cbr)
    CBOR_Array [tok, _, cbr, CBOR_Array [x]]  | tok `tm` tok_TERMNAME -> EP_Variable (cb_parse_range cbr) (cb_parse_VarAST x)
    CBOR_Array [tok, _,_cbr, CBOR_Array [pat]] | tok `tm` tok_TUPLE -> cb_parse_p pat
    CBOR_Array [tok, _, cbr, CBOR_Array pats]  | tok `tm` tok_TUPLE -> EP_Tuple (cb_parse_range cbr) (map cb_parse_p pats)
    CBOR_Array [tok, _, cbr, CBOR_Array [dctor]] | tok `tm` tok_CTOR -> EP_Ctor (cb_parse_range cbr) [] (cb_parse_dctor dctor)
    CBOR_Array [tok, _, cbr, CBOR_Array [num]]   | tok `tm` tok_LIT_NUM -> cb_parse_lit_num EP_Int EP_Int (cb_parse_range cbr) num
    CBOR_Array [tok, _, cbr, CBOR_Array [bool]]  | tok `tm` tok_BOOL    -> cb_parse_bool    (EP_Bool (cb_parse_range cbr)) bool
    _ -> error $ "cb_parse_patom failed: " ++ show cbor


  cb_parse_bool ctor cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array []] | tok `tm` tok_TRU -> ctor True
    CBOR_Array [tok, _,_cbr, CBOR_Array []] | tok `tm` tok_FLS -> ctor False
    _ -> error $ "cb_parse_bool failed: " ++ show cbor


  cb_parse_binding cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [x, e]] | tok `tm` tok_BINDING ->
      TermBinding (cb_parse_x_VarAST x) (cb_parse_e e)
    _ -> error $ "cb_parse_binding failed: " ++ show cbor


  cb_parse_formal cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [xid]]    | tok `tm` tok_FORMAL ->
      let t = MetaPlaceholder ".inferred" in -- TODO
      TypedId t (Ident (cb_parse_x_text xid) 0)
    CBOR_Array [tok, _,_cbr, CBOR_Array [xid, t]] | tok `tm` tok_FORMAL ->
      TypedId (cb_parse_t t) (Ident (cb_parse_x_text xid) 0)
    _ -> error $ "cb_parse_formal failed: " ++ show cbor


  cb_parse_tyformal cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array [aid, k]] | tok `tm` tok_TYPEVAR_DECL ->
      TypeFormal (cb_parse_aid aid) (cb_parse_range cbr) (cb_parse_k k)
    CBOR_Array [tok, _, cbr, CBOR_Array [aid]]    | tok `tm` tok_TYPEVAR_DECL ->
      TypeFormal (cb_parse_aid aid) (cb_parse_range cbr) KindPointerSized
    _ -> error $ "cb_parse_tyformal failed: " ++ show cbor

  cb_parse_t :: CBOR -> TypeP
  cb_parse_t cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [xid, tp, e]] | tok `tm` tok_REFINED ->
      RefinedTypeP (cb_parse_x_str xid) (cb_parse_tp tp) (cb_parse_e e)
    _ -> cb_parse_tp cbor

  cb_parse_tp :: CBOR -> TypeP
  cb_parse_tp cbor = case cbor of
    CBOR_Array [tok, _,_cbr, CBOR_Array [tatom]] | tok `tm` tok_TYPE_ATOM -> cb_parse_tatom tatom
    CBOR_Array [tok, _,_cbr, CBOR_Array (tatom : tatoms)] | tok `tm` tok_TYPE_TYP_APP ->
      let tys = map cb_parse_tatom tatoms in
      case tatom of
        CBOR_Array [tik, _, _, CBOR_Array [name]] | tik `tm` tok_TYPENAME ->
          TyAppP (TyConP $ cb_parse_typename name) tys
        _ -> error $ "tp (cb_parse_tatom tatom) (map cb_parse_tatom tatoms)" ++ show tatom
    CBOR_Array [tok, _,_cbr, CBOR_Array args] | tok `tm` tok_FORALL_TYPE ->
      let (tyformals, t) = (init args, last args) in
      ForAllP (map cb_parse_tyformal tyformals) (cb_parse_t t)
    _ -> error $ "cb_parse_tp failed: " ++ show cbor

  unTuple cbor = case cbor of
    CBOR_Array [tok, _, _, CBOR_Array vals] | tok `tm` tok_TUPLE -> vals
    _ -> error $ "unTuple given " ++ show cbor

  cb_ty_of_str cbr name@(c:_) =
      if isLower c
        then TyVarP (BoundTyVar name (cb_parse_range cbr))
        else TyAppP (TyConP name) []
  cb_ty_of_str _ [] = error $ "cb_ty_of_str cannot parse empty name!"

  cb_parse_tatom cbor = case cbor of
    CBOR_Array [tok, _, cbr, CBOR_Array [typename]] | tok `tm` tok_TYPENAME ->
      cb_ty_of_str cbr (cb_parse_typename typename)
    CBOR_Array [tok, _,_cbr, CBOR_Array [a]] | tok `tm` tok_TYPE_PLACEHOLDER ->
      MetaPlaceholder (cb_parse_aid a)
    CBOR_Array [tok, _,_cbr, CBOR_Array [t]] | tok `tm` tok_TUPLE -> cb_parse_t t
    CBOR_Array [tok, _,_cbr, CBOR_Array (hash:tys)] | tok `tm` tok_TUPLE && isHashMark hash
                                                                  -> TupleTypeP KindAnySizeType  (map cb_parse_t tys)
    CBOR_Array [tok, _,_cbr, CBOR_Array tys] | tok `tm` tok_TUPLE -> TupleTypeP KindPointerSized (map cb_parse_t tys)
    CBOR_Array [tok, _, cbr, CBOR_Array [tuple, _mu, mu_eff]]        | tok `tm` tok_FUNC_TYPE ->
        let tys = map cb_parse_t (unTuple tuple) in
        let eff = let effp = map cb_parse_eff (unMu mu_eff) in
                  case effp of
                    [] -> Nothing
                    [eff] -> Just eff
                    _ -> trace ("Warning: dropping multi-parsed-effects: " ++ show effp) Nothing in
        FnTypeP (init tys) (last tys) eff FastCC FT_Func (cb_parse_range cbr)
    CBOR_Array [tok, _, cbr, CBOR_Array [tuple, _mu, _eff, tannots]] | tok `tm` tok_FUNC_TYPE ->
        let annots = cb_parse_tannots tannots in
        let (cc, ft) = extractFnInfoFromAnnots annots in
        let tys = map cb_parse_t (unTuple tuple) in
        FnTypeP (init tys) (last tys) Nothing cc ft (cb_parse_range cbr)
    _ -> error $ "cb_parse_tatom failed: " ++ show cbor

  cb_parse_eff :: CBOR -> Effect
  cb_parse_eff cbor = case cbor of
    CBOR_Array [tok_row,_,_cbr,CBOR_Array (a:tatoms)] | tok_row `tm` tok_EFFECT_SINGLE ->
      case tatoms of
        [] -> effectSingle (cb_ty_of_a _cbr a)
        _ ->  effectSingle (TyAppP (cb_ty_of_a _cbr a) (map cb_parse_tatom tatoms))
          
    CBOR_Array [tok_row,_,_cbr,CBOR_Array rowsyntax] | tok_row `tm` tok_EFFECT_ROW ->
      case rowsyntax of
        [] ->        effectsClosed []
        [mu_effs] -> effectsClosed (map cb_parse_single_effect (unMu mu_effs))
        [mu_effs, mu_aidq] ->
           case unMu mu_aidq of
             [] -> effectsClosed  (map cb_parse_single_effect (unMu mu_effs))
             [aid] ->
                   effectsExtends (map cb_parse_single_effect (unMu mu_effs))
                                  (cb_ty_of_a _cbr aid)
             other -> error $ "cb_parse_eff_ext failed: " ++ show other
        _ -> error $ "cb_parse_eff_rowsyntax failed: " ++ show cbor
    _ -> error $ "cb_parse_eff failed: " ++ show cbor

  cb_ty_of_a :: CBOR -> CBOR -> TypeP
  cb_ty_of_a cbr a = cb_ty_of_str cbr (cb_parse_aid a)

  cb_parse_single_effect :: CBOR -> TypeP
  cb_parse_single_effect cbor = case cbor of
    CBOR_Array [tok,_, cbr,CBOR_Array axs] | tok `tm` tok_EFFECT_SINGLE ->
      case axs of
        [a]    -> cb_ty_of_a cbr a
        (a:xs) -> let (TyAppP tcon []) = cb_ty_of_a cbr a in
                       TyAppP tcon (map cb_parse_tatom xs) -- TODO handle minus
        [] -> error $ "cb_parse_single_eff_empty failed: " ++ show cbor
    _ -> error $ "cb_parse_single_effect failed: " ++ show cbor

  extractFnInfoFromAnnots annots =
      if (T.pack "proc", T.pack "true") `elem` annots
        then (CCC   , FT_Proc)
        else (FastCC, FT_Func)

  cb_parse_tannots cbor = case cbor of
    CBOR_Array [tok, _, _cbr, CBOR_Array bindings] | tok `tm` tok_BINDING ->
      [(evarName v, evarName x) | TermBinding v (E_VarAST _ x) <- map cb_parse_binding bindings]
    _ -> error $ "cb_parse_tannots failed: " ++ show cbor

  -- TODO parse different escapes, etc.
  cb_parse_str quo chrs = case (quo, chrs) of
    (CBOR_Array [tok, _, _, CBOR_Array []], CBOR_Array [_, val, cbr, _]) ->
      E_StringAST (annotOfCbor chrs) $ cb_parse_str' tok (T.unpack $ cborText val) (cb_parse_range cbr)
    _ -> error $ "cb_parse_str failed: " ++ show cbor

  cb_parse_str' tok str range =
    let (isBytes, isRaw, strFromQuotes) = case str of
          ('b':'r':rest) -> (True, True, rest)
          ('r':'b':rest) -> (True, True, rest)
          ('r':rest)     -> (False, True, rest)
          ('b':rest)     -> (True, False, rest)
          _              -> (False, False, str)
        quotesLen = if tok `tm` tok_TDQU || tok `tm` tok_TRTK then 3 else 1
        bodyLen = length strFromQuotes - (quotesLen * 2)
        strWithoutQuotes = take bodyLen (drop quotesLen strFromQuotes)
        hexbits c = if isHexDigit c then
                       digitToInt c else error $ "expected hex digit, got " ++ show c
        byteOfChars hi lo = chr $ (16 * hexbits hi) + hexbits lo
        tryChr codepoint =
              if codepoint < 0xD800
             || (codepoint >= 0xE000 && codepoint <  0xFDD0)
             || (codepoint >  0xFDEF && codepoint <= 0x10FFFF
                            && (codepoint .&. 0xFFFE) /= 0xFFFE)
               then Just (chr codepoint)
               else Nothing
        charOfStuff stuff orig =
          if all isHexDigit stuff
           then if length stuff <= 6
                  then case readHex stuff of
                        [(codepoint, "")] ->
                          case tryChr codepoint of
                            Just c -> c
                            Nothing -> error $ "Invalid codepoint..."
                        parses -> error $ "Expected one parse for " ++ show stuff ++ " but got " ++ show parses
                  else error $ "Unicode escapes can have at most 6 hex digits.\nHad: " ++ show stuff ++
                                "\nOrig is:\n" ++ showSourceRange range
           else error $ "Parsing non-hex unicode character names is a TODO"
        parse isBytes orig =
          let go [] acc = reverse acc
              go ('\\':'r':rest) acc = go rest ('\r':acc)
              go ('\\':'t':rest) acc = go rest ('\t':acc)
              go ('\\':'n':rest) acc = go rest ('\n':acc)
              go ('\\':'"':rest) acc = go rest ('"':acc)
              go ('\\':'\\':rest) acc = go rest ('\\':acc)
              go ('\n':          rest) acc | isBytes = go rest acc -- ignore newlines in byte literals
              go ('\\':'x':hi:lo:rest) acc | isBytes = go rest (byteOfChars hi lo:acc)
              go ('\\':'u':'{':rest) acc = let (stuff, ('}':post)) = break (== '}') rest
                                           in  go post (charOfStuff stuff orig:acc)
              -- go ('\\':'\'':rest) acc = go rest ('\'':acc)
              go (c:rest) acc | c /= '\\' = go rest (c:acc)
              go s _ = error $ "Unable to parse string " ++ show orig ++ " starting at " ++ show s
          in go orig []
     in
    case (isRaw, isBytes) of
      (True, True)   -> SS_Bytes YesRaw $ BS.pack strWithoutQuotes
      (True, False)  -> SS_Text  YesRaw $  T.pack strWithoutQuotes
      (False, True)  -> SS_Bytes NotRaw $ BS.pack $ parse isBytes strWithoutQuotes
      (False, False) -> SS_Text  NotRaw $  T.pack $ parse isBytes strWithoutQuotes

  cb_parseInclude cbor = case cbor of
    CBOR_Array [tok, _, _cbr, CBOR_Array [CBOR_Array [_, ts_ident, _cbr_i, _],
                                                     CBOR_Array [_, ts_path , _cbr_p, _]]]
      | tok `tm` tok_SNAFUINCLUDE ->
            (cborText ts_ident, cborText ts_path)
    _ -> error $ "cb_parseIncludes failed"

  cb_parseIncludes cbor = case cbor of
    CBOR_Array [tok, _, _, CBOR_Array includes] | tok `tm` tok_SNAFUINCLUDE ->
      map cb_parseInclude includes
    _ -> error $ "cb_parseIncludes failed"

processArrayValue :: ExprAST TypeP -> ArrayEntry (ExprAST TypeP)
processArrayValue (E_IntAST annot t) = AE_Int annot t
processArrayValue expr = AE_Expr expr

mkPrimCall :: String -> [Literal] -> [TypeP] -> [ExprAST TypeP] -> ExprAnnot -> ExprAST TypeP
mkPrimCall name lits tys args annot =
    let emptyAnnot = annotForRange (MissingSourceRange "prim") in
    E_CallAST annot (E_PrimAST emptyAnnot name lits tys) args

parseCallPrim' primname tys args annot = do
    let fixupSubscriptRanges (E_ArrayRead (ExprAnnot pc r tc) (ArrayIndex a b rng sg)) =
          let r' = rangeUnions r [rangeOf a, rangeOf b, r, rng]
              annot' = ExprAnnot pc r' tc in
          E_ArrayRead annot' (ArrayIndex a b rng sg)
        fixupSubscriptRanges _ = error $ "fixupSubscriptRanges needs an ArrayRead"

    case (T.unpack primname, args) of
      ("assert-invariants", _) -> mkPrimCall "assert-invariants" [] [] args annot
      ("mach-array-literal", _) -> case tys of
                                    []   -> E_MachArrayLit annot Nothing   (map processArrayValue args)
                                    [ty] -> E_MachArrayLit annot (Just ty) (map processArrayValue args)
                                    _    -> error $ "ProtobufFE: prim mach-array-literal takes at most one type argument"
      ("tuple",  _ ) -> E_TupleAST annot KindPointerSized args
      ("tuple-unboxed",  _ ) -> E_TupleAST annot KindAnySizeType args
      ("deref", [e]) -> E_DerefAST annot e
      ("ref",             [e]) -> E_AllocAST annot e MemRegionGlobalHeap
      ("stackref-unsafe", [e]) -> E_AllocAST annot e MemRegionStack
      ("subscript",  [a,b])        -> fixupSubscriptRanges $ E_ArrayRead annot (ArrayIndex a b (rangeOf annot) SG_Dynamic)
      ("subscript-unsafe",  [a,b]) -> fixupSubscriptRanges $ E_ArrayRead annot (ArrayIndex a b (rangeOf annot) SG_Unsafe)
      ("subscript-static",  [a,b]) -> fixupSubscriptRanges $ E_ArrayRead annot (ArrayIndex a b (rangeOf annot) SG_Static)
      ("store",[a,b])-> case b of -- a >^ c[d]
                           E_ArrayRead _ ari -> E_ArrayPoke annot ari a
                           _                 -> E_StoreAST annot a b
      ("kill-entire-process",  [s@(E_StringAST {})]) ->
                                                E_KillProcess annot s
      ("inline-asm", _) ->
        case (tys, args) of
          ([_], E_StringAST _ (SS_Text _ cnt) : E_StringAST _ (SS_Text _ cns) : E_BoolAST _ sideeffects : args' ) -> do
            let prim = (E_PrimAST annot "inline-asm"
                           [LitText cnt, LitText cns, LitBool sideeffects] tys)
            E_CallAST annot prim args'
          _ -> error $ "ProtobufFE: inline-asm requires a fn type, two string literals, and a bool"

      (name, args) ->
        case (tys, Map.lookup name gFosterPrimOpsTable) of
          ([], Just _) -> mkPrimCall name [] [] args annot
          _ ->
            error $ "ProtobufFE: unknown primitive/arg combo " ++ show primname
                    ++ "\n" ++ showSourceRange (rangeOf annot)


cb_int :: CBOR -> Int
cb_int cbor = case cbor of
    CBOR_UInt integer -> fromIntegral integer
    CBOR_SInt integer -> fromIntegral integer
    CBOR_Byte word8   -> fromIntegral word8
    _ -> error $ "cb_int had unexpected input: " ++ show cbor

-- {{{
type Effect = TypeP
effectSingle :: Effect -> Effect
effectSingle eff =
  case eff of
    TyAppP {} -> effectExtend eff nullFx
    TyVarP {} -> eff -- Type variables are treated as rows rather than labels.
    _ -> error $ "ProtobufFE.hs: effectSingle given " ++ show eff

effectExtend :: Effect -> Effect -> Effect
effectExtend label row = TyAppP (TyConP "effect.Extend") [label, row]

effectsExtends :: [Effect] -> Effect -> Effect
effectsExtends labels row = foldr effectExtend row labels

effectsClosed :: [Effect] -> Effect
effectsClosed effs = effectsExtends effs nullFx

nullFx = TyAppP (TyConP "effect.Empty") []
-- }}}

-- {{{
data SourceLoc = SourceLoc !Int !Int

type FmtState a = State (Seq.Seq (SourceLoc, Formatting)) a

-- The front-end produces an abstract syntax tree with position information
-- but without "hidden" tokens like newlines and comments. Such tokens are
-- instead produced in a separate list, off to the side. Our task is then to
-- take each hidden token and attach it to the parsed AST, based on the range
-- information embedded in the AST and the hidden tokens.

resolveFormatting :: [CBOR] -> ModuleExpr TypeP -> ModuleExpr TypeP
resolveFormatting hiddentokens m =
   m { moduleASTitems = evalState
                              (mapM attachFormattingItem (moduleASTitems m))
                              (Seq.fromList $ map p hiddentokens) }
 where loc lineno charpos = SourceLoc (cb_int lineno) (cb_int charpos)
       p cbor = case cbor of
          CBOR_Array [_comment, lineno, charpos, txt] ->
             (loc lineno charpos, Comment (T.unpack $ cborText txt))
          CBOR_Array [thing,    lineno, charpos] ->
            case T.unpack $ cborText thing of
                "NEWLINE" -> (loc lineno charpos, BlankLine)
                _ -> error $ "resolveFormatting encountered unexpected hidden token type"
          _ -> error $ "resolveFormatting encountered unexpected hidden token: " ++ show cbor

getPreFormatting :: ExprAnnot -> FmtState ExprAnnot
getPreFormatting (ExprAnnot (_:_) _ _) = error $ "ExprAnnot should not have any pre-formatting yet!"
getPreFormatting (ExprAnnot [] rng post) = do
 fs <- get
 let prefilter (loc, _      ) = loc `beforeRangeStart` rng
 let (pre, rest) = Seq.spanl prefilter fs
 put rest
 return (ExprAnnot (map snd $ toList pre) rng post)

getPostFormatting :: ExprAnnot -> FmtState ExprAnnot
getPostFormatting (ExprAnnot _ _ (_:_)) = error $ "ExprAnnot should not have any post-formatting yet!"
getPostFormatting (ExprAnnot pre0 rng []) = do
 fs <- get
 if Seq.null fs
   then return (ExprAnnot pre0 rng [])
   else do
      let
          prefilter (loc, _ ) = loc `beforeRangeEnd` rng

          (post, rest) = Seq.spanl prefilter fs

          -- onlyComments (_, Comment _) = True
          -- onlyComments (_, _)         = False

          -- (pre, rest0) = span prefilter fs
          -- (post, rest) = span onlyComments rest0
      put rest
      return (ExprAnnot (pre0) rng (map snd $ toList post))

beforeRangeStart _ (MissingSourceRange _) = False
beforeRangeStart (SourceLoc line col) (SourceRange bline bcol _ _ _ _) =
        line <  bline
    || (line == bline && col < bcol)

beforeRangeEnd _ (MissingSourceRange _) = False
beforeRangeEnd (SourceLoc line col) (SourceRange _ _ eline ecol _ _) =
        line <  eline
    || (line == eline && col < ecol)

rangeSpanNextLine (SourceRange sl sc el _ec lines file) =
                  SourceRange sl sc (el + 1) 0 lines file
rangeSpanNextLine sr = sr

attachFormattingFn :: FnAST TypeP -> FmtState     (FnAST TypeP)
attachFormattingFn fn = do
 a0 <- getPreFormatting  (fnAstAnnot fn)
 b  <- attachFormatting  (fnAstBody  fn)
 an <- getPostFormatting a0
 return $ fn { fnAstAnnot = an, fnAstBody = b }

attachFormattingItem (ToplevelDefn (s,e)) = do
  ef <- attachFormatting e; return $ ToplevelDefn (s, ef)
attachFormattingItem (ToplevelDecl de) = return $ ToplevelDecl de
attachFormattingItem (ToplevelData dt) = return $ ToplevelData dt
attachFormattingItem (ToplevelEffect et) = return $ ToplevelEffect et

-- patterns have source ranges, not annotations.
convertTermBinding (TermBinding evar expr) =
             liftM (TermBinding evar) (attachFormatting expr)

attachFormatting :: ExprAST TypeP -> FmtState     (ExprAST TypeP)
attachFormatting (E_SeqAST annot a b) = do
 a' <- attachFormatting a
 ExprAnnot pre  rng [] <- getPreFormatting annot
 ExprAnnot pre' _ post <- getPostFormatting (ExprAnnot pre (rangeSpanNextLine rng) [])
 b' <- attachFormatting b
 return $ E_SeqAST (ExprAnnot pre' rng post) a' b'

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
   E_PrimAST      _ nm ls ts -> liftM4' E_PrimAST     ana (return nm) (return ls) (return ts)
   E_MachArrayLit _ mbt args -> liftM3' E_MachArrayLit ana (return mbt) (mapM (liftArrayEntryM q) args)
   E_KillProcess  _ e        -> liftM2' E_KillProcess ana (q e)
   E_CompilesAST  _ me       -> liftM2' E_CompilesAST ana (liftMaybeM q me)
   E_IfAST        _ a b c    -> liftM4' E_IfAST       ana (q a) (q b) (q c)
   E_SeqAST {}               -> undefined
   E_AllocAST     _ a rgn    -> liftM3' E_AllocAST    ana (q a) (return rgn)
   E_DerefAST     _ a        -> liftM2' E_DerefAST    ana (q a)
   E_StoreAST     _ a b      -> liftM3' E_StoreAST    ana (q a) (q b)
   E_TyApp        _ a tys    -> liftM3' E_TyApp       ana (q a) (return tys)
   E_TyCheck      _ a ty     -> liftM3' E_TyCheck     ana (q a) (return ty )
   E_TupleAST     _ k  exprs -> liftM3' E_TupleAST    ana (return k) (mapM q exprs)
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
   E_Handler      _ e bs mbe -> do e' <- q e
                                   bs' <- mapM (\(CaseArm pat exp guard bindings rng) -> do
                                      exp'   <-           q exp
                                      guard' <- liftMaybe q guard
                                      return (CaseArm pat exp' guard' bindings rng)) bs
                                   x' <- liftMaybe q mbe
                                   an <- ana
                                   return $ E_Handler an e' bs' x'
   E_Case         _ e bs     -> do e' <- q e
                                   bs' <- mapM (\(CaseArm pat exp guard bindings rng) -> do
                                                       exp'   <-           q exp
                                                       guard' <- liftMaybe q guard
                                                       return (CaseArm pat exp' guard' bindings rng)) bs
                                   an <- ana
                                   return $ E_Case an e' bs'

liftM2' f a b     = do b' <- b;                   a' <- a; return $ f a' b'
liftM3' f a b c   = do b' <- b; c' <- c;          a' <- a; return $ f a' b' c'
liftM4' f a b c d = do b' <- b; c' <- c; d' <- d; a' <- a; return $ f a' b' c' d'


liftMaybeM :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
liftMaybeM f m = case m of Nothing ->         return Nothing
                           Just t  -> f t >>= return.Just
-- }}}

cborText :: CBOR -> T.Text
cborText (CBOR_BS bs) = TE.decodeUtf8 bs
cborText (CBOR_TS ts) = TE.decodeUtf8 ts
cborText _ = error "cborText needs bytes"

data OpPrec =
    OpPrecTighter
  | OpPrecLooser
  | OpPrecOther
  deriving Show

data VarOpPair = VarOpPair (ExprAST TypeP) T.Text

data ParsedStmt =
    StmtExpr    ExprAnnot (ExprAST TypeP)
  | StmtLetBind ExprAnnot (EPattern TypeP, ExprAST TypeP)
  | StmtRecBind ExprAnnot (EPattern TypeP, ExprAST TypeP)
  deriving Show

annotOfParsedStmt ps = case ps of
  StmtExpr    annot _ -> annot
  StmtLetBind annot _ -> annot
  StmtRecBind annot _ -> annot

makeProcsWithin :: TypeP -> TypeP  
makeProcsWithin typ = go typ where
  go x = case x of
    TyConP    _nm                 -> x
    TyAppP    con types           -> TyAppP (go con) (map go types)
    TupleTypeP k  types           -> TupleTypeP k (map go types)
    FnTypeP    s t fx cc _pf src -> FnTypeP (map go s) (go t) (fmap go fx) CCC FT_Proc src
    ForAllP  tvs rho              -> ForAllP tvs (go rho)
    TyVarP   {}                   -> x
    MetaPlaceholder {}            -> x
    RefinedTypeP nm ty _e         -> RefinedTypeP nm (go ty) _e
