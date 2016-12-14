module Foster.FromHaskell (convertHaskellToFoster) where

import Language.Haskell.Exts.SrcLoc
import Language.Haskell.Exts.Simple.Parser
import Language.Haskell.Exts.Simple.Pretty (prettyPrint)
import qualified Language.Haskell.Exts.Simple.Syntax as H
import Language.Haskell.Exts.Simple(parseFile)

import qualified Data.Text as T
import Control.Monad.State(forM, forM_)

import Text.PrettyPrint.ANSI.Leijen((<+>), (<>), (<$>), pretty, text, line,
                                     hsep, fill, parens, vcat, list, red,
                                     plain)

import Foster.Base
import Foster.ExprAST
import Foster.ParsedType
import Foster.PrettyExprAST(prettyTopLevelFn)

convertHaskellToFoster hspath fosterpath = do
  res <- parseFile hspath
  writeFile fosterpath ""

  let noRange = MissingSourceRange ""
      noAnnot = ExprAnnot [] noRange []

  let isVar pat =
        case pat of
          H.PVar _ -> True
          _        -> False

      renameIdent "Nothing" = "None"
      renameIdent "Just" = "Some"
      renameIdent s = s

      rename (H.Ident s) = renameIdent s
      rename (H.Symbol s) = s

  let
      expOfQName qname = case qname of
        H.Qual modname name ->
            E_VarAST noAnnot (VarAST Nothing (T.pack $ prettyPrint modname ++ "_" ++ rename name))
        H.UnQual name -> E_VarAST noAnnot (VarAST Nothing (T.pack $ rename name))

        H.Special sp ->
          case sp of
            H.UnitCon     -> E_TupleAST noAnnot (error "kind3") []
            H.ListCon     -> error $ "H.ListCon"
            H.FunCon      -> error $ "H.FunCon"
            H.TupleCon {} -> error $ "H.TupleCon"
            H.Cons        -> error $ "H.Cons"
            H.UnboxedSingleCon -> error $ "H.UnboxedSC"

      app :: H.Exp -> [H.Exp] -> ExprAST TypeP
      app e es = case e of
        H.App e1 e2 -> app e1 (e2:es)

        H.Var (H.UnQual (H.Symbol "$")) -> app (head es) (tail es)
        H.Var qname -> E_CallAST noAnnot (expOfQName qname) (map expOfExp es)
        H.Con (H.Special (H.TupleCon _boxed _n)) -> E_TupleAST noAnnot (error "kind2") (map expOfExp es)
        H.Con (H.Special H.Cons)     -> E_CallAST noAnnot (E_VarAST noAnnot (VarAST Nothing (T.pack "Cons"))) (map expOfExp es)

        _ -> E_CallAST noAnnot (expOfExp e) (map expOfExp es)

      mkLet [] e = e
      mkLet (d:decls) e =
        case d of
          H.PatBind (H.PVar v) rhs _mb_binds ->
               mkLet decls (E_LetAST noAnnot (TermBinding (VarAST Nothing (T.pack $ rename v)) (expOfRhs rhs)) e)
          _ -> mkLet decls e

      expOfExp :: H.Exp -> ExprAST TypeP
      expOfExp exp = case exp of
        H.Var qname -> expOfQName qname
        H.Con qname -> expOfQName qname
        H.Lit (H.Int i)     -> E_IntAST noAnnot (show i)
        H.Lit (H.PrimInt i) -> E_IntAST noAnnot (show i)
        H.Lit (H.String s)  -> E_StringAST noAnnot False (SS_Text $ T.pack s)

        H.App e1 e2 -> app e1 [e2]

        H.Tuple _boxed exps -> E_TupleAST noAnnot (error "kind1") (map expOfExp exps)
        H.If c t e -> E_IfAST noAnnot (expOfExp c) (expOfExp t) (expOfExp e)

        H.List exps ->
          E_MachArrayLit noAnnot Nothing [AE_Expr (expOfExp e) | e <- exps]

        H.Paren e -> expOfExp e
        H.Lambda pats body -> E_FnAST noAnnot $ fnOfLambda "" pats (expOfExp body) False
        H.Case exp alts -> E_Case noAnnot (expOfExp exp) (map caseArmOfAlt alts)
        H.InfixApp e1 qop e2 ->
          case qop of
            H.QVarOp qnm -> app (H.Var qnm) [e1, e2]
            H.QConOp qnm -> app (H.Con qnm) [e1, e2]
            _ -> error $ "expOfExp.InfixApp " ++ show [prettyPrint e1, prettyPrint  qop, prettyPrint e2]

        H.ExpTypeSig e _ty ->
          --E_TyCheck noAnnot (expOfExp e) (typOfTyp ty)
          expOfExp e

        H.Let (H.BDecls decls) e -> mkLet decls (expOfExp e)

        H.EnumFrom {} -> E_VarAST noAnnot (VarAST Nothing (T.pack $ "/* " ++ prettyPrint exp ++ " */"))
        H.ListComp {} -> E_VarAST noAnnot (VarAST Nothing (T.pack $ "/* " ++ prettyPrint exp ++ " */"))

        _ -> error $ "expOfExp: " ++ prettyPrint exp

      caseArmOfAlt alt =
        case alt of
          H.Alt pat (H.UnGuardedRhs exp) _mb_binds -> CaseArm (patOfPat pat) (expOfExp exp) Nothing [] noRange
          H.Alt pat (H.GuardedRhss rhss) _mb_binds -> error $ "caseArmOfAlt.guarded"

      expOfRhs rhs = case rhs of
        H.UnGuardedRhs exp -> expOfExp exp
        H.GuardedRhss grhss -> error $ "expOfRhs.Guarded"

      patOfPat p =
        case p of
          H.PVar nm   -> EP_Variable noRange (VarAST Nothing (T.pack $ prettyPrint nm))
          H.PWildCard -> EP_Wildcard noRange
          H.PParen p  -> patOfPat p
          H.PTuple _boxed pats -> EP_Tuple noRange (map patOfPat pats)
          H.PLit _sign (H.Int i)     -> EP_Int noRange (show i)
          H.PLit _sign (H.PrimInt i) -> EP_Int noRange (show i)
          H.PIrrPat p  -> patOfPat p
          H.PBangPat p -> patOfPat p
          H.PApp qname pats ->
            EP_Ctor noRange (map patOfPat pats) (T.pack $ prettyPrint qname)

          H.PAsPat name pat -> error $ "patOfPat.AsPat: " ++ prettyPrint p
          H.PatTypeSig {} -> error $ "patOfPat.PatTypeSig: " ++ prettyPrint p
          H.PRPat {} -> error $ "patOfPat.PRPat: " ++ prettyPrint p
          H.PViewPat {} -> error $ "patOfPat.PViewPat: " ++ prettyPrint p
          H.PList {} -> error $ "patOfPat.PList: " ++ prettyPrint p
          H.PRec {} -> error $ "patOfPat.PRec: " ++ prettyPrint p
          H.PInfixApp {} -> error $ "patOfPat.PInfixApp: " ++ prettyPrint p
          _ -> error $ "patOfPat: " ++ prettyPrint p

      fnOfLambda nameStr pats body isToplevel =
        let (args', body') =
              if all isVar pats
                then let args = [prettyPrint name | H.PVar name <- pats] in
                     (args, body)
                     -- { patVars => body }
                     -- { genArgs => case genArgs of pats -> body end }
                else let args = ["arg" ++ show n | (_, n) <- zip pats [0..]] in
                     let bod  = case (args, pats) of
                                 ([arg], [pat]) ->
                                      (E_Case noAnnot (E_VarAST noAnnot (VarAST Nothing (T.pack arg)))
                                        [CaseArm (patOfPat pat) body Nothing [] noRange])
                                 _ -> (E_Case noAnnot (E_TupleAST noAnnot (error "kind0") [E_VarAST noAnnot (VarAST Nothing (T.pack arg)) | arg <- args])
                                        [CaseArm (EP_Tuple noRange (map patOfPat pats))
                                            body Nothing [] noRange])
                                  in
                     (args, bod)
        in
            FnAST noAnnot
                 (T.pack nameStr)
                 [] -- TODO this might be wrong...
                 [TypedId (MetaPlaceholder "") (Ident (T.pack arg) 0) | arg <- args']
                 body'
                 isToplevel

      fnOfMatches nameStr [pats] [body] isToplevel =
        fnOfLambda nameStr pats body isToplevel

      fnOfMatches nameStr patss bodies isToplevel =
           let args = ["arg" ++ show n | (_, n) <- zip (head patss) [0..]] in
           let bod  = case (args, head patss) of
                       ([arg], [pat]) ->
                            (E_Case noAnnot (E_VarAST noAnnot (VarAST Nothing (T.pack arg)))
                              [CaseArm (patOfPat pat)
                                  body Nothing [] noRange | (pats, body) <- zip patss bodies])
                       _ -> (E_Case noAnnot (E_TupleAST noAnnot (error "kind0") [E_VarAST noAnnot (VarAST Nothing (T.pack arg)) | arg <- args])
                              [CaseArm (EP_Tuple noRange (map patOfPat pats))
                                  body Nothing [] noRange | (pats, body) <- zip patss bodies])
                        in
            FnAST noAnnot
                 (T.pack nameStr)
                 [] -- TODO this might be wrong...
                 [TypedId (MetaPlaceholder "") (Ident (T.pack arg) 0) | arg <- args]
                 bod
                 isToplevel
{-
      typOfTyp ty =
        case ty of
          H.TyF
  -}
      parseMatches (H.Match name pats rhs _mb_binds : rest) = go name [pats] [rhs] rest
        where
          go name patss rhss [] = (name, reverse patss, reverse rhss)
          go name patss rhss (H.Match name' pats' rhs' _ :  rest) = go name (pats' : patss) (rhs' : rhss) rest
          go name _ _ _ = error "parseMatches.InfixMatch"

      dumpFnLoneMatch match = do
        case match of
          H.Match name pats rhs mb_binds -> do
            let fn = fnOfLambda (prettyPrint name) pats (expOfRhs rhs) True
            appendFile fosterpath (show $ plain $ prettyTopLevelFn fn)
            appendFile fosterpath "\n\n"

          H.InfixMatch {} ->
            appendFile fosterpath ("/* TODO(InfixMatch):\n" ++ prettyPrint match ++ "*/\n")

      dumpFnMatches matches = do
        let (name, patss, rhss) = parseMatches matches
        let fn = fnOfMatches (prettyPrint name) patss (map expOfRhs rhss) True
        appendFile fosterpath (show $ plain $ prettyTopLevelFn fn)
        appendFile fosterpath "\n\n"

      parseDeclHead dh = go dh []
        where go dh tyvars =
                case dh of
                    H.DHead name -> (name, reverse tyvars)
                    H.DHParen dh -> go dh tyvars
                    H.DHApp dh tvb -> go dh (tvb:tyvars)
                    H.DHInfix tvb name -> (name, reverse (tvb:tyvars))

      dumpDecl d = do
        case d of
          H.TypeDecl dh ty ->
            appendFile fosterpath ("/* TODO(dumpDecl.TypeDecl):\n" ++ prettyPrint d ++ "*/\n")
          H.DataDecl H.DataType Nothing dh qcdecls mb_der -> do
            let (name, tvbs) = parseDeclHead dh
            appendFile fosterpath $ "type case " ++ prettyPrint name ++ {- tyvars -} "\n"
            forM_ qcdecls $ \(H.QualConDecl mb_tvbs mb_ctx condecl) -> do
               case condecl of
                 H.ConDecl nm tys -> do
                   appendFile fosterpath ("  of $" ++ prettyPrint nm)
                   forM_ tys $ \ty -> appendFile fosterpath (" " ++ prettyPrint ty)

                 H.RecDecl nm fields -> do
                   appendFile fosterpath ("  of $" ++ prettyPrint nm)
                   forM_ fields $ \(H.FieldDecl names ty) -> do
                     forM_ names $ \name ->
                       appendFile fosterpath (" /* " ++ prettyPrint name ++ " */ " ++ prettyPrint ty)
                   -- TODO generate accessors
                   appendFile fosterpath "\n/* TODO: generate record accessor functions */\n"
               appendFile fosterpath "\n"
            appendFile fosterpath ";\n"
            case mb_der of
              Nothing -> return ()
              Just der -> appendFile fosterpath ("/* " ++ prettyPrint der ++ "*/\n")

          H.DataDecl dor mb_ctx dh qcdecls mb_der ->
            appendFile fosterpath ("/* TODO(dumpDecl.DataDecl):\n" ++ prettyPrint d ++ "*/\n")
          H.TypeSig names ty ->
            forM_ names $ \name -> appendFile fosterpath (prettyPrint name ++ " :: " ++ prettyPrint ty ++ "\n")

          H.FunBind [match] ->
            dumpFnLoneMatch match

          H.FunBind matches ->
            dumpFnMatches matches

          H.PatBind pat rhs binds ->
            appendFile fosterpath ("/* TODO(dumpDecl.PatBind):\n" ++ prettyPrint d ++ "*/\n")

          _ -> do
            appendFile fosterpath ("/* TODO(dumpDecl):\n" ++ prettyPrint d ++ "*/\n")

  case res of
    ParseOk m -> do
      case m of
        H.Module _mb_modulehead _pragmas imports decls -> do
          forM_ imports $ \(H.ImportDecl im qualB srcB safeB mb_pkg mb_as mb_specs) -> do
            appendFile fosterpath ("// " ++ show im ++ "\n")

          mapM_ dumpDecl decls

        _ -> error $ "Tried to parse Module but couldn't..."

    ParseFailed _ msg ->
      error $ "Parsing input Haskell program failed; msg was " ++ msg
