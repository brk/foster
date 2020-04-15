module Foster.FromHaskell (convertHaskellToFoster) where

--import Language.Haskell.Exts.SrcLoc
import Language.Haskell.Exts.Simple.Parser
import Language.Haskell.Exts.Simple.Pretty (prettyPrint)
import qualified Language.Haskell.Exts.Simple.Syntax as H
import Language.Haskell.Exts.Simple(parseFile)

import qualified Data.Text as T
import Control.Monad.State(forM_)

import Text.PrettyPrint.ANSI.Leijen((<+>), (<>), (<$>), pretty, text, line,
                                     hsep, fill, parens, vcat, list, red,
                                     plain)

import Foster.Base
import Foster.ExprAST
import Foster.ParsedType
import Foster.PrettyExprAST(prettyTopLevelFn)
import Foster.SourceRange(SourceRange(MissingSourceRange))

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
        H.Qual modname name -> mkVarE $ prettyPrint modname ++ "_" ++ rename name
        H.UnQual name -> mkVarE $ rename name

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
        H.Var qname -> E_CallAST noAnnot (expOfQName qname) (map expOfExp es) CA_None
        H.Con (H.Special (H.TupleCon _boxed _n)) -> E_TupleAST noAnnot (error "kind2") (map expOfExp es)
        H.Con (H.Special H.Cons)     -> E_CallAST noAnnot (mkVarE "Cons") (map expOfExp es) CA_None

        _ -> E_CallAST noAnnot (expOfExp e) (map expOfExp es) CA_None

      mkLetS [] e = e
      mkLetS (s:stmts) e =
        case s of
          H.Generator (H.PVar v) exp ->
               mkLetS stmts (E_LetAST noAnnot (TermBinding (mkVar $ rename v) (expOfExp exp)) e)
          H.Generator pat exp ->
               mkLetS stmts (E_LetAST noAnnot (TermBinding (mkVar $ prettyPrint pat) (expOfExp exp)) e)
          H.LetStmt (H.BDecls decls) ->
               mkLet  decls (mkLetS stmts e)
          H.Qualifier exp ->
               E_SeqAST noAnnot (expOfExp exp) (mkLetS stmts e)
          _ -> mkLetS stmts (E_LetAST noAnnot (TermBinding (mkVar $ prettyPrint s) (mkVarE "()")) e)


      mkLet [] e = e
      mkLet (d:decls) e =
        case d of
          H.PatBind (H.PVar v) rhs _mb_binds ->
               mkLet decls (E_LetAST noAnnot (TermBinding (mkVar $ rename v) (expOfRhs rhs)) e)
          H.PatBind pat rhs _mb_binds ->
               mkLet decls (E_LetAST noAnnot (TermBinding (mkVar $ prettyPrint pat) (expOfRhs rhs)) e)
          _ -> mkLet decls (E_LetAST noAnnot (TermBinding (mkVar $ prettyPrint d) (mkVarE "()")) e)

      expOfExp :: H.Exp -> ExprAST TypeP
      expOfExp exp = case exp of
        H.Var qname -> expOfQName qname
        H.Con qname -> expOfQName qname
        H.Lit (H.Int i)     -> E_IntAST noAnnot (show i)
        H.Lit (H.PrimInt i) -> E_IntAST noAnnot (show i)
        H.Lit (H.String s)  -> E_StringAST noAnnot (SS_Text NotRaw $ T.pack s)

        H.App e1 e2 -> app e1 [e2]

        H.Tuple _boxed exps -> E_TupleAST noAnnot (error "kind1") (map expOfExp exps)
        H.If c t e -> E_IfAST noAnnot (expOfExp c) (expOfExp t) (expOfExp e)

        H.List exps ->
          foldr (\e _l -> E_CallAST noAnnot (mkVarE "Cons") [expOfExp e] CA_None) (mkVarE "Nil") exps 
          --E_MachArrayLit noAnnot Nothing [AE_Expr (expOfExp e) | e <- exps]

        H.Paren e -> expOfExp e
        H.Lambda pats body -> E_FnAST noAnnot $ fnOfLambda "" pats (expOfExp body) [] False
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
        H.Do stmts ->
            case (init stmts, last stmts) of
                (decls, H.Qualifier e) -> mkLetS decls (expOfExp e)
                _ -> error $ "do-stmt did not end with an expression: " ++ prettyPrint exp

        H.LeftSection e qop ->
           E_FnAST noAnnot $ FnAST noAnnot (T.pack "") []
            [TypedId (MetaPlaceholder "") (Ident (T.pack "__sarg") 0)]
            (expOfExp $ H.InfixApp e qop (H.Var (H.UnQual (H.Ident "__sarg"))))
            False

        H.EnumFrom {} -> mkVarE $ "/* " ++ prettyPrint exp ++ " */"
        H.ListComp {} -> mkVarE $ "/* " ++ prettyPrint exp ++ " */"

        H.RecConstr {} -> mkVarE $ "/* " ++ prettyPrint exp ++ " */"
        H.RecUpdate {} -> mkVarE $ "/* " ++ prettyPrint exp ++ " */"

        _ -> error $ "expOfExp: " ++ prettyPrint exp

      caseArmOfAlt alt =
        case alt of
          H.Alt pat (H.UnGuardedRhs exp) _mb_binds -> CaseArm (patOfPat pat) (expOfExp exp) Nothing [] noRange
          H.Alt _pat (H.GuardedRhss _rhss) _mb_binds -> error $ "caseArmOfAlt.guarded"

      expOfRhs rhs = case rhs of
        H.UnGuardedRhs exp -> expOfExp exp
        H.GuardedRhss _grhss -> error $ "expOfRhs.Guarded"

      expAndGuardsOfRhs rhs = case rhs of
        H.UnGuardedRhs exp -> (expOfExp exp, [])
        H.GuardedRhss [H.GuardedRhs guards exp] -> (expOfExp exp, guards)
        H.GuardedRhss _grhss -> error $ "expOfRhs.Guarded (multi)"

      patOfPat p =
        case p of
          H.PVar nm   -> EP_Variable noRange (mkVar $ prettyPrint nm)
          H.PWildCard -> EP_Wildcard noRange
          H.PParen p  -> patOfPat p
          H.PTuple _boxed pats -> EP_Tuple noRange (map patOfPat pats)
          H.PLit _sign (H.Int i)     -> EP_Int noRange (show i)
          H.PLit _sign (H.PrimInt i) -> EP_Int noRange (show i)
          H.PIrrPat p  -> patOfPat p
          H.PBangPat p -> patOfPat p
          H.PInfixApp p1 qname p2 -> patOfPat (H.PApp qname [p1, p2])
          H.PApp qname pats ->
            EP_Ctor noRange (map patOfPat pats) (T.pack $ prettyPrint qname)

          H.PList pats -> foldr (\p ep -> EP_Ctor noRange [patOfPat p, ep] (T.pack "Cons"))
                                (EP_Ctor noRange [] (T.pack "Nil")) pats

          H.PAsPat _name _pat -> error $ "patOfPat.AsPat: " ++ prettyPrint p
          H.PatTypeSig {} -> error $ "patOfPat.PatTypeSig: " ++ prettyPrint p
          H.PRPat {} -> error $ "patOfPat.PRPat: " ++ prettyPrint p
          H.PViewPat {} -> error $ "patOfPat.PViewPat: " ++ prettyPrint p
          H.PList {} -> error $ "patOfPat.PList: " ++ prettyPrint p
          H.PRec {} -> error $ "patOfPat.PRec: " ++ prettyPrint p
          H.PInfixApp {} -> error $ "patOfPat.PInfixApp: " ++ prettyPrint p
          _ -> error $ "patOfPat: " ++ prettyPrint p

      fnOfLambda nameStr pats body guards isToplevel =
        let (args', body') =
              if all isVar pats
                then let args = [prettyPrint name | H.PVar name <- pats] in
                     (args, body)
                     -- { patVars => body }
                     -- { genArgs => case genArgs of pats -> body end }
                else let args = ["arg" ++ show n | (_, n) <- zip pats [0..]]
                         guard = mkGuard guards
                         bod  = case (args, pats) of
                                 ([arg], [pat]) ->
                                      (E_Case noAnnot (mkVarE arg)
                                        [CaseArm (patOfPat pat) body guard [] noRange])
                                 _ -> (E_Case noAnnot (E_TupleAST noAnnot (error "kind0") (map mkVarE args))
                                        [CaseArm (EP_Tuple noRange (map patOfPat pats))
                                            body guard [] noRange])
                                  in
                     (args, bod)
        in
            FnAST noAnnot
                 (T.pack nameStr)
                 [] -- TODO this might be wrong...
                 [TypedId (MetaPlaceholder "") (Ident (T.pack arg) 0) | arg <- args']
                 body'
                 isToplevel

      mkVar  str = VarAST Nothing (T.pack str)
      mkVarE str = E_VarAST noAnnot (mkVar str)

      mkGuard :: [H.Stmt] -> Maybe (ExprAST TypeP)
      mkGuard guards =
        case guards of
           [] -> Nothing
           [H.Qualifier exp] -> Just $ expOfExp exp
           _  -> Just $ mkVarE $ "/* " ++ show guards ++ " */"

      fnOfMatches nameStr [pats] [(body, guards)] isToplevel =
        fnOfLambda nameStr pats body guards isToplevel

      fnOfMatches nameStr patss bodiesAndGuards isToplevel =
           let args = ["arg" ++ show n | (_, n) <- zip (head patss) [0..]]
               bod  = case (args, head patss) of
                       ([arg], [_pat]) ->
                            (E_Case noAnnot (mkVarE arg)
                              [CaseArm (patOfPat pat)
                                  body (mkGuard guards) [] noRange | ([pat], (body, guards)) <- zip patss bodiesAndGuards])
                       _ -> (E_Case noAnnot (E_TupleAST noAnnot (error "kind0") (map mkVarE args))
                              [CaseArm (EP_Tuple noRange (map patOfPat pats))
                                  body (mkGuard guards) [] noRange | (pats, (body, guards)) <- zip patss bodiesAndGuards])
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
          go name patss rhss (H.Match _name' pats' rhs' _ :  rest) =
                      go name (pats' : patss) (rhs' : rhss) rest
          go _name _ _ _ = error "parseMatches.InfixMatch"

      dumpFnLoneMatch match = do
        case match of
          H.Match name pats rhs _mb_binds -> do
            let fn = fnOfLambda (prettyPrint name) pats (expOfRhs rhs) [] True
            appendFile fosterpath (show $ plain $ prettyTopLevelFn fn)
            appendFile fosterpath "\n\n"

          H.InfixMatch {} ->
            appendFile fosterpath ("/* TODO(InfixMatch):\n" ++ prettyPrint match ++ "*/\n")

      dumpFnMatches matches = do
        let (name, patss, rhss) = parseMatches matches
        let fn = fnOfMatches (prettyPrint name) patss (map expAndGuardsOfRhs rhss) True

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
          H.TypeDecl _dh _ty ->
            appendFile fosterpath ("/* TODO(dumpDecl.TypeDecl):\n" ++ prettyPrint d ++ "\n*/\n\n")
          H.DataDecl H.DataType Nothing dh qcdecls ders -> do
            let (name, _tvbs) = parseDeclHead dh
            appendFile fosterpath $ "type case " ++ prettyPrint name ++ {- tyvars -} "\n"
            forM_ qcdecls $ \(H.QualConDecl _mb_tvbs _mb_ctx condecl) -> do
               case condecl of
                 H.ConDecl nm tys -> do
                   appendFile fosterpath ("  of $" ++ prettyPrint nm)
                   forM_ tys $ \ty -> appendFile fosterpath (" " ++ prettyPrint ty)

                 H.RecDecl nm fields -> do
                   appendFile fosterpath ("  of $" ++ prettyPrint nm  ++ "\n")
                   forM_ fields $ \(H.FieldDecl names ty) -> do
                     forM_ names $ \name ->
                       appendFile fosterpath ("      /* " ++ prettyPrint name ++ " */ " ++ prettyPrint ty ++ "\n")
                   -- TODO generate accessors
                   appendFile fosterpath "\n/* TODO: generate record accessor functions */\n"
               appendFile fosterpath "\n"
            appendFile fosterpath ";\n"
            case ders of
              [] -> return ()
              _  -> appendFile fosterpath ("/* # derivings: " ++ show (length ders) ++ "*/\n")

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
          forM_ imports $ \(H.ImportDecl (H.ModuleName modname) qualB srcB safeB mb_pkg mb_as mb_specs) -> do
            appendFile fosterpath ("// snafuinclude " ++ show modname ++ ";\n")

          mapM_ dumpDecl decls

        _ -> error $ "Tried to parse Module but couldn't..."

    ParseFailed _ msg ->
      error $ "Parsing input Haskell program failed; msg was " ++ msg
