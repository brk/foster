-----------------------------------------------------------------------------
-- Copyright (c) 2014 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.PrettyAnnExpr where

import Prelude hiding ((<$>))

import Foster.Base
import Foster.AnnExpr
import Foster.TypeTC

import Prettyprinter
import Prettyprinter.Render.Terminal

import qualified Data.Text as T
import Data.Char(isAlpha)

-- "The ribbon width is the maximal amount of
--  non-indentation characters on a line."

showTyped :: PrettyT t => Doc AnsiStyle -> t -> Doc AnsiStyle
showTyped d t = parens (d <+> text "::" <+> prettyT t)

showUnTyped d _ = d

comment d = text "/*" <+> d <+> text "*/"

instance PrettyT e => PrettyT (ArrayIndex e) where
  prettyT (ArrayIndex b i _rng SG_Static) = prettyT b <> brackets (prettyT i)
  prettyT (ArrayIndex b i _rng SG_Dynamic) =
    text "prim array-subscript" <+> prettyT b <+> prettyT i
  prettyT (ArrayIndex b i _rng SG_Unsafe) =
    text "prim array-subscript-unsafe" <+> prettyT b <+> prettyT i

-- (<//>) ?vs? align (x <$> y)

kwd  s = dullblue  (text s)
lkwd s = dullwhite (text s)
end    = lkwd "end"

prettyRecord labs exps =
    let
      prettyField (lab, exp) = text lab <> text ":" <+> prettyT exp
      pairs = map prettyField (zip labs exps)
    in
    parens (hsep $ punctuate comma pairs)

{-
instance Pretty TypeP where
  pretty t = case t of
          PrimIntP       isb          -> text "Int" <> pretty isb
          TyConAppP      dt ts        -> text "[TyCon" <+> tupled (map pretty ts) <> text "]"
          TupleTypeP     ts           -> tupled (map pretty ts)
          FnTypeP        ts r p cc pf -> text "{" <+> hsep [pretty t <+> text "=>" | t <- ts]
                                                  <+> pretty r <+> text "}" -- TODO pp precond
          CoroTypeP      s  r         -> text "Coro ..."
          ArrayTypeP     t            -> text "Array" <+> pretty t
          RefTypeP       t            -> text "Ref" <+> pretty t
          ForAllP        tyfs rho     -> text "forall ..." <+> pretty rho
          TyVarP         tv           -> text "tyvar"
          MetaPlaceholder str         -> text ("?? " ++ str)
-}

lineOrSpace = line              -- line, unless undone by group, then space
lineOrEmpty = linebreak
spaceOrLine = group line        -- space if possible, otherwise line
emptyOrLine = group linebreak

-- x <$>  y     =       x <> lineOrSpace <> y --      line
-- x </>  y     =       x <> spaceOrLine <> y -- soft line
-- x <//> y     =       x <> lineOrEmpty <> y -- line break
-- x <$$> y     =       x <> emptyOrLine <> y -- soft break

instance (PrettyT ty, PrettyT expr) => PrettyT (Fn rec expr ty) where
  prettyT fn =
      group (lbrace <> args (fnVars fn)
                    </> nest 4 (group $
                                  linebreak <> prettyT (fnBody fn))
                    <$> rbrace)
    where args []  = emptyDoc
          args frm = emptyDoc <+> hsep (map (\v -> prettyFnFormal v <+> text "=>") frm)

          prettyFnFormal (TypedId _t v) = prettyIdent v

prettyTyFormals [] = emptyDoc
prettyTyFormals tyfs = emptyDoc <+> text "forall" <+> hsep (map prettyTyFormal tyfs) <+> text ","
  where prettyTyFormal (TypeFormal name _sr kind) =
                                          text name <+> text ":" <+> pretty kind

{-
prettyTopLevelFn fn =
 withAnnot (fnAstAnnot fn) $
  text (T.unpack $ fnAstName fn) <+> text "=" <+> pretty fn <> text ";"

instance Pretty (ModuleAST (ExprSkel ExprAnnot) TypeP) where
  pretty m = text "// begin decls"
            <$> vcat [showTyped (text s) t | (s, t) <- moduleASTdecls m]
            <$> text "// end decls"
            <$> text "// begin datatypes"
            <$> empty
            <$> text "// end datatypes"
            <$> text "// begin prim types"
            <$> empty
            <$> text "// end prim types"
            <$> text "// begin functions"
            <$> vsep (map prettyTopLevelFn (moduleASTfunctions m))
            <$> text "// end functions"
-}

--prettyId (TypedId _ i) = text (T.unpack $ identPrefix i)

prettyAtom e =
  case e of
    AnnCall       {} -> prettyT e
    E_AnnFn f        -> prettyT f
    AnnArrayRead  {} -> prettyT e

    E_AnnVar      {} -> prettyT e
    AnnPrimitive  {} -> prettyT e
    AnnLiteral    {} -> prettyT e
    AnnRecord     {} -> prettyT e
    AnnTuple      {} -> prettyT e
    AnnHandler    {} -> prettyT e
    AnnCase       {} -> prettyT e
    AnnIf         {} -> prettyT e
    AnnLetVar     {} -> prettyT e
    AnnLetFuns    {} -> prettyT e
    AnnLetRec     {} -> prettyT e
    AnnAppCtor    {} -> prettyT e
    AnnAlloc      {} -> prettyT e
    AnnDeref      {} -> prettyT e
    AnnStore      {} -> prettyT e
    AnnAllocArray {} -> prettyT e
    AnnArrayPoke  {} -> prettyT e
    AnnArrayLit   {} -> prettyT e
    E_AnnTyApp    {} -> prettyT e
    AnnCompiles   {} -> prettyT e
    AnnKillProcess {} -> prettyT e

isOperator (E_AnnVar _ (tid, _)) = not . isAlpha . T.head . identPrefix $ tidIdent tid
isOperator _                     = False

instance Pretty Formatting where
  pretty BlankLine   = text "/*nl*/"
  -- Egads, is there no way of *forcing* a linebreak with wl-pprint?
  pretty (Comment t) =
    case T.unpack t of
      ('/':'/':s) -> text "/*" <> string s <+> text "*/"
      _ -> text t

withAnnot (ExprAnnot pre _ post) doc =
  hsep $ map pretty pre ++ [doc <> hsep (map pretty post)]

  {-
instance Pretty (ArrayEntry (ExprAST TypeP)) where
  pretty (AE_Int _annot str) = pretty str
  pretty (AE_Expr ex) = pretty ex
-}

prettyBinding :: PrettyT bound => Ident -> bound -> (Doc AnsiStyle -> Doc AnsiStyle) -> Doc AnsiStyle
prettyBinding id bound prefix =
    prefix (pretty id) <+> text "=" <+> prettyT bound <> lkwd ";"

prettySeq :: PrettyT bound => [Ident] -> [bound] -> (Doc AnsiStyle -> Doc AnsiStyle) -> Doc AnsiStyle
prettySeq ids bounds prefix =
    indent 2 $ vcat [prettyBinding id bnd prefix | (id, bnd) <- zip ids bounds]

instance PrettyT (AnnExpr TypeTC) where
  prettyT e =
        case e of
            AnnLiteral annot _ lit  -> withAnnot annot $ prettyT lit
            AnnRecord  annot _ labs es -> withAnnot annot $ prettyRecord labs es
            AnnTuple   annot _ _ es -> withAnnot annot $ parens (hsep $ punctuate comma (map prettyT es))
            E_AnnFn    fn           ->                   prettyT fn
            AnnIf      annot _ c b1 b2 -> withAnnot annot $
                                               kwd "if" <+> prettyT c
                                           <$> nest 2 (kwd "then" <+> prettyT b1)
                                           <$> nest 2 (kwd "else" <+> prettyT b2)
                                           <$> end
            AnnHandler annot _ _fx action arms mb_xform _ -> withAnnot annot $ prettyHandler action arms mb_xform
            AnnCase annot _ scrut arms  -> withAnnot annot $ prettyCase scrut arms
            AnnLetVar annot i bound expr -> withAnnot annot $
                                       prettyBinding i bound id
                                   <$> prettyT expr
            AnnLetFuns annot [id] [fn] expr -> withAnnot annot $
                                       prettySeq [id] [fn] (\d -> d)
                                   <$> prettyT expr
            AnnLetFuns annot ids fns expr -> withAnnot annot $
                                       prettySeq ids fns (\d -> lkwd "REC" <+> d)
                                   <$> prettyT expr
            AnnLetRec  annot ids exprs expr -> withAnnot annot $
                                       prettySeq ids exprs (\d -> lkwd "REC" <+> d)
                                   <$> prettyT expr
            E_AnnVar   annot (tid, _) -> withAnnot annot $ prettyT tid
            AnnPrimitive annot _ prim -> withAnnot annot $ prettyT prim
            AnnCall   annot _ e [] _  -> withAnnot annot $ prettyT e <+> text "!"
            AnnCall   annot _ e [e1,e2] _ | isOperator e
                                      -> withAnnot annot $ prettyT e1 <+> prettyT e <+> prettyT e2
            AnnCall    annot _ e es _ -> withAnnot annot $ prettyT e <+> hsep (map prettyAtom es)
            AnnAppCtor annot _ e es   -> withAnnot annot $ pretty  e <+> hsep (map prettyAtom es)

            AnnAlloc annot _ e _rgn  -> withAnnot annot $ parens $ text "ref" <+> prettyT e
            AnnDeref annot _ e       -> withAnnot annot $ prettyT e <> text "^"
            AnnStore annot _ e1 e2   -> withAnnot annot $ prettyT e1 <+> text ">^" <+> prettyT e2
            AnnAllocArray annot _ _e _ty _ _ -> withAnnot annot $ text "AnnAllocArray"
            AnnArrayLit   annot _ _entries -> withAnnot annot $ text "AnnArrayLit"
            AnnArrayRead  annot _ ai      -> withAnnot annot $ prettyT ai
            AnnArrayPoke  annot _ ai e    -> withAnnot annot $ prettyT e <+> text ">^" <+> prettyT ai
            AnnKillProcess {} -> text "<<<AnnKillProcess>>>"
            AnnCompiles    {} -> text "<<<AnnCompiles>>>"
            E_AnnTyApp annot t e ts -> withAnnot annot $ showTyped (prettyT e <> text ":" <> prettyT ts) t
{-
            E_ArrayPoke   annot ai e -> withAnnot annot $ pretty e <+> text ">^" <+> pretty ai
            E_MachArrayLit annot args -> withAnnot annot $ text "prim mach-array-literal" <+> hsep (map pretty args)
            E_VarAST annot evar     -> withAnnot annot $ pretty evar
            E_TyApp  annot e argtys -> withAnnot annot $ pretty e <> text ":[" <> hsep (punctuate comma (map pretty argtys)) <> text "]"
            E_TyCheck annot e ty    -> withAnnot annot $ parens (pretty e <+> text "as" <+> pretty ty)
            E_KillProcess annot exp -> withAnnot annot $ text "prim kill-entire-process" <+> pretty exp
            E_StringAST   annot s   -> withAnnot annot $ dquotes (text $ T.unpack s)
            E_BoolAST     annot b   -> withAnnot annot $ text $ show b
            E_PrimAST     annot nm  -> withAnnot annot $ text nm
            E_CallAST annot e []      _ -> withAnnot annot $ pretty e <+> text "!"
            E_CallAST annot e [e1,e2] _ | isOperator e
                                        -> withAnnot annot $ pretty e1 <+> pretty e <+> pretty e2
            E_CallAST annot e es      _ -> withAnnot annot $ pretty e <+> hsep (map prettyAtom es)
            E_LetAST  annot (TermBinding evar bound) expr ->
                                       withAnnot annot $
                                      lkwd "let"
                                      <+> (pretty evar)
                                      <+> text "="
                                      <+> pretty bound <+> lkwd "in"
                                   <$> pretty expr
            E_LetRec annot binds e -> withAnnot annot $
                                       text "rec"
                                   <$> indent 2 (vcat [pretty evar <+> text "="
                                                                   <+> pretty expr
                                                      | TermBinding evar expr <- binds
                                                      ])
                                   <$> lkwd "in"
                                   <$> pretty e
                                   <$> end
            E_IfAST annot c b1 b2 -> withAnnot annot $
                                       kwd "if" <+> pretty c
                                   <$> nest 2 (kwd "then" <+> pretty b1)
                                   <$> nest 2 (kwd "else" <+> pretty b2)
                                   <$> end
            E_IntAST   annot intstr  -> withAnnot annot $ red     $ text intstr
            E_RatAST   annot fltstr  -> withAnnot annot $ dullred $ text fltstr

            E_Case annot scrut arms  -> withAnnot annot $ prettyCase scrut arms
            E_CompilesAST annot Nothing  -> withAnnot annot $ text $ "E_CompilesAST NOTHING"
            E_CompilesAST annot (Just e) -> withAnnot annot $ parens $ text "prim __COMPILES__" <+> pretty e
            E_ArrayRead   annot ai   -> withAnnot annot $ pretty ai
            E_ArrayPoke   annot ai e -> withAnnot annot $ pretty e <+> text ">^" <+> pretty ai
            E_TupleAST    annot es   -> withAnnot annot $ parens (hsep $ punctuate comma (map pretty es))
            E_SeqAST annot _  _  -> let exprs = childrenOf e in
                                    let seqcat l r = pretty l <> text ";"
                                                 <$> pretty r in
                                    withAnnot annot $
                                        group $ foldl1 seqcat (map pretty exprs)
            E_FnAST annot fn     -> withAnnot annot $ pretty fn
-}
