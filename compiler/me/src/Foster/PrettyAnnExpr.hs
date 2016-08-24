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

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T
import Data.Char(isAlpha)

-- "The ribbon width is the maximal amount of
--  non-indentation characters on a line."

showTyped :: Pretty t => Doc -> t -> Doc
showTyped d t = parens (d <+> text "::" <+> pretty t)

showUnTyped d _ = d

comment d = text "/*" <+> d <+> text "*/"

instance Pretty e => Pretty (ArrayIndex e) where
  pretty (ArrayIndex b i _rng SG_Static) = pretty b <> brackets (pretty i)
  pretty (ArrayIndex b i _rng SG_Dynamic) =
    text "prim array-subscript" <+> pretty b <+> pretty i
  pretty (ArrayIndex b i _rng SG_Unsafe) =
    text "prim array-subscript-unsafe" <+> pretty b <+> pretty i

-- (<//>) ?vs? align (x <$> y)

kwd  s = dullblue  (text s)
lkwd s = dullwhite (text s)
end    = lkwd "end"

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

instance (Pretty ty, Pretty expr) => Pretty (Fn rec expr ty) where
  pretty fn =
      group (lbrace <> args (fnVars fn)
                    </> nest 4 (group $
                                  linebreak <> pretty (fnBody fn))
                    <$> rbrace)
    where args []  = empty
          args frm = empty <+> hsep (map (\v -> prettyFnFormal v <+> text "=>") frm)

          prettyFnFormal (TypedId _t v) = text (T.unpack $ identPrefix v)

prettyTyFormals [] = empty
prettyTyFormals tyfs = empty <+> text "forall" <+> hsep (map prettyTyFormal tyfs) <+> text ","
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

prettyId (TypedId _ i) = text (T.unpack $ identPrefix i)

prettyAtom e =
  case e of
    AnnCall       {} -> pretty e
    E_AnnFn f        -> pretty f
    AnnArrayRead  {} -> pretty e

    E_AnnVar      {} -> pretty e
    AnnPrimitive  {} -> pretty e
    AnnLiteral    {} -> pretty e
    AnnTuple      {} -> pretty e
    AnnCase       {} -> pretty e
    AnnIf         {} -> pretty e
    AnnLetVar     {} -> pretty e
    AnnLetFuns    {} -> pretty e
    AnnLetRec     {} -> pretty e
    AnnAppCtor    {} -> pretty e
    AnnAlloc      {} -> pretty e
    AnnDeref      {} -> pretty e
    AnnStore      {} -> pretty e
    AnnAllocArray {} -> pretty e
    AnnArrayPoke  {} -> pretty e
    AnnArrayLit   {} -> pretty e
    E_AnnTyApp    {} -> pretty e
    AnnCompiles   {} -> pretty e
    AnnKillProcess {} -> pretty e

isOperator (E_AnnVar _ (tid, _)) = not . isAlpha . T.head . identPrefix $ tidIdent tid
isOperator _                     = False

instance Pretty Formatting where
  pretty BlankLine   = text "/*nl*/"
  -- Egads, is there no way of *forcing* a linebreak with wl-pprint?
  pretty (Comment ('/':'/':s)) = text "/*" <> text s <+> text "*/"
  pretty (Comment s) = string s

withAnnot (ExprAnnot pre _ post) doc =
  hsep $ map pretty pre ++ [doc <> hsep (map pretty post)]

  {-
instance Pretty (ArrayEntry (ExprAST TypeP)) where
  pretty (AE_Int _annot str) = pretty str
  pretty (AE_Expr ex) = pretty ex
-}

prettyBinding :: Pretty bound => Ident -> bound -> (Doc -> Doc) -> Doc
prettyBinding id bound prefix =
    prefix (pretty id) <+> text "=" <+> pretty bound <> lkwd ";"

prettySeq :: Pretty bound => [Ident] -> [bound] -> (Doc -> Doc) -> Doc
prettySeq ids bounds prefix =
    indent 2 $ vcat [prettyBinding id bnd prefix | (id, bnd) <- zip ids bounds]

instance Pretty (AnnExpr TypeTC) where
  pretty e =
        case e of
            AnnLiteral annot _ lit  -> withAnnot annot $ pretty lit
            AnnTuple   annot _ _ es -> withAnnot annot $ parens (hsep $ punctuate comma (map pretty es))
            E_AnnFn    fn           ->                   pretty fn
            AnnIf      annot _ c b1 b2 -> withAnnot annot $
                                               kwd "if" <+> pretty c
                                           <$> nest 2 (kwd "then" <+> pretty b1)
                                           <$> nest 2 (kwd "else" <+> pretty b2)
                                           <$> end
            AnnCase annot _ scrut arms  -> withAnnot annot $ prettyCase scrut arms
            AnnLetVar annot i bound expr -> withAnnot annot $
                                       prettyBinding i bound id
                                   <$> pretty expr
            AnnLetFuns annot [id] [fn] expr -> withAnnot annot $
                                       prettySeq [id] [fn] (\d -> d)
                                   <$> pretty expr
            AnnLetFuns annot ids fns expr -> withAnnot annot $
                                       prettySeq ids fns (\d -> lkwd "REC" <+> d)
                                   <$> pretty expr
            AnnLetRec  annot ids exprs expr -> withAnnot annot $
                                       prettySeq ids exprs (\d -> lkwd "REC" <+> d)
                                   <$> pretty expr
            E_AnnVar   annot (tid, _) -> withAnnot annot $ pretty tid
            AnnPrimitive annot _ prim -> withAnnot annot $ pretty prim
            AnnCall   annot _ e []    -> withAnnot annot $ pretty e <+> text "!"
            AnnCall   annot _ e [e1,e2] | isOperator e
                                      -> withAnnot annot $ pretty e1 <+> pretty e <+> pretty e2
            AnnCall    annot _ e es   -> withAnnot annot $ pretty e <+> hsep (map prettyAtom es)
            AnnAppCtor annot _ e es   -> withAnnot annot $ pretty e <+> hsep (map prettyAtom es)

            AnnAlloc annot _ e _rgn  -> withAnnot annot $ parens $ text "ref" <+> pretty e
            AnnDeref annot _ e       -> withAnnot annot $ pretty e <> text "^"
            AnnStore annot _ e1 e2   -> withAnnot annot $ pretty e1 <+> text ">^" <+> pretty e2
            AnnAllocArray annot _ _e _ty _ _ -> withAnnot annot $ text "AnnAllocArray"
            AnnArrayLit   annot _ _entries -> withAnnot annot $ text "AnnArrayLit"
            AnnArrayRead  annot _ ai      -> withAnnot annot $ pretty ai
            AnnArrayPoke  annot _ ai e    -> withAnnot annot $ pretty e <+> text ">^" <+> pretty ai
            AnnKillProcess {} -> text "<<<AnnKillProcess>>>"
            AnnCompiles    {} -> text "<<<AnnCompiles>>>"
            E_AnnTyApp annot t e ts -> withAnnot annot $ showTyped (pretty e <> text ":" <> pretty ts) t
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
            E_CallAST annot e []    -> withAnnot annot $ pretty e <+> text "!"
            E_CallAST annot e [e1,e2] | isOperator e
                                    -> withAnnot annot $ pretty e1 <+> pretty e <+> pretty e2
            E_CallAST annot e es    -> withAnnot annot $ pretty e <+> hsep (map prettyAtom es)
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
            E_CompilesAST annot (Just e) -> withAnnot annot $ parens $ text "__COMPILES__" <+> pretty e
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
