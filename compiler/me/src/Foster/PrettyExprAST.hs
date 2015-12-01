-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.PrettyExprAST where

import Foster.Base
import Foster.ExprAST
import Foster.ParsedType

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
  pretty (ArrayIndex b i _rng SG_Dynamic) =
    pretty b <> brackets (pretty i)
  pretty (ArrayIndex b i _rng SG_Static) =
    text "prim array-subscript" <+> pretty b <+> pretty i
  pretty (ArrayIndex b i _rng SG_Unsafe) =
    text "prim array-subscript-unsafe" <+> pretty b <+> pretty i

-- (<//>) ?vs? align (x <$> y)

kwd  s = dullblue  (text s)
lkwd s = dullwhite (text s)
end    = lkwd "end"


instance Pretty TypeP where
  pretty t = case t of
          PrimIntP       isb          -> text "Int" <> pretty isb
          TyConAppP      dt ts        -> parens $ pretty dt <+> sep (map pretty ts)
          TupleTypeP     ts           -> tupled (map pretty ts)
          FnTypeP    ts r _cc _pf _sr -> text "{" <+> hsep [pretty t <+> text "=>" | t <- ts]
                                                  <+> pretty r <+> text "}"
          CoroTypeP      s  r         -> parens $ text "Coro" <+> pretty s <+> pretty r
          ArrayTypeP     t            -> parens $ text "Array" <+> pretty t
          RefTypeP       t            -> parens $ text "Ref" <+> pretty t
          ForAllP        _tyfs rho    -> text "forall ..." <+> pretty rho
          TyVarP         tv           -> pretty tv
          MetaPlaceholder str         -> text ("?? " ++ str)
          RefinedTypeP nm ty e -> text "%" <+> text nm <+> text ":" <+> pretty ty <+> text ":" <+> pretty e

lineOrSpace = line              -- line, unless undone by group, then space
lineOrEmpty = linebreak
spaceOrLine = group line        -- space if possible, otherwise line
emptyOrLine = group linebreak

-- x <$>  y     =       x <> lineOrSpace <> y --      line
-- x </>  y     =       x <> spaceOrLine <> y -- soft line
-- x <//> y     =       x <> lineOrEmpty <> y -- line break
-- x <$$> y     =       x <> emptyOrLine <> y -- soft break

prettyTopLevelFn fn =
 withAnnot (fnAstAnnot fn) $
  text (T.unpack $ fnAstName fn) <+> text "=" <+> pretty fn <> text ";"

instance Pretty ty => Pretty (FnAST ty) where
  pretty fn =
      group (lbrace <> prettyTyFormals (fnTyFormals fn) <> args (fnFormals fn)
                    <+> nest 4 (group $ pretty (fnAstBody fn))
                    <$> rbrace)
    where args []  = empty
          args frm = empty <+> hsep (map (\v -> prettyFnFormal v <+> text "=>") frm)

          prettyFnFormal (TypedId _t v) = text (T.unpack $ identPrefix v)

prettyTyFormals [] = empty
prettyTyFormals tyfs = empty <+> text "forall" <+> hsep (map prettyTyFormal tyfs) <+> text ","
  where prettyTyFormal (TypeFormal name _sr kind) =
                                          text name <+> text ":" <+> pretty kind

instance Pretty ty => Pretty (ModuleAST FnAST ty) where
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

prettyId (TypedId _ i) = text (T.unpack $ identPrefix i)

prettyAtom e =
  case e of
    E_SeqAST      {} -> parens $ pretty e
    E_CallAST     {} -> parens $ pretty e

    E_PrimAST     {} -> pretty e
    E_StringAST   {} -> pretty e
    E_BoolAST     {} -> pretty e
    E_IntAST      {} -> pretty e
    E_RatAST      {} -> pretty e
    E_TupleAST    {} -> pretty e
    E_FnAST       {} -> pretty e
    E_IfAST       {} -> pretty e
    E_Case        {} -> pretty e
    E_LetAST      {} -> pretty e
    E_LetRec      {} -> pretty e
    E_VarAST      {} -> pretty e
    E_AllocAST    {} -> pretty e
    E_DerefAST    {} -> pretty e
    E_StoreAST    {} -> pretty e
    E_ArrayRead   {} -> pretty e
    E_ArrayPoke   {} -> pretty e
    E_TyApp       {} -> pretty e
    E_TyCheck     {} -> pretty e
    E_CompilesAST {} -> pretty e
    E_KillProcess {} -> pretty e
    E_MachArrayLit {} -> pretty e

isOperator (E_VarAST _ evar) = not . isAlpha . T.head $ evarName evar
isOperator _                 = False

instance Pretty Formatting where
  pretty BlankLine   = {-text "~" <>-} linebreak
  -- Egads, is there no way of *forcing* a linebreak with wl-pprint?
  pretty (Comment ('/':'/':s)) = text "/*" <> text s <+> text "*/"
  pretty (Comment s) = string s -- comment markers already included

withAnnot (ExprAnnot pre _ post) doc =
      hcat (map pretty pre)
      <>
      doc
      <>
      hcat (map pretty post)

wasRaw False = empty
wasRaw True  = text "r"

instance Pretty ty => Pretty (ArrayEntry (ExprAST ty)) where
  pretty (AE_Int _annot str) = pretty str
  pretty (AE_Expr ex) = pretty ex

instance Pretty ty => Pretty (ExprAST ty) where
  pretty e =
        case e of
            E_MachArrayLit annot _mbt args -> withAnnot annot $ text "prim mach-array-literal" <+> hsep (map pretty args)
            E_VarAST annot evar     -> withAnnot annot $ pretty evar
            E_TyApp  annot e argtys -> withAnnot annot $ pretty e <> text ":[" <> hsep (punctuate comma (map pretty argtys)) <> text "]"
            E_TyCheck annot e ty    -> withAnnot annot $ parens (pretty e <+> text "as" <+> pretty ty)
            E_KillProcess annot exp -> withAnnot annot $ text "prim kill-entire-process" <+> pretty exp
            E_StringAST   annot r (SS_Text  t) -> withAnnot annot $             wasRaw r <> dquotes (text $ T.unpack t)
            E_StringAST   annot r (SS_Bytes b) -> withAnnot annot $ text "b" <> wasRaw r <> dquotes (text $ show b)
            E_BoolAST     annot b   -> withAnnot annot $ text $ show b
            E_PrimAST     annot nm []   _ -> withAnnot annot $ text nm
            E_PrimAST     annot nm lits _ -> withAnnot annot $ text nm <+> pretty lits
            E_CallAST annot e []    -> withAnnot annot $ pretty e <+> text "!"
            E_CallAST annot e [e1,e2] | isOperator e
                                    -> withAnnot annot $ pretty e1 <+> pretty e <+> pretty e2
            E_CallAST annot e es    -> withAnnot annot $ pretty e <+> align (hsep (map prettyAtom es))
            E_LetAST  annot (TermBinding evar bound) expr ->
                                       withAnnot annot $
                                      lkwd "let"
                                      <+> {- fill 8 -} (pretty evar)
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
            E_AllocAST annot e _rgn  -> withAnnot annot $ parens $ text "ref" <+> pretty e
            E_DerefAST annot e       -> withAnnot annot $ pretty e <> text "^"
            E_StoreAST annot e1 e2   -> withAnnot annot $ pretty e1 <+> text ">^" <+> pretty e2
            E_Case annot scrut arms  -> withAnnot annot $ prettyCase scrut arms
            E_CompilesAST annot Nothing  -> withAnnot annot $ text $ "E_CompilesAST NOTHING"
            E_CompilesAST annot (Just e) -> withAnnot annot $ parens $ text "__COMPILES__" <+> pretty e
            E_ArrayRead   annot ai   -> withAnnot annot $ pretty ai
            E_ArrayPoke   annot ai e -> withAnnot annot $ pretty e <+> text ">^" <+> pretty ai
            E_TupleAST    annot _ es -> withAnnot annot $ parens (hsep $ punctuate comma (map pretty es))
            E_SeqAST (ExprAnnot pre _ post) l r -> pretty l <> text ";" <+> (vcat $ map pretty $ pre ++ post)
                                                <> pretty r
            E_FnAST annot fn     -> withAnnot annot $ pretty fn

