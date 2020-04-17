-----------------------------------------------------------------------------
-- Copyright (c) 2010 Ben Karel. All rights reserved.
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
-----------------------------------------------------------------------------

module Foster.PrettyExprAST where

import Prelude hiding ((<$>))

import Foster.Base
import Foster.Kind(kindAsHash)
import Foster.ExprAST
import Foster.ParsedType

import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Text as T
import Data.Char(isAlpha, isPrint, ord, chr, isAscii)
import Data.List(isPrefixOf)
import Numeric(showHex)
import Data.Word(Word8)
import qualified Data.ByteString as BS(unpack)

-- "The ribbon width is the maximal amount of
--  non-indentation characters on a line."

showTyped :: Pretty t => Doc -> t -> Doc
showTyped d t = parens (d <+> text "::" <+> pretty t)

showUnTyped d _ = d

comment d = text "/*" <+> d <+> text "*/"

instance (Pretty ty, IsQuietPlaceholder ty) => Pretty (ArrayIndex (ExprSkel ExprAnnot ty)) where
  pretty (ArrayIndex b i _rng SG_Dynamic) =
    prettyAtom b <> brackets (pretty i)
  pretty (ArrayIndex b i _rng SG_Static) =
    text "prim array-subscript" <+> pretty b <+> pretty i
  pretty (ArrayIndex b i _rng SG_Unsafe) =
    text "prim array-subscript-unsafe" <+> pretty b <+> pretty i

-- (<//>) ?vs? align (x <$> y)

kwd  s = dullblue  (text s)
lkwd s = dullwhite (text s)
end    = lkwd "end"

prettyFx Nothing = empty
prettyFx (Just fx) = pretty fx <> text " "

instance Pretty TypeP where
  pretty t = case t of
          TyConP nam          -> text nam
          TyAppP con []       ->          pretty con
          TyAppP con ts       -> parens $ pretty con <+> sep (map pretty ts)
          RecordTypeP labels ts          -> tupled (map pretty ts) <> text (show labels)
          TupleTypeP  k   ts             -> tupled (map pretty ts) <> text (kindAsHash k)
          FnTypeP    ts r fx _cc _pf _sr ->
                                         text "{" <+> hsep [pretty t <+> text "=>" | t <- ts]
                                                  <+> pretty r <+> prettyFx fx <> text "}"
          ForAllP        _tyfs rho    -> text "forall ..." <+> pretty rho
          TyVarP         tv           -> pretty tv
          MetaPlaceholder str         -> string ("?? " ++ str)
          RefinedTypeP nm ty e -> text "%" <+> text nm <+> text ":" <+> pretty ty <+> text ":" <+> pretty e

class IsQuietPlaceholder ty where
  isQuietPlaceholder :: ty -> Bool

instance IsQuietPlaceholder TypeP where
  isQuietPlaceholder t =
    case t of
      MetaPlaceholder ""   -> True
      MetaPlaceholder name -> ".inferred" `isPrefixOf` name
      _ -> False

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

instance (Pretty ty, IsQuietPlaceholder ty) => Pretty (FnAST ty) where
  pretty fn =
      group (lbrace <> prettyTyFormals (fnTyFormals fn) <> args (fnFormals fn)
                    <> nest 4 (group $ line <> pretty (fnAstBody fn))
                    <$> rbrace)
    where args []  = empty
          args frm = hang 1 (empty <+> vsep (map (\v -> prettyFnFormalTy v <+> text "=>") frm))
          --args frm = group $ align $ vsep (map arg frm)
          --arg v = prettyFnFormalTy v <+> text "=>"

          prettyFnFormal (TypedId _t v) = text (T.unpack $ identPrefix v)
          prettyFnFormalTy tid =
            if isQuietPlaceholder (tidType tid)
             then prettyFnFormal tid
             else prettyFnFormal tid <+> text ":" <+> pretty (tidType tid)

prettyTyFormals [] = empty
prettyTyFormals tyfs = empty <+> text "forall" <+> hsep (map prettyTyFormal tyfs) <+> text ","
  where prettyTyFormal (TypeFormal name _sr kind) =
                                          text name <+> text ":" <+> pretty kind

instance (Pretty ty, IsQuietPlaceholder ty) => Pretty (ModuleExpr ty) where
  pretty m =
        vcat (map prettyImport $ moduleASTincludes m)
    <$> vcat (map prettyItem $ moduleASTitems m)

prettyImport (ident, path) = text "snafuinclude" <+> text (T.unpack ident) <+> text (T.unpack path) <> text ";"

prettyItem (ToplevelDecl (s, t, NotForeign)) = text s <+> text "::" <+> pretty t <> text ";"
prettyItem (ToplevelDecl (s, t, IsForeign nm)) =
  if s == nm
    then text "foreign import" <+> text s <+>                           text "::" <+> pretty t <> text ";"
    else text "foreign import" <+> text s <+> text "as" <+> text nm <+> text "::" <+> pretty t <> text ";"
prettyItem (ToplevelDefn (_, E_FnAST _ fn)) = prettyTopLevelFn fn
prettyItem (ToplevelDefn (s, e)) = text s <+> text "=" <+> pretty e <> text ";"
prettyItem (ToplevelData dt) = pretty dt
prettyItem (ToplevelEffect ed) = pretty ed

prettyId (TypedId _ i) = text (T.unpack $ identPrefix i)

prettyExpr e =
  case e of
    E_SeqAST {} -> parens $ pretty e
    _ -> pretty e

showHex2 c s =
  let rv = showHex c s in
  if length rv == 1 then '0' : rv else rv

-- We restrict our output to printable ASCII values.
-- If we just used isPrint alone, we would take an input string
-- like b"\u{c3}\u{ab}" with an explicit representation of
-- the UTF-8 bytes for ë (U+00EB LATIN SMALL LETTER E WITH DIAERESIS).
-- The compiler parses the escape codes yielding a two-byte (Char)
-- string. The intention is that the bytes should be escaped,
-- but U+00C3 satisfies the Unicode-aware isPrint (Ã), so our
-- pretty printed string would be  b"Ã«" instead of b"\u{c3}\u{ab}".
printableAscii :: Char -> Bool
printableAscii c = isAscii c && isPrint c

formatTextChar :: Bool -> Char -> String
formatTextChar isSingleQuote c =
    case c of
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      '\\' -> "\\\\"
      '\'' -> if isSingleQuote then "\\'" else "'"
      '"'  -> "\\\""
      _ -> if printableAscii c then [c] else "\\u{" ++ showHex2 (ord c) "}"

formatBytesWord8 :: Bool -> Word8 -> String
formatBytesWord8 isSingleQuote w =
  let c = chr $ fromIntegral w in
    case c of
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      '\\' -> "\\\\"
      '\'' -> if isSingleQuote then "\\'" else "'"
      '"'  -> "\\\""
      _ -> if printableAscii c then [c] else "\\x" ++ showHex2 w ""

parens' d = {-nest 1-} (parens d)

prettyCallExprs [] = text "!"
prettyCallExprs es = hang 4 $ sep (map (group.prettyAtom) es)

prettyCallPrim nm []   tys exprs = text "prim" <+> text nm                 <+> prettyCallExprs exprs
prettyCallPrim nm lits tys exprs = text "prim" <+> text nm <+> pretty lits <+> prettyCallExprs exprs

prettyStmt e = case e of
    E_MachArrayLit annot _mbt args -> withAnnot annot $ parens' $ text "prim mach-array-literal" <+> hsep (map pretty args)
    E_VarAST annot evar     -> withAnnot annot $ pretty evar
    E_TyApp  annot e argtys -> withAnnot annot $ pretty e <> text ":[" <> hsep (punctuate comma (map pretty argtys)) <> text "]"
    E_TyCheck annot e ty    -> withAnnot annot $ parens' (pretty e <+> text "as" <+> pretty ty)
    E_KillProcess annot exp -> withAnnot annot $ parens' (text "prim kill-entire-process" <+> pretty exp)
    E_StringAST   annot (SS_Text  r t) -> withAnnot annot $             wasRaw r <> dquotes (text $ concatMap (formatTextChar False) $ T.unpack t)
    E_StringAST   annot (SS_Bytes r b) -> withAnnot annot $ text "b" <> wasRaw r <> dquotes (text $ concatMap (formatBytesWord8 False) $ BS.unpack b)
    E_BoolAST     annot b   -> withAnnot annot $ text $ show b
    
    E_CallPrimAST annot nm lits tys exprs -> withAnnot annot $ prettyCallPrim nm lits tys exprs

    E_CallAST annot e [e1,e2] _ | isOperator e
                            -> withAnnot annot $ hang 4 $ group $
                                                 prettyAtom e1 <$> pretty e <+> group (prettyAtom e2)
    E_CallAST annot e es _TODOcallAnnot
                            -> withAnnot annot $ prettyAtom e <+> prettyCallExprs es
    E_LetAST  annot (TermBinding evar bound) expr ->
                               withAnnot annot $
                              {- lkwd "let"
                              <+> -} {- fill 8 -} (pretty evar)
                              <+> text "="
                              <+> prettyBound bound {- <+> lkwd "in" -}
                                                  <> text ";"
                           <> hardline <> pretty expr
    E_LetRec annot binds e -> withAnnot annot $
                           (vcat [text "REC" <+> pretty evar <+> text "="
                                             <+> pretty expr <> text ";"
                                          | TermBinding evar expr <- binds
                                          ])
                           <$> pretty e
    E_IfAST annot c b1 b2 -> withAnnot annot $
                           nest 2 (kwd "if" <+> pretty c
                                   <$> (kwd "then" <+> align (pretty b1))
                                   <$> (kwd "else" <+> align (pretty b2)))
                           <$> end
    E_IntAST   annot intstr  -> withAnnot annot $ red     $ text intstr
    E_RatAST   annot fltstr  -> withAnnot annot $ dullred $ text fltstr
    E_AllocAST annot e _rgn  -> withAnnot annot $ parens' $ text "prim ref" <+> prettyAtom e
    E_DerefAST annot e       -> withAnnot annot $ prettyAtom e <> text "^"
    E_StoreAST annot e1 e2   -> withAnnot annot $ prettyAtom e1 <+> text ">^" <+> prettyAtom e2
    E_Handler  annot e arms mbe -> withAnnot annot $ prettyHandler e arms mbe
    E_Case annot scrut arms  -> withAnnot annot $ prettyCase scrut arms
    E_CompilesAST annot Nothing  -> withAnnot annot $ text $ "E_CompilesAST NOTHING"
    E_CompilesAST annot (Just e) -> withAnnot annot $ parens' $ text "prim __COMPILES__" <+> prettyAtom e
    E_ArrayRead   annot ai   -> withAnnot annot $ pretty ai
    E_ArrayPoke   annot ai e -> withAnnot annot $ prettyAtom e <+> text ">^" <+> pretty ai
    E_RecordAST   annot labs exps -> withAnnot annot $ prettyRecord labs exps
    E_TupleAST    annot _ es -> withAnnot annot $ parens' (hsep $ punctuate comma (map pretty es))
    E_SeqAST (ExprAnnot pre _ post) l r ->
      if null pre && null post
        then prettyExpr l <> text ";" <$> prettyStmt r
        else prettyExpr l <> text ";" </> (vcat $ map pretty $ pre ++ post)
                                      <$$> prettyStmt r
    E_FnAST annot fn     -> withAnnot annot $ pretty fn

prettyRecord labs exps =
    let
      prettyField (lab, exp) = text (T.unpack lab) <> text ":" <+> pretty exp
      pairs = map prettyField (zip labs exps)
    in
    parens' (hsep $ punctuate comma pairs)

-- Function bodies should not be rendered with alignment,
-- but other let-bound things should.
prettyBound b =
  case b of
    E_FnAST {} -> pretty b
    _ -> align (prettySeq b)

prettySeq :: (Pretty ty, IsQuietPlaceholder ty) => ExprSkel ExprAnnot ty -> Doc
prettySeq e =
  case e of
    E_SeqAST      {} -> parens' $ pretty e
    E_LetAST      {} -> parens' $ pretty e
    _ -> pretty e

prettyAtom :: (Pretty ty, IsQuietPlaceholder ty) => ExprSkel ExprAnnot ty -> Doc
prettyAtom e =
  case e of
    E_SeqAST      {} -> parens' $ pretty e
    E_LetAST      {} -> parens' $ pretty e
    E_CallAST     {} -> parens' $ pretty e
    _ -> pretty e

isOperator (E_VarAST _ evar) = not . isAlpha . T.head $ evarName evar
isOperator _                 = False

instance Pretty Formatting where
  pretty BlankLine   = {-text "~" <>-} linebreak
  pretty (Comment ('/':'/':s)) = text "//" <> text s <> hardline
  pretty (Comment s) = string s -- comment markers already included

annotPre [BlankLine] = []
annotPre pre = map pretty pre
withAnnot (ExprAnnot pre _ post) doc =
      hcat (annotPre pre)
      <>
      doc
      <>
      hcat (map pretty post)

wasRaw NotRaw = empty
wasRaw YesRaw = text "r"

instance (Pretty ty, IsQuietPlaceholder ty) => Pretty (ArrayEntry (ExprAST ty)) where
  pretty (AE_Int _annot str) = pretty str
  pretty (AE_Expr ex) = prettyAtom ex

instance (Pretty ty, IsQuietPlaceholder ty) => Pretty (ExprAST ty) where
  pretty e = prettyStmt e

