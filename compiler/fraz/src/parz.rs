#![allow(clippy::upper_case_acronyms)]

use codemap::{Span, Spanned, CodeMap};
use std::collections::VecDeque;
use crate::syn;

#[derive(Copy,Clone,Debug)]
pub enum ParseError {
  ParsingFailed,
  InvalidToken
}

fn token_range(s: Span, e: Span) -> Span { s.merge(e) }

// fn token_range(s: &parser::Token, e: &parser::Token) -> Span {
//     return s.extra().merge(e.extra())
// }

fn spanned<T>(n: T, s: Span) -> Spanned<T> {
  Spanned { node: n, span: s }
}

fn vd_singleton<T>(n: T) -> VecDeque<T> {
    let mut vd = VecDeque::new();
    vd.push_back(n);
    vd
}

fn ty_span(t: &syn::Type) -> Span { t.0.span }

fn suffix_span(suff: &syn::Suffix) -> Span {
    *match suff {
        syn::Suffix::Caret(tokspan) => tokspan,
        syn::Suffix::DotSqBrackets(_, span) => span,
        syn::Suffix::RawSqBrackets(_, span) => span,
        syn::Suffix::Bang(tokspan) => tokspan,
    }
}

fn lit_span(lit: &syn::Lit) -> Span {
    *match lit {
        syn::Lit::Num(tokspan) => tokspan,
        syn::Lit::Str(tokspan) => tokspan,
    }
}
fn expr_span(e: &syn::Expr) -> Span { e.0.span }

use pomelo;
pomelo::pomelo! {
    %include { use crate::parz::*; }
    %include { use crate::syn::*; }
    %include { use codemap::{Span, Spanned}; }
    %include { use std::collections::VecDeque; }

    %error ParseError;
    %syntax_error { syntax_error(token, extra) }
    %parse_fail { parse_fail() }
    %stack_overflow { stack_overflow() }

    %parser pub struct Parser<'e>{};
    %extra_argument &'e CodeMap;

    %extra_token codemap::Span;

    %token #[allow(non_camel_case_types)]
           #[derive(Copy,Clone,Debug)]
           pub enum Token {}
           ;

    %type transunit TransUnit;
    transunit ::= import_star(B) item_star(C) FINI { TransUnit(B, C) }
    
    %type import_star Vec<Import>;
    import_star ::=                              { Vec::new() }
    import_star ::= import_star(mut B) import(C) { B.push(C); B }
    
    %type import Import;
    import ::= INCLUDE(O) x(B) STR(C) SEMI(X) { Import { name: B, path: C, span: token_range(O,X) } }
    
    %type item_star Vec<Spanned<Item>>;
    item_star ::=                          { Vec::new() }
    item_star ::= item_star(mut B) item(C) { B.push(C); B }
    
    %type item Spanned<Item>;
    item ::= x(B) DCOLON(D) t(C)      SEMI(X)                                             { spanned(Item::Decl( B, C,    D), token_range(B, X)) }
    item ::= x(B) EQUAL(Q)  phrase(C) SEMI(X)                                             { spanned(Item::Defn( B, C,    Q), token_range(B, X)) }
    item ::= TYPE(O) CASE tyformal(B)  parens_tyformal_star(C)   datactor_star(D) SEMI(X) { spanned(Item::TypeCase( B, C, D), token_range(O, X)) }
    item ::= EFFECT(O)    tyformal(B)  parens_tyformal_star(C) effectctor_star(D) SEMI(X) { spanned(Item::Effect(   B, C, D), token_range(O, X)) }
    item ::= FOREIGN(O) IMPORT x(B) asid?(C) DCOLON t(D) SEMI(X)                          { spanned(Item::ForeignImport( B, C, D), token_range(O, X)) }
    item ::= FOREIGN(O) TYPE  tyformal(B) SEMI(X)                                         { spanned(Item::ForeignType( B), token_range(O, X)) }
    
    %type parens_tyformal_star Vec<Tyformal>;
    parens_tyformal_star ::=                                                { Vec::new() }
    parens_tyformal_star ::= parens_tyformal_star(mut B) parens_tyformal(C) { B.push(C); B }
    
    %type parens_tyformal Tyformal;
    parens_tyformal ::= LPAREN(L) tyformal(B) RPAREN(R) { Tyformal::TyformalParens(L, Box::new(B), R) }
    
    %type datactor_star Vec<DataCtor>;
    datactor_star ::=                                   { Vec::new() }
    datactor_star ::= datactor_star(mut B) datactor(C)  { B.push(C); B }
    
    %type datactor DataCtor;
    datactor ::= OF dctor(B) tatom_star(C) { DataCtor::DataCtor(B, C) }
    
    %type effectctor_star Vec<Spanned<EffectCtor>>;
    effectctor_star ::= effectctor(C)                        { vec![C] }
    effectctor_star ::= effectctor_star(mut B) effectctor(C) { B.push(C); B    }
    
    %type effectctor Spanned<EffectCtor>;
    effectctor ::= OF(O) dctor(B) tatom_star(C)              { let span = token_range(O, C.last().map(ty_span).unwrap_or(B)); spanned(EffectCtor::EffPlain( B, C),    span) }
    effectctor ::= OF(O) dctor(B) tatom_star(C) DARROW t(D)  { let span = token_range(O, ty_span(&D)); spanned(EffectCtor::EffResume(B, C, D), span) }
    
    %type tatom_star Vec<Type>;
    tatom_star ::=                             { Vec::new() }
    tatom_star ::= tatom_star(mut B) tatom(C)  { B.push(C); B }
    
    %type asid Span;
    asid ::= AS id(B) { B }    

    %type dctor Span;
    dctor ::= DOLLAR ctor(B) { B }
    
    %type ctor Span;
    ctor ::= x(B) { B }
    
    %type x Span;
    x ::= id(B) { B }
    
    %type a Span;
    a ::= id(B) { B }
    
    %type pid Span;
    pid ::= id(B) { B }
    
    %type xid Span;
    xid ::= id(B) { B }
    xid ::= OPRNAME(B) { B }
    
    %type id Span;
    id ::= SMALLIDENT(B) { B }
    id ::= UPPERIDENT(B) { B }
    id ::= UNDERIDENT(B) { B }
    
    %type stmts Stmts;
    stmts ::= stmt_start(B) stmt_cont_star(mut C) { C.push_front(B); Stmts::Stmts(C) }
    
    %type stmt_start Stmt;
    stmt_start ::= REC(X) pbinding(B)  { let span = token_range(X, expr_span(&B.1)); Stmt::Rec(vec![B], span) }
    stmt_start ::= ext_pbinding(B)     { B }
    
    %type stmt_cont_star VecDeque<Stmt>;
    stmt_cont_star ::=                                     { VecDeque::new() }
    stmt_cont_star ::= stmt_cont_star(mut B) stmt_cont(C)  { B.extend(C); B }
    
    %type stmt_cont VecDeque<Stmt>;
    stmt_cont ::= SEMI stmt_start_opt(B) { B }
    
    %type stmt_start_opt VecDeque<Stmt>;
    stmt_start_opt ::=               { VecDeque::new() }
    stmt_start_opt ::= stmt_start(B) { vd_singleton(B) }
    
    
    %type ext_pbinding Stmt;
    ext_pbinding ::= e(B)                  { Stmt::Expr(B) }
    ext_pbinding ::= e(B)      EQUAL e(C)  { Stmt::ExprBind(B, C) }
    ext_pbinding ::= patlhs(B) EQUAL e(C)  { Stmt::PatBind(B, C) }
    
    %type pbinding (PatBind, Expr);
    pbinding ::= patbind(B) EQUAL e(C)  { (B, C) }
    
    %type patbind PatBind;
    patbind ::= xid(B)     { PatBind::Ident(B) }
    patbind ::= patlhs(B)  { PatBind::PatLhs(B) }
    
    %type patlhs PatLhs;
    patlhs ::= UNDERSCORE(X)                                      { PatLhs::Wildcard(token_range(X, X)) }
    patlhs ::= LET(O) LPAREN comma_separated_list_p(B) RPAREN(X)  { PatLhs::Tuple(B, token_range(O, X)) }
    
    %type comma_separated_list_p Vec<Pat>;
    comma_separated_list_p ::= p(C)                                      { vec![C] }
    comma_separated_list_p ::= comma_separated_list_p(mut B) COMMA p(C)  { B.push(C); B }
    
    %type e Expr;
    e ::= phrase(C) binops_opt(D)  { let span = D.last().map_or(expr_span(&C), |p| { expr_span(&p.1) }); Expr(spanned(Box::new(Expr_::Chain(C, D)), span)) }
    
    %type binops Vec<(Binop, Expr)>;
    binops ::= binop_phrase_plus(B)  { B }
    
    %type binop Binop;
    binop ::= SYMBOL(B)               { Binop::Symbol(B) }
    binop ::= BACKTICK x(B) BACKTICK  { Binop::Ident( B) }
    
    %type binops_opt Vec<(Binop, Expr)>;
    binops_opt ::=            { Vec::new() }
    binops_opt ::= binops(B)  { B }
    
    %type binop_phrase (Binop, Expr);
    binop_phrase ::= binop(B) phrase(C)  { (B, C) }
    
    %type binop_phrase_plus Vec<(Binop, Expr)>;
    binop_phrase_plus ::= binop_phrase(C)                           { vec![C] }
    binop_phrase_plus ::= binop_phrase_plus(mut B) binop_phrase(C)  { B.push(C); B }
    
    %type phrase Expr;
    phrase ::= lvalue_plus(C)                       { let span = C.last().expect("lvalue_plus nonempty").0.span; Expr(spanned(Box::new(Expr_::Call(C)), span)) }
    phrase ::= PRIM(O) nopr(B) lvalue_star(C)       { let span = token_range(O, C.last().map_or(B, expr_span)); Expr(spanned(Box::new(Expr_::Prim(B, C)), span)) }
    
    %type lvalue_plus Vec<Expr>;
    lvalue_plus ::= lvalue(C)                           { vec![C] }
    lvalue_plus ::= lvalue_plus(mut B) lvalue(C)        { B.push(C); B }
    
    %type lvalue_star Vec<Expr>;
    lvalue_star ::=                                     { Vec::new() }
    lvalue_star ::= lvalue_star(mut B) lvalue(C)        { B.push(C); B }
    
    %type nopr Span;
    nopr ::= x(B)       { B }
    nopr ::= SYMBOL(B)  { B }
    
    %type lvalue Expr;
    lvalue ::= atom(B) suffix_star(C)  { let span = C.last().map_or(expr_span(&B), suffix_span); Expr(spanned(Box::new(Expr_::LValue(B,C)), span)) }
    
    %type suffix Suffix;
    suffix ::= CARET(B)                        { Suffix::Caret(B) }
    suffix ::= DOT_LBRACK(O) e(B) RBRACK(X)    { Suffix::DotSqBrackets(B, token_range(O, X)) }
    suffix ::=     LBRACK(O) e(B) RBRACK(X)    { Suffix::RawSqBrackets(B, token_range(O, X)) }
    suffix ::= BANG(B)                         { Suffix::Bang(B) }
    
    %type suffix_star Vec<Suffix>;
    suffix_star ::=                                { Vec::new() }
    suffix_star ::= suffix_star(mut B) suffix(C)   { B.push(C); B }
    
    %type atom Expr;
    atom ::= x(B)                                   { Expr(spanned(Box::new(Expr_::Var(B)), B)) }
    atom ::= lit(B)                                 { let span = lit_span(&B); Expr(spanned(Box::new(Expr_::Lit(B)), span)) }
    atom ::= ifexpr(B)                              { B }
    atom ::= CASE(O) e(B) of_pmatch_plus(C) END(X)  { Expr(spanned(Box::new(Expr_::Case(B, C)), token_range(O, X))) }
    atom ::= LPAREN(O) RPAREN(X)                    { Expr(spanned(Box::new(Expr_::Unit      ), token_range(O, X))) }
    atom ::= tuple(B)                               { B }
    atom ::= handler(B)                             { B }
    atom ::= valabs(B)                              { B }
    
    %type valabs Expr;
    valabs ::= LCURLY(O) foralls(B) formals(C)          RCURLY(X)  { Expr(spanned(Box::new(Expr_::ValAbs(Some(B), C,  None   )), token_range(O, X))) }
    valabs ::= LCURLY(O) foralls(B) formals(C) stmts(D) RCURLY(X)  { Expr(spanned(Box::new(Expr_::ValAbs(Some(B), C,  Some(D))), token_range(O, X))) }
    valabs ::= LCURLY(O)            formals(C)          RCURLY(X)  { Expr(spanned(Box::new(Expr_::ValAbs(None   , C,  None   )), token_range(O, X))) }
    valabs ::= LCURLY(O)            formals(C) stmts(D) RCURLY(X)  { Expr(spanned(Box::new(Expr_::ValAbs(None   , C,  Some(D))), token_range(O, X))) }
    
    %type formals Vec<Formal>;
    formals ::=                                   { Vec::new() }
    formals ::= formals(mut B) formal(C) DARROW   { B.push(C); B }
    
    %type formal Formal;
    formal ::= pid(B)             { Formal::Formal(B, None) }
    formal ::= pid(B) COLON t(C)  { Formal::Formal(B, Some(C)) }
    
    %type foralls Vec<Tyformal>;
    foralls ::= FORALL tyformal_star(B) COMMA { B };
    
    %type tyformal_star Vec<Tyformal>;
    tyformal_star ::=                                   { Vec::new() }
    tyformal_star ::= tyformal_star(mut B) tyformal(C)  { B.push(C); B }
    
    %type handler Expr;
    handler ::= HANDLE(O) e(B) effmatch_star(C)         END(X)  { Expr(spanned(Box::new(Expr_::Handler(B, C, None   )), token_range(O, X))) }
    handler ::= HANDLE(O) e(B) effmatch_star(C) AS e(D) END(X)  { Expr(spanned(Box::new(Expr_::Handler(B, C, Some(D))), token_range(O, X))) }
    
    %type effmatch_star Vec<EffMatch>;
    effmatch_star ::=                                    { Vec::new() }
    effmatch_star ::= effmatch_star(mut B) effmatch(C)   { B.push(C); B }
    
    %type effmatch EffMatch;
    effmatch ::= OF patside(B) SARROW stmts(C) { EffMatch::EffMatch(B, C) }
    
    %type tuple Expr;
    tuple ::= LPAREN(O) e(B) AS t(C) RPAREN(X)                  { Expr(spanned(Box::new(Expr_::TypeAscription(B, C)), token_range(O, X))) }
    tuple ::= LPAREN(O) e(B) comma_e_star(C) RPAREN(X) HASH?(D) { Expr(spanned(Box::new(Expr_::Tuple(B, C, D      )), token_range(O, X))) }
    
    %type comma_e Expr;
    comma_e ::= COMMA e(B)  { B }
    
    %type comma_e_star Vec<Expr>;
    comma_e_star ::=                                 { Vec::new() }
    comma_e_star ::= comma_e_star(mut B) comma_e(C)  { B.push(C); B }
    
    %type of_pmatch_plus Vec<PatMatch>;
    of_pmatch_plus ::= OF pmatch(C)                       { vec![C] }
    of_pmatch_plus ::= of_pmatch_plus(mut B) OF pmatch(C) { B.push(C); B }
    
    %type pmatch PatMatch;
    pmatch ::= p(B)         SARROW stmts(D) { PatMatch::PatMatch(B, None,    D) }
    pmatch ::= p(B) IF e(C) SARROW stmts(D) { PatMatch::PatMatch(B, Some(C), D) }
    
    %type p Pat;
    p ::= patside(B) orpatside_plus(C)  { Pat::PatOf(B, C)          }
    p ::= patside(B)                    { Pat::PatOf(B, Vec::new()) }
    
    %type orpatside_plus Vec<Patside>;
    orpatside_plus ::= orpatside(C)                       { vec![C] }
    orpatside_plus ::= orpatside_plus(mut B) orpatside(C) { B.push(C); B    }
    
    %type orpatside Patside;
    orpatside ::= OR patside(B) { B }
    
    %type patside Patside;
    patside ::= dctor(B) patom_star(C) { Patside::Dctor(B, C) }
    patside ::= patom(B)               { Patside::Atom(B)   }
    
    %type patom_star Vec<PatAtom>;
    patom_star ::=                             { Vec::new() }
    patom_star ::= patom_star(mut B) patom(C)  { B.push(C); B }
    
    %type patom PatAtom;
    patom ::= x(B)                                  { PatAtom::Ident(B) }
    patom ::= UNDERSCORE(B)                         { PatAtom::Under(B) }
    patom ::= lit(B)                                { PatAtom::Lit(B) }
    patom ::= LPAREN(O) RPAREN(X)                   { PatAtom::Tuple(Vec::new(), token_range(O, X)) }
    patom ::= LPAREN(O) p_sepby_COMMA(B) RPAREN(X)  { PatAtom::Tuple(B,          token_range(O, X)) }
    
    %type p_sepby_COMMA Vec<Pat>;
    p_sepby_COMMA ::= p(B)                             { vec![B] }
    p_sepby_COMMA ::= p_sepby_COMMA(mut B) COMMA p(C)  { B.push(C); B }
    
    %type lit Lit;
    lit ::= NUM(B)  { Lit::Num(B) }
    lit ::= STR(B)  { Lit::Str(B) }
    
    %type ifexpr Expr;
    ifexpr ::= IF(O) stmts(B) THEN stmts(C) ELSE stmts(D) END(X)  { Expr(spanned(Box::new(Expr_::If(B, C, Some(D))), token_range(O, X))) }
    ifexpr ::= IF(O) stmts(B) THEN stmts(C)               END(X)  { Expr(spanned(Box::new(Expr_::If(B, C, None   )), token_range(O, X))) }
    
    %type tyformal Tyformal;
    tyformal ::= x(B)                { Tyformal::Tyformal(B, None) }
    tyformal ::= x(B) COLON kind(C)  { Tyformal::Tyformal(B, Some(C)) }
    
    %type kind Span;
    kind ::= x(B)  { B }
    
    %type t Type;
    t ::= PERCENT(P) x(B) COLON tp(C) COLON e(D)  { let span = token_range(P, expr_span(&D)); Type(spanned(Box::new(Type_::Refined(B, C, D)), span)) }
    t ::= tp(B)  { B }
    
    %type tp Type;
    tp ::= tatom(B) tatom_plus(C)  { let span = token_range(ty_span(&B), ty_span(C.last().unwrap_or(&B))); Type(spanned(Box::new(Type_::App(B, C)), span)) }
    tp ::= tatom(B)                { B }
    
    %type tatom_plus Vec<Type>;
    tatom_plus ::= tatom(C)                    { vec![C] }
    tatom_plus ::= tatom_plus(mut B) tatom(C)  { B.push(C); B }
    
    %type tatom Type;
    tatom ::= a(B)                                           { Type(spanned(Box::new(Type_::Var(B)     ), B)) }
    tatom ::= LPAREN(O) RPAREN(X)                            { Type(spanned(Box::new(Type_::Unit       ), token_range(O, X))) }
    tatom ::= LPAREN(O) t_sepby_COMMA(B) RPAREN(X) HASH?(C)  { Type(spanned(Box::new(Type_::Tuple(B, C)), token_range(O, C.unwrap_or(X)))) }
    tatom ::= LCURLY(O) t_sepby_DARROW(B) RCURLY(X)          { Type(spanned(Box::new(Type_::Fun(B)     ), token_range(O, X))) }
    
    %type t_sepby_DARROW Vec<Type>;
    t_sepby_DARROW ::= t(C)                               { vec![C] }
    t_sepby_DARROW ::= t_sepby_DARROW(mut B) DARROW t(C)  { B.push(C); B }
    
    %type t_sepby_COMMA Vec<Type>;
    t_sepby_COMMA ::= t(C)                             { vec![C] }
    t_sepby_COMMA ::= t_sepby_COMMA(mut B) COMMA t(C)  { B.push(C); B }
    
}

// If it evaluates to Ok(()), the parser will try to recover and continue.
// If it evaluates to Err(_) or a ? fails, the parser will fail with that
// error value.
fn syntax_error(tok: Option<parser::Token>, codemap: &CodeMap) -> Result<(), ParseError> {
    use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter, Level, SpanLabel, SpanStyle};
    match tok {
        Some(t) => {
            let mut emitter = Emitter::stderr(ColorConfig::Always, Some(codemap));
            emitter.emit(&[Diagnostic {
                level: Level::Error,
                message: "unexpected token".into(),
                code: Some("E303".into()),
                spans: vec![SpanLabel {
                    span: *t.extra(),
                    style: SpanStyle::Primary,
                    label: None,
                }],
            }]);
        },
        None => eprintln!("fraz::parz::syntax_error(), no token..."),
    }
    Ok(())
}

fn parse_fail() -> ParseError {
    println!("parse_fail");
    ParseError::ParsingFailed
}

fn stack_overflow() -> ParseError {
    println!("stack_overflow");
    ParseError::ParsingFailed
}

// fn convert_token(t: super::lex::FrazToken) -> Option<parser::Token> { ... }
// We have to generate the whole function definition; can't generate free-standing
// pattern matches, for better or for worse...
include!(concat!(env!("OUT_DIR"), "/tokcvt.rs"));

pub fn tryparse(toks: Vec<super::lex::FrazToken>, cm: codemap::CodeMap)
            -> Result<syn::TransUnit, ParseError> {
    let mut p = parser::Parser::new(&cm);
    for tok in toks.into_iter() {
        if tok.tok < 0 {
            // skip whitespace and comments
        } else {
            let pt = convert_token(tok).ok_or(ParseError::InvalidToken);
            p.parse(pt?)?;
        }
    }
    let (ast, _cm) = p.end_of_input()?;
    println!("{:?}", ast);
    Ok(ast)

}
