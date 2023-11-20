use codemap::Spanned;
use codemap::Span;
use std::collections::VecDeque;

#[derive(Debug,PartialEq,Hash)]
pub struct TransUnit(pub Vec<Import>, pub Vec<Spanned<Item>>);

#[derive(Debug,PartialEq,Hash)]
pub struct Import { pub name: Token, pub path: Token, pub span: Span }

#[derive(Debug,PartialEq,Hash)]
pub enum Item {
     Decl(Token, Type, Token),
     Defn(Token, Expr, Token),
     TypeCase(Tyformal, Vec<Tyformal>, Vec<DataCtor>),
     Effect(  Tyformal, Vec<Tyformal>, Vec<Spanned<EffectCtor>>),
     ForeignImport(Token, Option<Token>, Type),
     ForeignType(Tyformal),
}

#[derive(Debug,PartialEq,Hash)]
pub enum EffectCtor {
    EffPlain(Token, Vec<Type>),
    EffResume(Token, Vec<Type>, Type),
}

#[derive(Debug,PartialEq,Hash)]
pub enum Pat {
    PatOf(Patside, Vec<Patside>)
}

#[derive(Debug,PartialEq,Hash)]
pub enum PatLhs {
    Wildcard(Token),
    Tuple(Vec<Pat>, TokenRange),
}

#[derive(Debug,PartialEq,Hash)]
pub enum Patside {
    Dctor(Token, Vec<PatAtom>),
    Atom(PatAtom),
}

#[derive(Debug,PartialEq,Hash)]
pub enum PatMatch { PatMatch(Pat, Option<Expr>, Stmts) }

#[derive(Debug,PartialEq,Hash)]
pub enum PatAtom {
    Ident(Token),
    Under(Token),
    Lit(Lit),
    Tuple(Vec<Pat>, TokenRange),
}

#[derive(Debug,PartialEq,Hash)]
pub enum PatBind {
    Ident(Token),
    PatLhs(PatLhs),
}

#[derive(Debug,PartialEq,Hash)]
pub enum Formal {
    Formal(Token, Option<Type>)
}

#[derive(Debug,PartialEq,Hash)]
pub enum Tyformal {
    Tyformal(Token, Option<Token>),
    TyformalParens(Token, Box<Tyformal>, Token),
}

#[derive(Debug,PartialEq,Hash)]
pub struct Type(pub Spanned<Box<Type_>>);

#[derive(Debug,PartialEq,Hash)]
pub enum Type_ {
    Refined(Token, Type, Expr),
    App(Type, Vec<Type>),
    Unit,
    Tuple(Vec<Type>, Option<Token>),
    Fun(Vec<Type>),
    Var(Token),
}

#[derive(Debug,PartialEq,Hash)]
pub enum Binop {
    Symbol(Token),
    Ident(Token),
}

#[derive(Debug,PartialEq,Hash)]
pub enum Stmts { Stmts(VecDeque<Stmt>) }

#[derive(Debug,PartialEq,Hash)]
pub enum Stmt {
    Rec(Vec<(PatBind, Expr)>, Span),
    Expr(Expr),
    ExprBind(Expr, Expr),
    PatBind(PatLhs, Expr),
}

#[derive(Debug,PartialEq,Hash)]
pub struct Expr(pub Spanned<Box<Expr_>>);

#[derive(Debug,PartialEq,Hash)]
pub enum Expr_ {
    Var(Token),
    Lit(Lit),
    If(Stmts, Stmts, Option<Stmts>),
    Case(Expr, Vec<PatMatch>),
    Unit,
    TypeAscription(Expr, Type),
    Tuple(Expr, Vec<Expr>, Option<Token>),
    Handler(Expr, Vec<EffMatch>, Option<Expr>),
    ValAbs(Option<Vec<Tyformal>>, Vec<Formal>, Option<Stmts>),
    LValue(Expr, Vec<Suffix>),
    Call(Vec<Expr>),
    Prim(Token, Vec<Expr>),
    Chain(Expr, Vec<(Binop, Expr)>),
}

#[derive(Debug,PartialEq,Hash)]
pub enum Suffix {
    Caret(Token),
    DotSqBrackets(Expr, Span),
    RawSqBrackets(Expr, Span),
    Bang(Token),
}

#[derive(Debug,PartialEq,Hash)]
pub enum Lit {
    Num(Token),
    Str(Token),
}

#[derive(Debug,PartialEq,Hash)]
pub enum EffMatch { EffMatch(Patside, Stmts) }

#[derive(Debug,PartialEq,Hash)]
pub enum DataCtor { DataCtor(Token, Vec<Type>) }

type Token = Span;
type TokenRange = Span;