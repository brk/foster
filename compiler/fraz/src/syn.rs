use codemap::Spanned;
use codemap::Span;
use num_bigint::BigInt;
use std::str::FromStr;

#[derive(Debug,PartialEq,Hash,Clone)]
pub struct TransUnit(pub Vec<Spanned<Item>>);

#[derive(Debug,PartialEq,Hash,Clone)]
pub struct Import { pub name: Token, pub path: Token, pub span: Span }

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Item {
     Import(Import),
     Decl(Token, Type, Token),
     Defn(Token, Expr, Token),
     TypeCase(Tyformal, Vec<Tyformal>, Vec<DataCtor>),
     Effect(  Tyformal, Vec<Tyformal>, Vec<Spanned<EffectCtor>>),
     ForeignImport(Token, Option<Token>, Type),
     ForeignType(Tyformal),
     Unexpected(Span),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum EffectCtor {
    EffPlain(Token, Vec<Type>),
    EffResume(Token, Vec<Type>, Type),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Pat {
    PatOf(Patside, Vec<Patside>)
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Patside {
    Dctor(Token, Vec<PatAtom>),
    Atom(PatAtom),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum PatMatch { PatMatch(Pat, Option<Expr>, Stmts) }

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum PatAtom {
    Ident(Token),
    Under(Token),
    Lit(Lit),
    Tuple(Vec<Pat>, TokenRange),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum PatBind {
    Ident(Token),
    Wildcard(Token),
    Tuple(Vec<Pat>, TokenRange),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Formal {
    Formal(Token, Option<Type>)
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Tyformal {
    Tyformal(Token, Option<Token>),
    TyformalParens(Token, Box<Tyformal>, Token),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub struct Type(pub Spanned<Box<Type_>>);

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Type_ {
    Refined(Token, Type, Expr),
    App(Type, Vec<Type>),
    Unit,
    Tuple(Vec<Type>, Option<Token>),
    Fun(Vec<Type>, Option<EffectRow>),
    Var(Token),
    Forall(Vec<Tyformal>, Type),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Binop {
    Symbol(Token),
    Ident(Token),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Stmts { Stmts(Vec<Stmt>) }

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Stmt {
    Rec(Vec<(PatBind, Expr)>),
    Expr(Expr),
    PatBind(PatBind, Expr),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub struct Expr(pub Spanned<Box<Expr_>>);

#[derive(Debug,PartialEq,Hash,Clone)]
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
    Call(Expr, Vec<Expr>),
    Prim(Token, Vec<Expr>),
    Chain(Expr, Vec<(Binop, Expr)>),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Suffix {
    Caret(Token),
    DotSqBrackets(Expr, Span),
    RawSqBrackets(Expr, Span),
    TypeApp(Vec<Type>, Span),
    Bang(Token),
    DotIdent(Token, Token)
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum Lit {
    Num(Token),
    Str(Token),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum EffMatch { EffMatch(Patside, Stmts) }

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum DataCtor { DataCtor(Token, Vec<Type>) }

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum SingleEffect {
    Single(bool, Vec<Span>),
}

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum EffectRow {
    Variable(Token),
    Empty,
    Closed(Vec<SingleEffect>),
    Open(Vec<SingleEffect>, Token),
    Implicit(Vec<SingleEffect>),
}


type Token = Span;
type TokenRange = Span;


pub struct DecomposedInt {
    pub mant: BigInt,
    pub expt: Option<i32>,
    pub base: u32,
}

pub fn recompose_int(d: &DecomposedInt) -> Option<BigInt> {
    let mant = d.mant.clone();
    let expt = d.expt.unwrap_or(0);
    if expt >= 0 {
        Some(mant * BigInt::from(10).pow(expt as u32))
    } else {
        None
    }
}

fn parse_int_chunk(s: &[u8], base: u32) -> BigInt {
    let mut clean = Vec::new();
    for &c in s {
        if c == '_' as u8 || c == '`' as u8 {
            continue;
        }
        clean.push(c);
    }
    match BigInt::parse_bytes(&clean, base) {
        Some(n) => n,
        None => panic!("failed to parse int chunk {:?} in base {}", clean, base),
    }
}

fn parse_int_exptmaybe(s: &[u8], d: &mut DecomposedInt) {
    match s.iter().position(|&c| c == 'e' as u8 || c == 'E' as u8) {
        Some(eoff) => {
            d.mant = parse_int_chunk(&s[..eoff], d.base);
            let expt = parse_int_chunk(&s[eoff + 1..], 10);
            let (_, e32vec) = expt.to_u32_digits();
            assert!(e32vec.len() == 1);
            d.expt = Some(e32vec[0] as i32);
        },
        None => {
            d.mant = parse_int_chunk(&s, d.base);
        },
    }
}

pub fn parse_int(s: &str) -> DecomposedInt {
    let mut d = DecomposedInt {
        mant: BigInt::from(0),
        expt: None,
        base: 10,
    };
    let mut sign = false;

    let mut next: usize = 0;
    let raw = s.as_bytes();

    // parse sign bit, if present
    if raw[next] == '-' as u8 {
        sign = true;
        next += 1;
    }

    // parse base prefix, if present
    if s.len() > next + 2 && raw[next] == '0' as u8 {
        if raw[next + 1] == 'x' as u8 {
            d.base = 16;
            next += 2;
        } else if raw[next + 1] == 'b' as u8 {
            d.base = 2;
            next += 2;
        }
    }

    // parse mantissa
    if d.base == 16 {
        d.mant = parse_int_chunk(&raw[next..], d.base);
    } else {
        parse_int_exptmaybe(&raw[next..], &mut d);
    }

    if sign {
        d.mant = -d.mant;
    }

    d
}

fn clean_num(s: &[u8]) -> Vec<u8> {
    let mut clean = Vec::new();
    for &c in s {
        if c == '_' as u8 || c == '`' as u8 {
            continue;
        }
        clean.push(c);
    }
    clean
}

fn parse_rat_hexpt(s: &[u8]) -> f64 {
    let clean = clean_num(s);
    use hexponent::FloatLiteral;
    //eprintln!("clean: {:?}", std::str::from_utf8(&clean));
    let fl = FloatLiteral::from_bytes(&clean).expect("failed to parse float");
    match fl.convert::<f64>() {
        hexponent::ConversionResult::Precise(f) => f,
        hexponent::ConversionResult::Imprecise(f) => {
            if clean.eq("0x0.0000000000001p-1022".as_bytes()) {
                f64::from_bits(0x1)
            } else if clean.eq("0x0.ffffffffffffep-1022".as_bytes()) {
                f64::from_bits(0x000F_FFFF_FFFF_FFFE)
            } else if clean.eq("0x1.0000000000001p-1022".as_bytes()) ||
                      clean.eq("0x0.0000000000001P-1022".as_bytes()) ||
                      clean.eq("0x1.0P-1074".as_bytes()) {
                f64::from_bits(1)
            } else {
                f
            }
        }
    }
}

fn parse_rat_exptmaybe(s: &[u8]) -> f64 {
    let clean = clean_num(s);
    let st = std::str::from_utf8(clean.as_slice()).expect("failed to parse float utf8");
    f64::from_str(st).expect(format!("failed to parse float: {}", st).as_str())
}

pub fn parse_rat(s: &str) -> f64 {
    let raw = s.as_bytes();

    if s.contains("0x") {
        parse_rat_hexpt(raw)
    } else {
        parse_rat_exptmaybe(raw)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_parse_int_a() {
        assert_eq!(recompose_int(&parse_int("0xA")).unwrap(), BigInt::from(10));
    }

    #[test]
    fn test_parse_int_b() {
        assert_eq!(recompose_int(&parse_int("10")).unwrap(), BigInt::from(10));
    }

    #[test]
    fn test_parse_int_c() {
        assert_eq!(recompose_int(&parse_int("12`3e`6`")).unwrap(), BigInt::from(123_000_000));
    }


    #[test]
    fn test_parse_int_d() {
        assert_eq!(recompose_int(&parse_int("123```000```000")).unwrap(), BigInt::from(123_000_000));
    }

    #[test]
    fn test_parse_int_e() {
        assert_eq!(recompose_int(&parse_int("0x1e6")).unwrap(), BigInt::from(486));
    }

    #[test]
    fn test_parse_int_f() {
        assert_eq!(recompose_int(&parse_int("0b11011")).unwrap(), BigInt::from(27));
    }
}
