use std::vec;
use std::fs::File;
use std::io::Write;
use std::io::BufWriter;

use crate::syn::*;
use codemap::Spanned;
use codemap::Span;
use codemap::CodeMap;

#[derive(Debug,PartialEq,Hash,Clone)]
pub enum ChezSyntax {
    Raw(String),
    Call(Vec<ChezSyntax>),
    TopForms(Vec<ChezSyntax>),
}

pub fn emit(cs: &ChezSyntax, out: &mut File) -> std::io::Result<()> {
    let mut buf = BufWriter::new(out);
    emit_buf(cs, &mut buf)?;
    buf.flush()
}


pub fn emit_buf(cs: &ChezSyntax, out: &mut BufWriter<&mut File>) -> std::io::Result<()> {
    match cs {
        ChezSyntax::Raw(s) => write!(out, "{}", s),
        ChezSyntax::Call(cs) => {
            write!(out, "(")?;
            for c in cs {
                emit_buf(c, out)?;
                write!(out, " ")?;
            }
            write!(out, ")\n")?;
            Ok(())
        },
        ChezSyntax::TopForms(cs) => {
            for c in cs {
                emit_buf(c, out)?;
                writeln!(out, "")?;
            }
            Ok(())
        }
    }
}

fn tochez_lit(lit: &Lit, cm: &CodeMap) -> ChezSyntax {
    match lit {
        Lit::Num(tok) => {
            let s = span_str(cm, tok);
            if s.contains('.') || s.contains("e-") {
                let v = crate::syn::parse_rat(&s);
                if v.is_sign_negative() && v == -0.0 {
                    ChezSyntax::Raw("-0.0".to_string())
                } else {
                    ChezSyntax::Raw(format!("{}", v))
                }
            } else {
                let d = crate::syn::parse_int(&s);
                match crate::syn::recompose_int(&d) {
                    Some(big) => {
                        ChezSyntax::Raw(format!("{}", big))
                    },
                    None => {
                        let v = crate::syn::parse_rat(&s);
                        ChezSyntax::Raw(format!("{}", v))
                    },
                }
            }
        },
        Lit::Str(tok) => {
            let p = parse_str_lit(span_ref(cm, tok));
            if p.is_byt {
                let mut s = String::new();
                s.push_str("(vector");
                s.reserve(3 * p.bytecontents.len());
                for c in p.bytecontents.iter() {
                    s.push_str(format!(" {}", c).as_str());
                }
                s.push(')');
                ChezSyntax::Raw(s)
            } else {
                ChezSyntax::Raw(format!("(TextFragment-strlit \"{}\" {})", p.strcontents, p.utf8len))
            }
        },
    }
}

struct ParsedStrLit {
    strcontents: String,
    bytecontents: Vec<u8>,
    is_raw: bool,
    is_byt: bool,
    utf8len: isize,
}

/// Returns the contents of the string literal with escape sequences translated for Chez.
/// The input string must be a valid string literal, including the surrounding quotes.
fn parse_str_lit(s: &str) -> ParsedStrLit {
    let mut p = ParsedStrLit { strcontents: String::new(), bytecontents: Vec::new(), is_raw: false, is_byt: false, utf8len: 0 };
    let mut curr = 0;
    let b = s.as_bytes();
    if b[curr] == 'r' as u8 {
        p.is_raw = true;
        curr += 1;
    }
    if b[curr] == 'b' as u8 {
        p.is_byt = true;
        curr += 1;
    }
    let pastflags = &b[curr..];
    let mut qsz = 1;
    if pastflags.eq("\"\"".as_bytes()) { return p; }
    if pastflags.eq("''".as_bytes()) { return p; }

    if pastflags.starts_with("\'\'\'".as_bytes())
     || pastflags.starts_with("\"\"\"".as_bytes()) {
        qsz = 3;
    }

    let leading_nl_offset = if pastflags[qsz] == '\n' as u8 { 1 } else { 0 };

    let raw = &pastflags[qsz + leading_nl_offset..pastflags.len()-qsz];
    
    p.utf8len = raw.len() as isize;
    if p.is_raw {
        match std::str::from_utf8(raw) {
            Ok(s) => {
                for c in s.chars() {
                    p.strcontents.push(c);
                    if c == '\\' {
                        p.strcontents.push('\\');
                    }
                }
            }
            Err(e) => panic!("parse_str_lit: invalid raw string: {:?}", e),
        }
    } else {
        tochez_str_lit_contents(raw, &mut p);
    }
    p
}

fn utf8_encoded_len(codepoint: u32) -> isize {
    if codepoint <= 0x7f {
        1
    } else if codepoint <= 0x7ff {
        2
    } else if codepoint <= 0xffff {
        3
    } else if codepoint <= 0x10ffff {
        4
    } else {
        panic!("utf8_encoded_len: invalid codepoint: {:x}", codepoint);
    }
}

fn tochez_str_lit_contents(raw: &[u8], p: &mut ParsedStrLit) {
    let mut state = 0; // 1 = saw backslash, 2 = parsing hex {}, 3 = parsing hex 1 of 2, 4 = parsing hex 2 of 2
    let mut cooked = Vec::new();
    let mut hex: u32 = 0;
    for cref in raw {
        let c = *cref;
        match state {
            0 => {
                p.utf8len -= 1;
                match (c, p.is_byt) {
                    (b'\\', _) => state = 1,
                    (b'\r', true) => {},
                    (b'\n', true) => {},
                    _ => { cooked.push(c); p.utf8len += 1 },
                }
            },
            1 => {
                match c {
                    b'\\' => if p.is_byt { cooked.push(c); } else { cooked.push(b'\\'); cooked.push(b'\\'); },
                    b'\'' => if p.is_byt { cooked.push(c); } else { cooked.push(b'\\'); cooked.push(b'\''); },
                    b'\"' => if p.is_byt { cooked.push(c); } else { cooked.push(b'\\'); cooked.push(b'"'); },
                    b'n' => if p.is_byt { cooked.push(c); } else { cooked.push(b'\\'); cooked.push(b'n'); },
                    b'r' => if p.is_byt { cooked.push(c); } else { cooked.push(b'\\'); cooked.push(b'r'); },
                    b't' => if p.is_byt { cooked.push(c); } else { cooked.push(b'\\'); cooked.push(b't'); },
                    b'u' => { p.utf8len -= 1; if !p.is_byt { cooked.push(b'\\'); cooked.push(b'x'); } },
                    b'x' => { p.utf8len -= 1; if !p.is_byt { cooked.push(b'\\'); cooked.push(b'x'); } },
                    _ => panic!("parse_str_lit: invalid escape sequence: \\{}", c),
                }
                state = match c {
                    b'u' => 2,
                    b'x' => 3,
                    _ => 0,
                };
                assert!(hex == 0);
            },
            2 => {
                p.utf8len -= 1;
                match c {
                    b'{' => continue,
                    b'0'..=b'9' => {
                        hex = (hex << 4) | ((c - b'0') as u32); if !p.is_byt { cooked.push(c); }
                    },
                    b'a'..=b'f' => {
                        hex = (hex << 4) | ((10 + c - b'a') as u32); if !p.is_byt { cooked.push(c); }
                    },
                    b'A'..=b'F' => {
                        hex = (hex << 4) | ((10 + c - b'A') as u32); if !p.is_byt { cooked.push(c); }
                    },
                    b'}' => {
                        state = 0;
                        p.utf8len += utf8_encoded_len(hex);
                        if p.is_byt {
                            if hex == 0 {
                                cooked.push(b'\0');
                            } else {
                                let mut hexrev = Vec::new();
                                while hex > 0 {
                                    hexrev.push((hex & 0xff) as u8);
                                    hex = hex >> 8;
                                }
                                for c in hexrev.iter().rev() {
                                    cooked.push(*c);
                                }
                            }
                        } else {
                            cooked.push(b';');
                        }
                    },
                    _ => panic!("parse_str_lit: invalid hex escape sequence: \\x{}", c),
                }
            },
            3 => {
                assert!(hex == 0);
                p.utf8len -= 1;
                match c {
                    b'0'..=b'9' => {
                        if p.is_byt { hex = (c - b'0') as u32; } else { cooked.push(c); }
                    },
                    b'a'..=b'f' => {
                        if p.is_byt { hex = (10 + c - b'a') as u32; } else { cooked.push(c); }
                    },
                    b'A'..=b'F' => {
                        if p.is_byt { hex = (10 + c - b'A') as u32; } else { cooked.push(c); }
                    },
                    _ => panic!("parse_str_lit: invalid hex escape sequence: \\x{}", c),
                }
                state = 4;
            },
            4 => {
                match c {
                    b'0'..=b'9' => {
                        if p.is_byt { hex = (hex << 4) | ((c - b'0') as u32); } else { cooked.push(c); }
                    },
                    b'a'..=b'f' => {
                        if p.is_byt { hex = (hex << 4) | ((10 + c - b'a') as u32); } else { cooked.push(c); }
                    },
                    b'A'..=b'F' => {
                        if p.is_byt { hex = (hex << 4) | ((10 + c - b'A') as u32); } else { cooked.push(c); }
                    },
                    _ => panic!("parse_str_lit: invalid hex escape sequence: \\x{}", c),
                }
                state = 0;
                if p.is_byt {
                    if hex == 0 {
                        cooked.push(b'\0');
                    } else {
                        assert!(hex <= 0xff);
                        /*
                        let mut hexrev = Vec::new();
                        while hex > 0 {
                            hexrev.push((hex & 0xff) as u8);
                            hex = hex >> 8;
                        }
                        for c in hexrev.iter().rev() {
                            cooked.push(*c);
                        }
                        */
                        cooked.push(hex as u8);
                        hex = 0;
                    }
                } else {
                    cooked.push(b';');
                }
            },
            _ => panic!("parse_str_lit: invalid state: {}", state),
        }
    }
    if p.is_byt {
        p.bytecontents = cooked;
    } else {
        p.strcontents.push_str(std::str::from_utf8(&cooked).unwrap());
    }
}

fn tochez_patatom(patatom: &PatAtom, cm: &CodeMap) -> ChezSyntax {
    match patatom {
        PatAtom::Ident(name) => {
            let s = span_str(cm, name);
            ChezSyntax::Raw(s)
        },
        PatAtom::Under(_) => {
            ChezSyntax::Raw("_".to_string())
        },
        PatAtom::Lit(lit) => {
            tochez_lit(lit, cm)
        },
        PatAtom::Tuple(pats, _range) => {
            let mut forms = Vec::new();
            forms.push(ChezSyntax::Raw("list".to_string()));
            for pat in pats {
                forms.push(tochez_pat(pat, cm));
            }
            ChezSyntax::Call(forms)
        },
    }
}

fn tochez_patside(patside: &Patside, cm: &CodeMap) -> ChezSyntax {
    match patside {
        Patside::Dctor(name, pats) => {
            let mut forms = Vec::new();
            forms.push(ChezSyntax::Raw(format!("{}?", span_str(cm, name))));
            for pat in pats {
                forms.push(tochez_patatom(pat, cm));
            }
            ChezSyntax::Call(forms)
        },
        Patside::Atom(patatom) => {
            tochez_patatom(patatom, cm)
        },
    }
}

fn tochez_pat(pat: &Pat, cm: &CodeMap) -> ChezSyntax {
    match pat {
        Pat::PatOf(lhs, rhs) => {
            let mut forms = Vec::new();
            forms.push(tochez_patside(lhs, cm));
            for side in rhs {
                forms.push(tochez_patside(side, cm));
            }
            ChezSyntax::Call(forms)
        },
    }
}

fn tochez_patlhs(patlhs: &PatLhs, cm: &CodeMap) -> ChezSyntax {
    match patlhs {
        PatLhs::Wildcard(_) => {
            ChezSyntax::Raw("...wildcard...".to_string())
        },
        PatLhs::Tuple(pats, _range) => {
            let mut forms = Vec::new();
            forms.push(ChezSyntax::Raw("list".to_string()));
            for pat in pats {
                forms.push(tochez_pat(pat, cm));
            }
            ChezSyntax::Call(forms)
        },
    }
}

fn tochez_patbind(patbind: &PatBind, expr: &Expr, cm: &CodeMap) -> ChezSyntax {
    match patbind {
        PatBind::Ident(name) => {
            let s = span_str(cm, name);
            ChezSyntax::Call(vec![ChezSyntax::Raw(s), tochez_expr(expr, cm)])
        },
        PatBind::PatLhs(patlhs) => {
            let lhs = tochez_patlhs(patlhs, cm);
            ChezSyntax::Call(vec![lhs, tochez_expr(expr, cm)])
        },
    }
}

fn tochez_let_1(name: ChezSyntax, expr: ChezSyntax, cont: ChezSyntax) -> ChezSyntax {
    ChezSyntax::Call(vec![ChezSyntax::Raw("let".to_string()),
        ChezSyntax::Call(vec![ChezSyntax::Call(vec![name, expr])]), cont])
}

fn tochez_stmt_then(stmt: &Stmt, cont: ChezSyntax, cm: &CodeMap) -> ChezSyntax {
    match stmt {
        Stmt::Rec(patbinds, _span) => {
            let binds = patbinds.iter().map(|pb| tochez_patbind(&pb.0, &pb.1, cm)).collect();
            ChezSyntax::Call(vec![ChezSyntax::Raw("letrec".to_string()), ChezSyntax::Call(binds), cont])
        },
        Stmt::Expr(expr) => {
            let lhs = ChezSyntax::Raw("_".to_string());
            let rhs = tochez_expr(expr, cm);
            tochez_let_1(lhs, rhs, cont)
        },
        Stmt::ExprBind(lhs, rhs) if expr_is_var(lhs) => {
            let lhs = tochez_expr(lhs, cm);
            let rhs = tochez_expr(rhs, cm);
            tochez_let_1(lhs, rhs, cont)
        },
        Stmt::ExprBind(lhs, rhs) => {
            let pat = Pat::PatOf(Patside::Atom(patatom_of_expr(lhs.clone(), &cm)), Vec::new());
            let fail = ChezSyntax::Raw("\"let-expr match failure\"".to_string());
            let c1 = tochez_scrut_cont_body(&pat, cont, &None, fail, cm);
            tochez_let_1(ChezSyntax::Raw("_scrutinee".to_string()), tochez_expr(&rhs, cm), c1)        },
        Stmt::PatBind(lhs, rhs) => {
            let pat = Pat::PatOf(Patside::Atom(patatom_of_patlhs(lhs)), Vec::new());
            let fail = ChezSyntax::Raw("\"let-pat match failure\"".to_string());
            let c1 = tochez_scrut_cont_body(&pat, cont, &None, fail, cm);
            tochez_let_1(ChezSyntax::Raw("_scrutinee".to_string()), tochez_expr(&rhs, cm), c1)
        },
    
    }
}

fn patatom_of_patlhs(patlhs: &PatLhs) -> PatAtom {
    match patlhs {
        PatLhs::Wildcard(tok) => {
            PatAtom::Under(tok.clone())
        },
        PatLhs::Tuple(pats, _range) => {
            PatAtom::Tuple(pats.clone(), _range.clone())
        },
    }
}

fn patatom_of_expr(expr: Expr, cm: &CodeMap) -> PatAtom {
    let e0span = expr.0.span;
    match *expr.0.node {
        Expr_::Var(tok) => {
            PatAtom::Ident(tok)
        },
        Expr_::Lit(lit) => {
            PatAtom::Lit(lit)
        },
        Expr_::Tuple(expr, exprs, _hashtok) => {
            let mut pats = Vec::new();
            pats.push(pat_of_expr(expr, cm));
            for e in exprs {
                pats.push(pat_of_expr(e, cm));
            }
            PatAtom::Tuple(pats, e0span)
        },
        other => {
            panic!("patatom_of_expr: not a pattern atom: {:?}\n{:?}", other, 
                cm.look_up_span(e0span))
        },
    }
}

fn pat_of_expr(expr: Expr, cm: &CodeMap) -> Pat {
    let e0span = expr.0.span;
    let boxe = expr.0.node;
    match *boxe {
        Expr_::Var(tok) => {
            let s = span_ref(cm, &tok);
            if s.eq("True") || s.eq("False") {
                Pat::PatOf(Patside::Dctor(tok, Vec::new()), Vec::new())
            } else {
                Pat::PatOf(Patside::Atom(PatAtom::Ident(tok)), Vec::new())
            }
        },
        Expr_::Lit(lit) => {
            Pat::PatOf(Patside::Atom(PatAtom::Lit(lit)), Vec::new())
        },
        Expr_::Tuple(expr, exprs, _hashtok) => {
            let mut pats = Vec::new();
            pats.push(pat_of_expr(expr, cm));
            for e in exprs {
                pats.push(pat_of_expr(e, cm));
            }
            Pat::PatOf(Patside::Atom(PatAtom::Tuple(pats, e0span)), Vec::new())
        },
        other => {
            panic!("pat_of_expr: not a pattern: {:?}", other)
        },
    }
}

fn expr_is_var(expr: &Expr) -> bool {
    match &*expr.0.node {
        Expr_::Var(_) => true,
        _ => false,
    }
}

fn tochez_stmt_single(stmt: &Stmt, cm: &CodeMap) -> ChezSyntax {
    match stmt {
        Stmt::Expr(expr) => {
            tochez_expr(expr, cm)
        },
        _ => {
            tochez_stmt_then(stmt, ChezSyntax::Raw("unit".to_string()), cm)
        },
    }
}

fn tochez_stmts_vd(stmts: &std::collections::VecDeque<Stmt>, cm: &CodeMap) -> ChezSyntax {
    assert!(stmts.len() > 0);
    // Foster statements are syntactically single bindings or a bare expression,
    // but semantically they are a sequence of (possibly unnamed) bindings,
    // so we process them in reverse order to build up a nested let expression,
    // rather than using `begin` or such.
    
    let mut cont = tochez_stmt_single(stmts.back().unwrap(), cm);
    for stmt in stmts.iter().rev().skip(1) {
        cont = tochez_stmt_then(stmt, cont, cm);
    }
    cont
}

fn tochez_stmts(stmts: &Stmts, cm: &CodeMap) -> ChezSyntax {
    match stmts {
        crate::syn::Stmts::Stmts(stmts) => {
            tochez_stmts_vd(stmts, cm)
        }
    }
}

fn tochez_type(_typ: &Type, _cm: &CodeMap) -> ChezSyntax {
    ChezSyntax::Raw("...type...".to_string())
}

fn tochez_vector_ref_checked(expr: ChezSyntax, index: ChezSyntax, cm: &CodeMap, span: &Span) -> ChezSyntax {
    let who = ChezSyntax::Raw("#f".to_string());
    let msg = ChezSyntax::Raw(format!("\"vector-ref-checked: {} at line {} of {}\"",
        span_ref(cm, &span),
        cm.look_up_span(*span).begin.line + 1,
        cm.look_up_span(*span).file.name()));
    ChezSyntax::Call(vec![ChezSyntax::Raw("vector-ref-checked".to_string()), expr, index, who, msg])
}

fn tochez_suffix(suffix: &Suffix, expr: ChezSyntax, cm: &CodeMap) -> ChezSyntax {
    match suffix {
        Suffix::Caret(_) => {
            ChezSyntax::Call(vec![ChezSyntax::Raw("deref".to_string()), expr])
        },
        Suffix::DotSqBrackets(e_k, span) => {
            tochez_vector_ref_checked(expr, tochez_expr(e_k, cm), cm, span)
        },
        Suffix::RawSqBrackets(e_k, span) => {
            tochez_vector_ref_checked(expr, tochez_expr(e_k, cm), cm, span)
        },
        Suffix::TypeApp(_, _) => {
            expr
        },
        Suffix::Bang(_) => {
            ChezSyntax::Call(vec![expr])
        },
        Suffix::DotIdent(_, _) => {
            ChezSyntax::Raw("...dotident...".to_string())
        },
    }
}

fn span_ref<'cm>(cm: &'cm CodeMap, span: &Span) -> &'cm str {
    cm.find_file(span.low()).source_slice(*span)
}

fn span_str(cm: &CodeMap, span: &Span) -> String {
    span_ref(cm, span).to_string()
}


fn formal_name(cm: &CodeMap, formal: &Formal) -> String {
    match formal {
        Formal::Formal(name, _ty) => tochez_name(name, cm),
    }
}

fn bindingpower(cm: &CodeMap, binop: Span) -> i32 {
    let s = span_ref(cm, &binop);
    match s.chars().nth(0).unwrap() {
        '|' => 10,
        _ => 100
    }
}

fn leftassoc(cm: &CodeMap, binop: Span) -> bool {
    let s = span_ref(cm, &binop);
    match s.chars().nth(0).unwrap() {
        '^' => false,
        _ => true
    }
}

fn binop_tok(binop: Binop) -> Span {
    match binop {
        Binop::Ident(tok) => tok,
        Binop::Symbol(tok) => tok,
    }
}

enum PipeRhs {
    Call(Expr, Vec<Expr>),
    NonCall(Expr),
}

fn pipe_rhs(e: Expr) -> PipeRhs {
    match &*e.0.node {
        Expr_::Call(callee, args) => {
            PipeRhs::Call(callee.clone(), args.clone())
        },
        _ => {
            PipeRhs::NonCall(e)
        }
    }
}

/*
fn poke_rhs(e: Expr) -> Option<Expr> {
    match &*e.0.node {
        Expr_::Call(args) => {
            PipeRhs::Call(args.clone())
        },
        _ => {
            PipeRhs::NonCall(e)
        }
    }
}
*/

fn binop_call(cm: &CodeMap, binoptok: Span, lhs: Expr, rhs: Expr) -> Expr {
    let binopstr = span_ref(cm, &binoptok);
    let newspan = lhs.0.span.merge(rhs.0.span);
    if binopstr == "|>" {
        match pipe_rhs(rhs) {
            PipeRhs::Call(callee, mut args) => {
                // eprintln!("pipe-call lhs sexpr: {:?}", tochez_expr(&lhs, cm));
                // for a in args.iter_mut() {
                //     eprintln!("     pipe-call arg sexpr: {:?}", tochez_expr(&a, cm));
                // }

                //args.insert(0, lhs);
                args.push(lhs);
                return Expr(Spanned { node: Box::new(Expr_::Call(callee, args)), span: newspan });
            },
            PipeRhs::NonCall(e) => {
                return Expr(Spanned { node: Box::new(Expr_::Call(e, vec![lhs])), span: newspan });
            }
        }
    }
    /*
    if binopstr == ">^" {
        match poke_rhs(rhs) {
            PokeRhs::ArraySubscript(mut args) => {
                // todo
            },
            _ => {
                // todo
            }
        }
    }
    */
    let binopvar = Expr(Spanned { node: Box::new(Expr_::Var(binoptok)), span: binoptok });
    let n = Expr_::Call(binopvar, vec![lhs, rhs]);
    Expr(Spanned { node: Box::new(n), span: newspan })
}

fn spill(cm: &CodeMap, binoptok: Span, exprq: &mut Vec<Expr>) {
    let rhs = exprq.pop().unwrap();
    let lhs = exprq.pop().unwrap();
    // eprintln!("spill {} lhs sexpr: {:?}", span_ref(cm, &binoptok), tochez_expr(&lhs, cm));
    // eprintln!("spill {} rhs sexpr: {:?}", span_ref(cm, &binoptok),  tochez_expr(&rhs, cm));
    exprq.push(binop_call(cm, binoptok, lhs, rhs));
}

fn parse_chain(cm: &CodeMap, lhs: &Expr, chain: &Vec<(Binop, Expr)>) -> Expr {

    // eprintln!("chain lhs: {:?}", span_ref(cm, &lhs.0.span));
    // for (binop, expr) in chain.iter() {
    //     eprintln!("     chain binop: {:?}", span_ref(cm, &binop_tok(binop.clone())));
    //     eprintln!("     chain rexpr: {:?}", span_ref(cm, &expr.0.span));
    //     eprintln!("     chain sexpr: {:?}", tochez_expr(expr, cm));
    // }


    // eprintln!("chain lhs: {:?}", lhs);
    // for (binop, expr) in chain.iter() {
    //     eprintln!("     chain rexpr: {:?}", expr);
    // }


    let mut exprq = vec![lhs.clone()];
    let mut opq: Vec<Span> = vec![];
    // Invariant: len(exprq) == len(opq) + 1
    for (binop, rhs) in chain {
        let binoptok = binop_tok(binop.clone());

        // Must push binop onto opq, but first spill any ops with higher precedence
        loop {
            if let Some(topop) = opq.pop() {
                let nextbp = bindingpower(cm, binoptok);
                let topbp = bindingpower(cm, topop);
                if nextbp <= topbp && leftassoc(cm, binoptok) {
                    // Spill decreases length of exprq by 1, matching pop of opq.
                    // eprintln!("spill because top ({}) bound tighter and binop ({}) was leftassoc",
                    //     span_ref(cm, &topop), span_ref(cm, &binoptok));
                    spill(cm, topop, &mut exprq);
                } else {
                    // eprintln!("restore {}  (@ {}) then push tighter-binding {} (@ {})", span_ref(cm, &topop), topbp, span_ref(cm, &binoptok), nextbp);
                    // Previous operator binds tighter
                    opq.push(topop);
                    opq.push(binoptok);

                    for ex in exprq.iter() {
                        eprintln!("     exprq sexpr: {:?}", tochez_expr(ex, cm));
                    }

                    // Invariant restored
                    break;
                }
            } else {
                // No previous operator, so push this one
                // eprintln!("no prev operator so push {}", span_ref(cm, &binoptok));
                opq.push(binoptok);
                // Invariant restored
                break;
            }
        }

        exprq.push(rhs.clone());
    };

    // eprintln!("after chain loop, left with:");
    // for ex in exprq.iter() {
    //     eprintln!("     exprq sexpr: {:?}", tochez_expr(ex, cm));
    // }
    // for op in opq.iter() {
    //     eprintln!("     opq: {:?}", span_ref(cm, op));
    // }

    assert!(exprq.len() == opq.len() + 1);
    while let Some(topop) = opq.pop() {
        // eprintln!("spill to consolidate remaining ops: {}", span_ref(cm, &topop));
        spill(cm, topop, &mut exprq);
    }
    assert!(exprq.len() == 1);
    let rv = exprq.pop().unwrap();
    // eprintln!("parse_chain returning sexpr: {:?}", tochez_expr(&rv, cm));
    rv
}

struct MatchContext {
    accessors: Vec<ChezSyntax>,
    binders: Vec<ChezSyntax>,
    boundvals: Vec<ChezSyntax>,
}

/* TODO:
    recursively examine patterns, keeping a stack of accessors.
    a single-entry stack is the scrutinzed variable.
    a multi-entry stack is a chain of accessors to use on the scrutinized variable.
    for example, looking at the pattern    $Foo ($Bar x 5)
    we'd examine $Bar x y  with the stack [scrutinee, Foo-0-get]
    and then examine  x    with the stack [scrutinee, Foo-0-get, Bar-0-get]
    and then examine  5    with the stack [scrutinee, Foo-0-get, Bar-1-get]
*/

fn tochez_scrut_accessors(mc: &MatchContext) -> ChezSyntax {
    assert!(mc.accessors.len() > 0);
    mc.accessors.iter().fold(None, |acc: Option<ChezSyntax>, accessor| {
        match acc {
            None => Some(accessor.clone()),
            Some(acc) => Some(ChezSyntax::Call(vec![accessor.clone(), acc])),
        }
    }).unwrap()
}

// Return a guard expression, if any, and augment the list of binding expression values.
// Integer literals become guard expressions; identifiers and wildcards do not need guards.
fn tochez_scrut_patatom(patatom: &PatAtom, mc: &mut MatchContext, cm: &CodeMap, collect_bindings: bool) -> Option<ChezSyntax> {
    match patatom {
        PatAtom::Ident(name) => {
            // Boolean constants are treated as literals, not identifiers.
            if span_ref(cm, name).eq("True") {
                let litval = ChezSyntax::Raw("#t".to_string());
                 Some(ChezSyntax::Call(vec![ChezSyntax::Raw("eq?".to_string()), litval,
                                                            tochez_scrut_accessors(&mc)]))
            } else if span_ref(cm, name).eq("False") {
                let litval = ChezSyntax::Raw("#f".to_string());
                 Some(ChezSyntax::Call(vec![ChezSyntax::Raw("eq?".to_string()), litval,
                                                            tochez_scrut_accessors(&mc)]))
            } else {
                let accessor = tochez_scrut_accessors(&mc);
                if collect_bindings {
                    mc.binders.push(ChezSyntax::Raw(span_str(cm, name)));
                    mc.boundvals.push(accessor);
                }
                None
            }
        },
        PatAtom::Under(_) => {
            None
        },
        PatAtom::Lit(lit) => {
            let litval = tochez_lit(lit, cm);
            Some(ChezSyntax::Call(vec![ChezSyntax::Raw("=".to_string()), litval,
                                                            tochez_scrut_accessors(&mc)]))
        },
        PatAtom::Tuple(pats, _range) => {
            if pats.is_empty() {
                None
            } else if pats.len() == 1 {
                Some(tochez_scrut_pat(&pats[0], mc, cm))
            } else {
                let mut forms = Vec::new();
                forms.push(ChezSyntax::Raw("and".to_string()));
                for (n, pat) in pats.iter().enumerate() {
                    mc.accessors.push(ChezSyntax::Raw(format!("tuple-{}-get", n)));
                    let residual = tochez_scrut_pat(pat, mc, cm);
                    mc.accessors.pop();
                    forms.push(residual);
                }
                Some(ChezSyntax::Call(forms))
            }
        },
    }
}

/// Return a boolean expression indicating matchability, and augment the list of binding expression values.
///
/// For matches against a constructor, the inspected value must match the constructor tag,
/// and the constructor arguments must match the pattern arguments.
fn tochez_scrut_patside(pat: &Patside, mc: &mut MatchContext, cm: &CodeMap, collect_bindings: bool) -> ChezSyntax {
    match pat {
        Patside::Dctor(name, pats) => {
            let mut andforms = Vec::new();
            andforms.push(ChezSyntax::Raw("and".to_string()));
            andforms.push(ChezSyntax::Call(vec![ChezSyntax::Raw(format!("{}?", span_str(cm, name))),
                                                         tochez_scrut_accessors(mc)]));
            
            for (n, pat) in pats.iter().enumerate() {
                mc.accessors.push(ChezSyntax::Raw(format!("{}-{}-get", span_str(cm, name), n)));
                let residual = tochez_scrut_patatom(pat, mc, cm, collect_bindings);
                mc.accessors.pop();
                match residual {
                    None => (),
                    Some(form) => andforms.push(form),
                }
            }
            if andforms.len() == 2 {
                andforms.pop().unwrap()
            } else {
                ChezSyntax::Call(andforms)
            }
        },
        Patside::Atom(patatom) => {
            tochez_scrut_patatom(patatom, mc, cm, collect_bindings).unwrap_or(ChezSyntax::Raw("#t".to_string()))
        },
    }
}

fn tochez_scrut_patsides(lhs: &Patside, rhs: &Vec<Patside>, mc: &mut MatchContext, cm: &CodeMap) -> ChezSyntax {
    let mut orforms = Vec::new();
    orforms.push(ChezSyntax::Raw("or".to_string()));
    orforms.push(tochez_scrut_patside(lhs, mc, cm, true));
    for side in rhs {
        orforms.push(tochez_scrut_patside(&side, mc, cm, false));
    }
    ChezSyntax::Call(orforms)
}

fn tochez_scrut_pat(pat: &Pat, mc: &mut MatchContext, cm: &CodeMap) -> ChezSyntax {
    match pat {
        Pat::PatOf(lhs, rhs) => {
            // p1 | p2 | p3
            tochez_scrut_patsides(lhs, rhs, mc, cm)
        },
    }
}

/*
fn tochez_scrut(pm: &PatMatch, cm: &CodeMap) -> (ChezSyntax, ChezSyntax, Vec<ChezSyntax>) {
    let mut mc = MatchContext { accessors: Vec::new(), binders: Vec::new(), boundvals: Vec::new() };
    match pm {
        PatMatch::PatMatch(pat, guard, stmts) => {
            let body = tochez_stmts(stmts, cm);
            let scrutinzer = tochez_scrut_pat(pat, guard, &mut mc, cm);
            (scrutinzer, body, binders)
        },
    }
}
*/

fn tochez_let_values(mc: MatchContext, body: ChezSyntax) -> ChezSyntax {
    if mc.binders.is_empty() && mc.boundvals.is_empty() {
        body
    } else if mc.binders.len() == 1 {
        tochez_let_1(mc.binders[0].clone(), mc.boundvals[0].clone(), body)
    } else {
        let mut values: Vec<ChezSyntax> = vec![ChezSyntax::Raw("values".to_string())];
        values.extend(mc.boundvals);
        let binders =
            ChezSyntax::Call(vec![ChezSyntax::Call(mc.binders),
                                  ChezSyntax::Call(values)]);
        ChezSyntax::Call(vec![ChezSyntax::Raw("let-values".to_string()),
                                         ChezSyntax::Call(vec![binders]),
                                         body])
    }
}

fn tochez_if_else(cond: ChezSyntax, iftru: ChezSyntax, iffls: ChezSyntax) -> ChezSyntax {
    let mut forms = Vec::new();
    forms.push(ChezSyntax::Raw("if".to_string()));
    forms.push(cond);
    forms.push(iftru);
    forms.push(iffls);
    ChezSyntax::Call(forms)
}

fn tochez_scrut_cont_body(pat: &Pat, body: ChezSyntax, guard: &Option<Expr>, cont: ChezSyntax, cm: &CodeMap) -> ChezSyntax {
    let mut mc = MatchContext { accessors: Vec::new(), binders: Vec::new(), boundvals: Vec::new() };

    mc.accessors.push(ChezSyntax::Raw("_scrutinee".to_string()));

    let guards = tochez_scrut_pat(pat, &mut mc, cm);
    // Without guard:
    // (if (...guards...) (let-values ((binders) (boundvals)) body) cont)
    match guard {
        None => {
            tochez_if_else(guards, tochez_let_values(mc, body), cont)
        },
        Some(guard) => {
            let contvar = ChezSyntax::Raw("_guardcont".to_string());
            let eguard = tochez_expr(guard, cm);
            let gbody = 
                tochez_let_values(mc,
                    tochez_if_else(eguard,
                        body,
                        ChezSyntax::Call(vec![contvar.clone()])));
            let contlambda = ChezSyntax::Call(vec![ChezSyntax::Raw("lambda".to_string()),
                ChezSyntax::Call(vec![]),
                cont]);
            tochez_let_1(contvar.clone(), contlambda, 
                tochez_if_else(guards, gbody, 
                    ChezSyntax::Call(vec![contvar])))
        },
    }
    // With guard:
    // (if (...guards...) (let-values ((binders) (boundvals)) (if guard body cont)) cont)
    // Except we don't want to duplicate cont, so we let-bind the cont expression and call its binder.
}

fn tochez_scrut_cont(pm: &PatMatch, cont: ChezSyntax, cm: &CodeMap) -> ChezSyntax {
    match pm {
        PatMatch::PatMatch(pat, guard, stmts) => {
            let body = tochez_stmts(stmts, cm);
            tochez_scrut_cont_body(pat, body, guard, cont, cm)
        },
    }
}

fn tochez_name(name: &Span, cm: &CodeMap) -> String {
    let s = span_str(cm, name);
    if s.eq("assert") {
        return "foster-assert".to_string()
    }
    if s.eq("delay") {
        return "_delay".to_string()
    }
    if s.eq("force") {
        return "_force".to_string()
    }
    if s.eq("list") {
        return "_list".to_string()
    }
    if s.eq("cond") {
        return "_cond".to_string()
    }
    if s.eq("when") {
        return "_when".to_string()
    }
    s
}

fn tochez_expr(ast: &Expr, cm: &CodeMap) -> ChezSyntax {
    match &*ast.0.node {
        Expr_::Lit(lit) => {
            tochez_lit(lit, cm)
        },
        Expr_::Var(name) => {
            ChezSyntax::Raw(tochez_name(name, cm))
        },
        Expr_::Call(callee, args) => {
            if args.len() == 0 {
                // In foster syntax, Call[e] == e, not (e); the equivalent to (e) is Call[LValue[e, !]]
                tochez_expr(callee, cm)
            } else {
                let mut args: Vec<ChezSyntax> = args.iter().map(|a| tochez_expr(a, cm)).collect();
                args.insert(0, tochez_expr(callee, cm));
                ChezSyntax::Call(args)
            }
            
        },
        Expr_::If(cond, then, None) => {
            let cond = tochez_stmts(&cond, cm);
            let then = tochez_stmts(&then, cm);
            let els = ChezSyntax::Raw("unit".to_string());
            ChezSyntax::Call(vec![ChezSyntax::Raw("if".to_string()), cond, then, els])
        },
        Expr_::If(cond, then, Some(els)) => {
            let cond = tochez_stmts(&cond, cm);
            let then = tochez_stmts(&then, cm);
            let els = tochez_stmts(&els, cm);
            ChezSyntax::Call(vec![ChezSyntax::Raw("if".to_string()), cond, then, els])
        },
        Expr_::Unit => {
            ChezSyntax::Raw("unit".to_string())
        },
        Expr_::TypeAscription(expr, ty) => {
            let expr = tochez_expr(&expr, cm);
            let ty = tochez_type(&ty, cm);
            ChezSyntax::Call(vec![ChezSyntax::Raw("ascribe".to_string()), expr, ty])
        },
        Expr_::Tuple(expr, exprs, _hashtok) => {
            let expr = tochez_expr(&expr, cm);
            if exprs.is_empty() {
                expr
            } else {
                let mut forms = Vec::new();
                forms.push(ChezSyntax::Raw("list".to_string()));
                forms.push(expr);
                for e in exprs {
                    forms.push(tochez_expr(&e, cm));
                }
                ChezSyntax::Call(forms)
            }
        },
        Expr_::Handler(_expr, _effmatches, _final) => {
            ChezSyntax::Raw("...handler...".to_string())
        },
        Expr_::ValAbs(_tyformals, formals, stmts) => {
            let argstrs = formals.iter().map(|f| formal_name(cm, &f)).collect::<Vec<_>>();
            let args: ChezSyntax = ChezSyntax::Call(argstrs.iter().map(|s| ChezSyntax::Raw(s.clone())).collect());
            let body = match stmts {
                None => ChezSyntax::Raw("unit".to_string()),
                Some(stmts) => {
                    tochez_stmts(stmts, cm)
                }
            };            
            ChezSyntax::Call(vec![ChezSyntax::Raw("lambda".to_string()), args, body])
        },
        Expr_::LValue(expr, suffixes) => {
            let mut expr = tochez_expr(&expr, cm);
            for suffix in suffixes {
                expr = tochez_suffix(&suffix, expr, cm);
            }
            expr
        },
        Expr_::Prim(tok, exprs) => {
            let s = span_ref(cm, tok);
            let mut forms = Vec::new();

            if s == "tuple-unboxed" {
                forms.push(ChezSyntax::Raw("list".to_string()));
            } else {
                forms.push(ChezSyntax::Raw(s.to_string()));
            }

            for e in exprs {
                forms.push(tochez_expr(&e, cm));
            }
            if s == "__COMPILES__" {
                forms.pop();
                forms.push(ChezSyntax::Raw("#f".to_string()));
            }

            if s == "kill-entire-process" {
                let lastexpr = exprs[exprs.len() - 1].0.node.clone();
                match *lastexpr {
                    Expr_::Lit(Lit::Str(strspan)) => {
                        let p = parse_str_lit(span_ref(cm, &strspan));
                        forms.pop();
                        forms.push(ChezSyntax::Raw(format!("\"{}\"", p.strcontents)));
                    },
                    _ => ()
                }
            }
            ChezSyntax::Call(forms)
        },
        Expr_::Chain(expr, chain) => {
            let parsed = parse_chain(cm, expr, chain);
            let expr = tochez_expr(&parsed, cm);
            expr
        },
        Expr_::Case(expr, patmatches) => {
            // Each body gets compiled to an expression with the
            // the pattern match binders as free variables,
            // Each pattern arm gets compiled to a function which takes a scrutinee
            // and returns either #f or a list of the bound variables.
            // The case expression then becomes a nested let expression
            // which applies each pattern arm function in turn, until one returns
            // something other than #f.

            let spanloc = cm.look_up_span(ast.0.span);
            let matchfailure: String = format!("(assertion-violation #f \"case match failure @ line {} of {}\")", spanloc.begin.line, spanloc.file.name());
            let mut form = ChezSyntax::Raw(matchfailure);

            form = patmatches.iter().rev().fold(form, |form, patchmatch| {
                tochez_scrut_cont(patchmatch, form, cm)
            });

            // let scrutinee = expr;
            // let rv_i = scrutinzers[i](scrutinee);
            // if rv_i == #f {
                // recur
            // } else {
                // let (x, y, z, ...) = rv_i;
                // bodies[i](x, y, z, ...)
            // }

            tochez_let_1(ChezSyntax::Raw("_scrutinee".to_string()), tochez_expr(&expr, cm), form)
        },
    }
}

fn _tyformal_name(cm: &CodeMap, tyformal: &Tyformal) -> String {
    match tyformal {
        Tyformal::Tyformal(name, _) => tochez_name(name, cm),
        Tyformal::TyformalParens(name, _, _) => tochez_name(name, cm),
    }
}

enum IntSizeConfig {
    ISC(i32, String, String),
}

pub fn tochez_transunit(ast: &TransUnit, cm: &CodeMap) -> ChezSyntax {
    let mut ss = vec![];

    ss.push(ChezSyntax::Raw("(import (rnrs arithmetic bitwise))".to_string()));
    ss.push(ChezSyntax::Raw("(import (rnrs io simple))".to_string()));
    ss.push(ChezSyntax::Raw("(import (rnrs bytevectors))".to_string()));
    
    ss.push(ChezSyntax::Raw("\n".to_string()));
    ss.push(ChezSyntax::Raw("(define True #t)".to_string()));
    ss.push(ChezSyntax::Raw("(define False #f)".to_string()));
    ss.push(ChezSyntax::Raw("(define unit #t)".to_string()));
    ss.push(ChezSyntax::Raw("(define ==Bool (lambda (x y) (eqv? x y)))".to_string()));

    ss.push(ChezSyntax::Raw("(define tuple-0-get (lambda (x) (list-ref x 0) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define tuple-1-get (lambda (x) (list-ref x 1) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define tuple-2-get (lambda (x) (list-ref x 2) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define tuple-3-get (lambda (x) (list-ref x 3) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define tuple-4-get (lambda (x) (list-ref x 4) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define tuple-5-get (lambda (x) (list-ref x 5) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define tuple-6-get (lambda (x) (list-ref x 6) ))".to_string()));

    ss.push(ChezSyntax::Raw("(define vector-string-concat
        (lambda (args)
          (write (list 'args= args)) (newline)
          
          (let f ([a 0] [n 0])
            (if (= (vector-length args) a)
                (make-string n)
                (let* ([s1 (vector-ref args a)]
                       [m (string-length s1)]
                       [s2 (f (+ a 1) (+ n m))])
                  (do ([i 0 (+ i 1)] [j n (+ j 1)])
                      ((= i m) s2)
                    (string-set! s2 j (string-ref s1 i))))))))
      ".to_string()));
    ss.push(ChezSyntax::Raw("(define-record-type TextFragmentR (fields vec utf8len))".to_string()));
    ss.push(ChezSyntax::Raw("(define-record-type TextConcatR (fields lhs rhs utf8len))".to_string()));
    ss.push(ChezSyntax::Raw("(define TextConcat make-TextConcatR)".to_string()));
    ss.push(ChezSyntax::Raw("(define TextConcat? TextConcatR?)".to_string()));
    ss.push(ChezSyntax::Raw("(define TextConcat-2-get TextConcatR-utf8len)".to_string()));
    ss.push(ChezSyntax::Raw("(define TextConcat-1-get TextConcatR-rhs)".to_string()));
    ss.push(ChezSyntax::Raw("(define TextConcat-0-get TextConcatR-lhs)".to_string()));
    ss.push(ChezSyntax::Raw("(define TextFragment-strlit (lambda (s n) (make-TextFragmentR (foster-vector-bytes-of-string s) n) ))".to_string())); 
    ss.push(ChezSyntax::Raw("(define TextFragment (lambda (v n) 
        (cond
          ((= (vector-length v) 0) (make-TextFragmentR \"\" 0))
          ((= n 0) (make-TextFragmentR \"\" 0))
          ((char? (vector-ref v 0)) (make-TextFragmentR (list->string (list-take (vector->list v) n)) n))
          ((string? (vector-ref v 0)) ; (vector-string-concat v)
            (assertion-violation #f \"TextFragment: string? not implemented\")
        )
          (else (make-TextFragmentR v n))) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define TextFragment? TextFragmentR?)".to_string()));
    ss.push(ChezSyntax::Raw("(define TextFragment-1-get TextFragmentR-utf8len)".to_string()));
    ss.push(ChezSyntax::Raw("(define TextFragment-0-get TextFragmentR-vec)".to_string()));
    ss.push(ChezSyntax::Raw("(define foster-vector-bytes-of-string (lambda (x) (list->vector (bytevector->u8-list (string->utf8 x))) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define foster-sext (lambda (x s w) 
    (cond
        ((< x 0) 
         (let ((p (bitwise-length x)))
           (bitwise-ior x (bitwise-arithmetic-shift-left (- 0 1) (- w p)))))
        ((bitwise-bit-set? x (- s 1))
         (+ (- 0 (bitwise-arithmetic-shift-left 1 s)) x))
        (else x)
        )))".to_string()));

    ss.push(ChezSyntax::Raw(format!("(define foster-shift-mask (lambda (w) (fxbit-field -1 0 (fxfirst-bit-set w)) ))")));
    ss.push(ChezSyntax::Raw(format!("(define foster-shift-masked (lambda (n w) (bitwise-and n (foster-shift-mask w)) ))")));
    
    let intsizes = vec![
        IntSizeConfig::ISC(8, "i8".to_string(), "Int8".to_string()),
        IntSizeConfig::ISC(32, "i32".to_string(), "Int32".to_string()),
        IntSizeConfig::ISC(64, "i64".to_string(), "Int64".to_string()),
        IntSizeConfig::ISC(32, "Word".to_string(), "Word".to_string()),
        IntSizeConfig::ISC(64, "WordX2".to_string(), "WordX2".to_string()),
    ];
    for configa in &intsizes {
        match configa {
            IntSizeConfig::ISC(sza, nma, nmalong) => {
                for configb in &intsizes {
                    match configb {
                        IntSizeConfig::ISC(szb, nmb, nmblong) => {
                            if sza <= szb {
                                ss.push(ChezSyntax::Raw(format!("(define sext_{}_to_{} (lambda (x) (foster-sext x {} {})))", nma, nmb, sza, szb)));
                                ss.push(ChezSyntax::Raw(format!("(define zext_{}_to_{} (lambda (x) x))", nma, nmb)));
                            }
                            
                            if sza >= szb {
                                ss.push(ChezSyntax::Raw(format!("(define trunc_{}_to_{} (lambda (x) (trunc-{} x)))", nma, nmb, nmblong)));
                            }
                        },
                    }
                }

                ss.push(ChezSyntax::Raw(format!("(define bitshl-{} (lambda (x y) (trunc-{} (bitwise-arithmetic-shift-left x (foster-shift-masked y {})))))", nmalong, nmalong, sza)));
                ss.push(ChezSyntax::Raw(format!("(define bitashr-{} (lambda (x y) (trunc-{} (foster-bitashr-core x y {}))))", nmalong, nmalong, sza)));
                ss.push(ChezSyntax::Raw(format!("(define bitlshr-{} (lambda (x y) (trunc-{} (bitwise-arithmetic-shift-right (trunc-{} x) y))))", nmalong, nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define bitand-{} (lambda (x y) (trunc-{} (bitwise-and x y))))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define bitor-{} (lambda (x y) (trunc-{} (bitwise-ior x y))))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define bitxor-{} (lambda (x y) (trunc-{} (bitwise-xor x y))))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define bitnot-{} (lambda (x) (trunc-{} (bitwise-not x))))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define ctlz-{} (lambda (x) (- {} (bitwise-length (trunc-{} x)))))", nmalong, sza, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define ctpop-{} (lambda (x) (foster-bit-count x {}) ))", nmalong, sza)));
                ss.push(ChezSyntax::Raw(format!("(define negate-{} (lambda (x) (trunc-{} (- 0 x))))", nmalong, nmalong)));

                ss.push(ChezSyntax::Raw(format!("(define =={} (lambda (x y) (= (trunc-{} x) (trunc-{} y)) ))", nmalong, nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define !={} (lambda (x y) (not (=={} x y)) ))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define <=U{} <=)", nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define >=U{}  (lambda (x y) (<=U{} y x)  ))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define <S{} (lambda (x y) (< (foster-sext x {} {}) (foster-sext y {} {})) ))",
                    nmalong, sza, sza, sza, sza)));
                ss.push(ChezSyntax::Raw(format!("(define >S{} (lambda (x y) (<S{} y x) ))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define <=S{} (lambda (x y) (<= (foster-sext x {} {}) (foster-sext y {} {})) ))",
                    nmalong, sza, sza, sza, sza)));
                ss.push(ChezSyntax::Raw(format!("(define >=S{} (lambda (x y) (<=S{} y x) ))", nmalong, nmalong)));
            
                ss.push(ChezSyntax::Raw(format!("(define <U{} (lambda (x y) (< (trunc-{} x) (trunc-{} y)) ))", nmalong, nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define >U{} (lambda (x y) (<U{} y x) ))", nmalong, nmalong)));
                
                ss.push(ChezSyntax::Raw(format!("(define +{} (lambda (x y) (trunc-{} (foster-add x y)) ))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define -{} (lambda (x y) (trunc-{} (- x y)) ))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define *{} (lambda (x y) (trunc-{} (* x y)) ))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define /{} (lambda (x y) (trunc-{} (/ x y)) ))", nmalong, nmalong)));

                ss.push(ChezSyntax::Raw(format!("(define udiv-unsafe-{} (lambda (x y) (trunc-{} (/ (trunc-{} x) (trunc-{} y))) ))", nmalong, nmalong, nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define urem-unsafe-{} (lambda (x y) (remainder (trunc-{} x) (trunc-{} y)) ))", nmalong, nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define sdiv-unsafe-{} (lambda (x y) (trunc-{} (/ x y)) ))", nmalong, nmalong)));
                ss.push(ChezSyntax::Raw(format!("(define srem-unsafe-{} (lambda (x y) (trunc-{} (remainder x y)) ))", nmalong, nmalong)));
            }
        }
    }
    ss.push(ChezSyntax::Raw("(define trunc-Int64 (lambda (x) (bitwise-and (truncate x) #xFFFFFFFFFFFFFFFF)))".to_string()));
    ss.push(ChezSyntax::Raw("(define trunc-Int32 (lambda (x) (bitwise-and (truncate x) #xFFFFFFFF)))".to_string()));
    ss.push(ChezSyntax::Raw("(define trunc-Int8 (lambda (x) (bitwise-and x #xFF)))".to_string()));
    ss.push(ChezSyntax::Raw("(define trunc-Word (lambda (x) (bitwise-and (truncate x) #xFFFFFFFF)))".to_string()));
    ss.push(ChezSyntax::Raw("(define trunc-WordX2 (lambda (x) (bitwise-and (truncate x) #xFFFFFFFFFFFFFFFF)))".to_string()));
    
    // We must manually check for fixed-width signedness of the underlying arbitrary-precision integers.
    ss.push(ChezSyntax::Raw("(define foster-bitashr-core (lambda (x y w)
        (if (bitwise-bit-set? x (1- w))
          (bitwise-arithmetic-shift-right
                (bitwise-ior (bitwise-arithmetic-shift-left -1 w) x) y)
          (bitwise-arithmetic-shift-right x y)) ))".to_string()));

    ss.push(ChezSyntax::Raw("(define foster-bit-count (lambda (x w)
        (let ((c (bitwise-bit-count x)))
            (if (negative? c) (+ w c 1) c)) ))".to_string()));

    ss.push(ChezSyntax::Raw("(define ascribe (lambda (x ty) x))".to_string()));

    ss.push(ChezSyntax::Raw("(define vector-ref-checked (lambda (v n who msg)
        (if (< n (vector-length v))  (vector-ref v n)
            (assertion-violation who msg n)) ))".to_string()));

    ss.push(ChezSyntax::Raw("(define ref box)".to_string()));
    ss.push(ChezSyntax::Raw("(define deref unbox)".to_string()));
    ss.push(ChezSyntax::Raw("(define >^ (lambda (v r) (set-box! r v)))".to_string()));

    ss.push(ChezSyntax::Raw("(define kill-entire-process (lambda (msg) (assertion-violation \"foster-prim-kill-entire-process\" msg) ))".to_string()));

    ss.push(ChezSyntax::Raw("(define opaquely_i32 (lambda (x) x))".to_string()));
    ss.push(ChezSyntax::Raw("(define opaquely_i64 (lambda (x) x))".to_string()));

    ss.push(ChezSyntax::Raw("(define force_gc_for_debugging_purposes (lambda () #f))".to_string()));

    ss.push(ChezSyntax::Raw("(define mach-array-literal vector)".to_string()));
    ss.push(ChezSyntax::Raw("(define allocDArray (lambda (n) (make-vector n)))".to_string()));
    
    ss.push(ChezSyntax::Raw("(define print_i64-to-port (lambda (x p) (write (foster-sext x 64 64) p) (newline p)))".to_string()));
    

    ss.push(ChezSyntax::Raw("(define print_i64 (lambda (x) (print_i64-to-port x (current-output-port)) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define expect_i64 (lambda (x) (print_i64-to-port x (current-error-port)) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define list-drop (lambda (xs n) (if (= n 0) xs (list-drop (cdr xs) (- n 1)) ) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define list-take (lambda (xs n) (if (= n 0) '() (cons (car xs) (list-take (cdr xs) (- n 1)) ) ) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define vector->bytevector (lambda (xs n off)
       (u8-list->bytevector (list-take (list-drop (vector->list xs) off) n)) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define prim_print_string_to (lambda (x port) (display-string x port)))".to_string()));
    ss.push(ChezSyntax::Raw("(define prim_print_bytes_to (lambda (vb n off port)
        (prim_print_string_to (utf8->string (vector->bytevector vb n off)) port)))".to_string()));
    ss.push(ChezSyntax::Raw("(define prim_print_bytevector_to (lambda (bv n off port)
     (if (and (= off 0) (= n (bytevector-length bv)))
       (prim_print_string_to (utf8->string bv) port)
       (begin (let ((x (make-bytevector n)))
         (bytevector-copy! bv off x 0 n)
         (prim_print_string_to (utf8->string x) port)
         )))))".to_string()));
    ss.push(ChezSyntax::Raw("(define prim_print_bytes_stderr (lambda (bv n off) (prim_print_bytes_to bv n off (current-error-port))))".to_string()));
    ss.push(ChezSyntax::Raw("(define prim_print_bytes_stdout (lambda (bv n off) (prim_print_bytes_to bv n off (current-output-port))))".to_string()));
    ss.push(ChezSyntax::Raw("(define expect_float_p9f64 (lambda (x) (fprintf (current-error-port) \"~,9f\" x) (newline (current-error-port))))".to_string()));
    ss.push(ChezSyntax::Raw("(define print_float_p9f64 (lambda (x) (printf \"~,9f\" x) (newline)))".to_string()));
    
    ss.push(ChezSyntax::Raw("(define vector-copy-nonoverlapping! (lambda (from fromat to toat reqlen)
       (letrec [(f (lambda (n)
                (if (< n reqlen) 
                    (begin (vector-set! to (+ toat n) (vector-ref from (+ fromat n)))
                           (f (+ n 1)))
                         )))]
            (f 0) ) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define vector-copy! (lambda (from fromat to toat reqlen)
        (let [(tmp (make-vector reqlen))]
            (vector-copy-nonoverlapping! from fromat tmp 0 reqlen)
            (vector-copy-nonoverlapping! tmp 0 to toat reqlen)
        ) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define memcpy_i8_to_at_from_at_len (lambda (to toat from fromat reqlen)
       (if (bytevector? to)
        (bytevector-copy! from fromat to toat reqlen)
        (    vector-copy! from fromat to toat reqlen) ) ))".to_string()));
    
    // Foster, for now, allows writing ASCII characters as strings,
    // so without type inference we must conservatively handle that case at runtime.
    ss.push(ChezSyntax::Raw("(define foster-add (lambda (x y)
        (let [(xn (if (string? x) (string->number x) x))
              (yn (if (string? y) (string->number y) y))]
          (+ xn yn) )))".to_string()));

    ss.push(ChezSyntax::Raw("(define prim_arrayLength vector-length)".to_string()));
    ss.push(ChezSyntax::Raw("(define subscript vector-ref)".to_string()));
    ss.push(ChezSyntax::Raw("(define subscript-static vector-ref)".to_string()));
    ss.push(ChezSyntax::Raw("(define assert-invariants (lambda (x) #t))".to_string()));

    ss.push(ChezSyntax::Raw("(define +f64 +)".to_string()));
    ss.push(ChezSyntax::Raw("(define *f64 *)".to_string()));
    ss.push(ChezSyntax::Raw("(define -f64 -)".to_string()));
    ss.push(ChezSyntax::Raw("(define nan-like (lambda (x)  (if (negative? x) -nan.0 +nan.0) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define div-f64 (lambda (x y)
        (if (zero? y) (nan-like x) (/ x y)) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define sqrt-f64 sqrt)".to_string()));
    ss.push(ChezSyntax::Raw("(define powi-f64 expt)".to_string()));
    ss.push(ChezSyntax::Raw("(define pow-f64 expt)".to_string()));
    ss.push(ChezSyntax::Raw("(define log-f64 log)".to_string()));
    ss.push(ChezSyntax::Raw("(define exp-f64 exp)".to_string()));
    ss.push(ChezSyntax::Raw("(define sin-f64 sin)".to_string()));
    ss.push(ChezSyntax::Raw("(define cos-f64 cos)".to_string()));
    ss.push(ChezSyntax::Raw("(define tan-f64 tan)".to_string()));
    ss.push(ChezSyntax::Raw("(define asin-f64 asin)".to_string()));
    ss.push(ChezSyntax::Raw("(define acos-f64 acos)".to_string()));
    ss.push(ChezSyntax::Raw("(define atan-f64 atan)".to_string()));
    ss.push(ChezSyntax::Raw("(define floor-f64 floor)".to_string()));
    ss.push(ChezSyntax::Raw("(define round-f64 round)".to_string()));
    ss.push(ChezSyntax::Raw("(define trunc-f64 truncate)".to_string()));
    ss.push(ChezSyntax::Raw("(define abs-f64 abs)".to_string()));
    ss.push(ChezSyntax::Raw("(define min-f64 min)".to_string()));
    ss.push(ChezSyntax::Raw("(define max-f64 max)".to_string()));
    ss.push(ChezSyntax::Raw("(define <f64 <)".to_string()));
    ss.push(ChezSyntax::Raw("(define >f64 >)".to_string()));
    ss.push(ChezSyntax::Raw("(define <=f64 <=)".to_string()));
    ss.push(ChezSyntax::Raw("(define >=f64 >=)".to_string()));
    ss.push(ChezSyntax::Raw("(define ==f64 =)".to_string()));
    ss.push(ChezSyntax::Raw("(define !=f64 (lambda (x y) (not (= x y))))".to_string()));

    ss.push(ChezSyntax::Raw("(define f64-as-i64 (lambda (x) (flbit-field x 0 64) ) )".to_string()));
    ss.push(ChezSyntax::Raw("(define encode-float (lambda (s e m) (inexact (* s m (expt 2 e))) ))".to_string()));
    // Note! Chez float decoding of 1.0 yields #(4503599627370496 -52 1)
    // whereas the raw bit pattern is 0x3FF0000000000000 corresponding to #(0 1023 0)
    ss.push(ChezSyntax::Raw("(define encode-float-bits (lambda (s e m)
        (let [(mf (+ 1 (* m (expt 2 -52))))]
            (inexact (* s mf (expt 2 e))) ) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define i64-as-f64 (lambda (x)
            (let* [(s (bitwise-bit-set? x 63))
                   (e (bitwise-bit-field x 52 63))
                   (m (bitwise-and x #x000FFFFFFFFFFFFF))
                   (son (if s -1 1))]
                (if (and (= e 0) (= m 0))
                    (inexact (if s -0.0 0.0))
                    (encode-float-bits son (fx- e 1023) m))
                ) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define f64-to-u64-unsafe (lambda (x) (trunc-Int64 (exact (round x))) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define f64-to-s64-unsafe (lambda (x) (exact (round x)) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define u64-to-f64-unsafe (lambda (x) (inexact (trunc-Int64 x)) ))".to_string()));
    ss.push(ChezSyntax::Raw("(define s64-to-f64-unsafe (lambda (x) (inexact x) ))".to_string()));
     
    ss.push(ChezSyntax::Raw("(define f64-to-u32-unsafe (lambda (x) (trunc-Int32 (abs (exact (round x)))) ))".to_string()));

    ss.push(ChezSyntax::Raw("(define s32-to-f64 (lambda (x) x))".to_string()));
    ss.push(ChezSyntax::Raw("(define u32-to-f64 (lambda (x) x))".to_string()));

    ss.push(ChezSyntax::Raw("(define print_float_f64   print_float_p9f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define expect_float_f64 expect_float_p9f64)".to_string()));

    // Chez Scheme does not support single-precision floats except as FFI values,
    // so we have to use doubles for everything.
    ss.push(ChezSyntax::Raw("(define i32-as-f32 (lambda (x)
    (let* [(s (bitwise-bit-set? x 31))
           (e (bitwise-bit-field x 23 31))
           (m32 (bitwise-and x #x07fffff))
           (m64 (* m32 (expt 2 29)))
           ]
           (if (and (= e 0) (= m32 0))
                    (inexact (if s -0.0 0.0))
                (if (= e 255)
                    (if (= m32 0)
                        (if s -inf.0 +inf.0)
                        (if s -nan.0 +nan.0))
                    (encode-float-bits (if s -1 1) (fx- e 127) m64)))
            )
))".to_string()));
    ss.push(ChezSyntax::Raw("(define i32-as-f64 i64-as-f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define +f32 +f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define -f32 -f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define *f32 *f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define /f32 div-f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define div-f32 div-f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define sqrt-f32 sqrt-f64)".to_string()));
    ss.push(ChezSyntax::Raw("(define f32-to-f64 (lambda (x) x))".to_string()));


    ss.push(ChezSyntax::Raw("(define __COMPILES__ (lambda (v e) v))".to_string()));
    ss.push(ChezSyntax::Raw("(define ...type... \"...type... TODO\")".to_string()));

    ss.push(ChezSyntax::Raw("\n".to_string()));

    for item in &ast.0 {
        match &item.node {
            Item::Import(Import { name, path, .. }) => {
                let name = span_str(cm, &name);
                let path = span_str(cm, &path);
                ss.push(ChezSyntax::Raw(format!(";; (import ({} {}))\n", name, path)));
            },
            Item::Decl(_name, _ty, _eq) => {
                //let name = span_str(cm, name);
                //let ty = span_str(cm, *ty);
                //let ty = "...ty...";
                //ss.push(ChezSyntax::Raw(format!("(declare {} {})", name, ty)));

                // drop type declarations
            },
            Item::Defn(name, expr, _eq) => {
                if span_str(cm, &name).eq("array-poke-i32") {
                    ss.push(ChezSyntax::Raw("(define array-poke-i32 (lambda (r i x) (vector-set! r i x)))".to_string()));
                    continue;
                }
                let csexpr: ChezSyntax = tochez_expr(&expr, cm);
                let raw_define = ChezSyntax::Raw("define".to_string());
                let chezname = ChezSyntax::Raw(tochez_name(&name, cm));
                ss.push(ChezSyntax::Call(vec![raw_define, chezname, csexpr]));
            },
            Item::TypeCase(_tyformal, _tyformals, datactors) => {
                for ctor in datactors {
                    match ctor {
                        DataCtor::DataCtor(name, tys) => {
                            let ctorname = span_str(cm, &name);
                            // Ensure that the underlying record type name is distinct from
                            // the constructor name.
                            let recordname = format!("^{}", ctorname);
                            let mut ctorfields = Vec::new();
                            ctorfields.push(ChezSyntax::Raw("fields".to_string()));
                            for (n, _) in tys.iter().enumerate() {
                                let immut = ChezSyntax::Raw("immutable".to_string());
                                let fieldname = ChezSyntax::Raw(format!("{}-{}", ctorname, n));
                                let accessor = ChezSyntax::Raw(format!("{}-{}-get", ctorname, n));
                                ctorfields.push(ChezSyntax::Call(vec![immut, fieldname, accessor]));
                            }
                            let nullary = ctorfields.len() == 1;
                            let fields = ChezSyntax::Call(ctorfields);
                            ss.push(ChezSyntax::Call(vec![ChezSyntax::Raw("define-record-type".to_string()), ChezSyntax::Raw(recordname.clone()), fields]));

                            if nullary {
                                // Nullary constructors are treated as constants rather than functions.
                                ss.push(ChezSyntax::Call(vec![ChezSyntax::Raw(format!("define {} (make-{})", ctorname, recordname))]));
                            } else {
                                ss.push(ChezSyntax::Call(vec![ChezSyntax::Raw(format!("define {} make-{}", ctorname, recordname))]));
                            }
                            
                            ss.push(ChezSyntax::Call(vec![ChezSyntax::Raw(format!("define {}? {}?", ctorname, recordname))]));
                        }
                    }
                }
            },
            Item::Effect(_tyformal, _tyformals, _effectctors) => {
                //let tyformal = span_str(cm, *tyformal);
                let tyformal = "...tyformal...";
                //let tyformals = span_str(cm, *tyformals);
                let tyformals = "...tyformals...";
                //let effectctors = span_str(cm, *effectctors);
                let effectctors = "...effectctors...";
                ss.push(ChezSyntax::Raw(format!("(effect {} {} {})", tyformal, tyformals, effectctors)));
            },
            Item::ForeignImport(name, _ty, _eq) => {
                let name = span_str(cm, &name);
                //let ty = span_str(cm, *ty);
                let ty = "...ty...";
                ss.push(ChezSyntax::Raw(format!("; (foreign-import {} {})", name, ty)));
            },
            Item::ForeignType(_tyformal) => {
                //let tyformal = span_str(cm, *tyformal);
                let tyformal = "...tyformal...";
                ss.push(ChezSyntax::Raw(format!("(foreign-type {})", tyformal)));
            },
            Item::Unexpected(_) => {
                ss.push(ChezSyntax::Raw(format!("(unexpected)")));
            },
        }
    }

    ss.push(ChezSyntax::Raw("(main)\n".to_string()));

    ChezSyntax::TopForms(ss)
}