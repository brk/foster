use std::vec;

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

pub fn emit(cs: &ChezSyntax) -> () {
    match cs {
        ChezSyntax::Raw(s) => print!("{}", s),
        ChezSyntax::Call(cs) => {
            print!("(");
            for c in cs {
                emit(c);
                print!(" ");
            }
            print!(")\n");
        },
        ChezSyntax::TopForms(cs) => {
            for c in cs {
                emit(c);
                println!("");
            }
        }
    }
}

fn tochez_lit(lit: &Lit, cm: &CodeMap) -> ChezSyntax {
    match lit {
        Lit::Num(tok) => {
            let s = span_str(cm, tok);
            if s.contains('.') {
                ChezSyntax::Raw(s)
            } else {
                let d = crate::syn::parse_int(&s);
                ChezSyntax::Raw(format!("{}", crate::syn::recompose(&d)))
            }
        },
        Lit::Str(tok) => {
            let s = span_str(cm, tok);
            ChezSyntax::Raw(s)
        },
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
        Stmt::ExprBind(lhs, rhs) => {
            let lhs = tochez_expr(lhs, cm);
            let rhs = tochez_expr(rhs, cm);
            tochez_let_1(lhs, rhs, cont)
        },
        Stmt::PatBind(lhs, rhs) => {
            let lhs = tochez_patlhs(lhs, cm);
            let rhs = tochez_expr(rhs, cm);
            tochez_let_1(lhs, rhs, cont)
        },
    
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

fn tochez_type(typ: &Type, cm: &CodeMap) -> ChezSyntax {
    ChezSyntax::Raw("...type...".to_string())
}

fn tochez_suffix(suffix: &Suffix, expr: ChezSyntax, cm: &CodeMap) -> ChezSyntax {
    match suffix {
        Suffix::Caret(_) => {
            ChezSyntax::Call(vec![ChezSyntax::Raw("deref".to_string()), expr])
        },
        Suffix::DotSqBrackets(e_k, _) => {
            ChezSyntax::Call(vec![ChezSyntax::Raw("vector-ref".to_string()), expr, tochez_expr(e_k, cm)])
        },
        Suffix::RawSqBrackets(e_k, _) => {
            ChezSyntax::Call(vec![ChezSyntax::Raw("vector-ref".to_string()), expr, tochez_expr(e_k, cm)])
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
        Formal::Formal(name, _ty) => span_str(cm, name),
    }
}

fn prec(cm: &CodeMap, binop: Span) -> i32 {
    let s = span_ref(cm, &binop);
    match s.chars().nth(0).unwrap() {
        '|' => 100,
        _ => 10
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
    Call(Vec<Expr>),
    NonCall(Expr),
}

fn pipe_rhs(e: Expr) -> PipeRhs {
    match &*e.0.node {
        Expr_::Call(args) => {
            PipeRhs::Call(args.clone())
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
            PipeRhs::Call(mut args) => {
                // eprintln!("pipe-call lhs sexpr: {:?}", tochez_expr(&lhs, cm));
                // for a in args.iter_mut() {
                //     eprintln!("     pipe-call arg sexpr: {:?}", tochez_expr(&a, cm));
                // }

                args.insert(1, lhs);
                return Expr(Spanned { node: Box::new(Expr_::Call(args)), span: newspan });
            },
            PipeRhs::NonCall(e) => {
                // eprintln!("pipe-noncall lhs: {:?}", span_ref(cm, &lhs.0.span));
                let args = vec![e, lhs];
                return Expr(Spanned { node: Box::new(Expr_::Call(args)), span: newspan });
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
    let n = Expr_::Call(vec![binopvar, lhs, rhs]);
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
                if prec(cm, binoptok) <= prec(cm, topop) && leftassoc(cm, binoptok) {
                    // Spill decreases length of exprq by 1, matching pop of opq.
                    // eprintln!("spill because top had higher precedence and binop was leftassoc");
                    spill(cm, topop, &mut exprq);
                } else {
                    // eprintln!("restore {} then push {}", span_ref(cm, &topop), span_ref(cm, &binoptok));
                    // Previous operator binds tighter
                    opq.push(topop);
                    opq.push(binoptok);

                    // for ex in exprq.iter() {
                    //     eprintln!("     exprq sexpr: {:?}", tochez_expr(ex, cm));
                    // }

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
    assert!(exprq.len() == opq.len() + 1);
    while let Some(topop) = opq.pop() {
        // eprintln!("spill to consolidate remaining ops");
        spill(cm, topop, &mut exprq);
    }
    assert!(exprq.len() == 1);
    exprq.pop().unwrap()
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
fn tochez_scrut_patatom(patatom: &PatAtom, mc: &mut MatchContext, cm: &CodeMap) -> Option<ChezSyntax> {
    match patatom {
        PatAtom::Ident(name) => {
            let accessor = tochez_scrut_accessors(&mc);
            mc.binders.push(ChezSyntax::Raw(span_str(cm, name)));
            mc.boundvals.push(accessor);
            None
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
            } else {
                let mut forms = Vec::new();
                forms.push(ChezSyntax::Raw("and".to_string()));
                for (n, pat) in pats.iter().enumerate() {
                    let residual = tochez_scrut_pat(pat, &None, mc, cm);
                    forms.push(residual);
                }
                Some(ChezSyntax::Call(forms))
            }
        },
    }
}

fn tochez_scrut_patside(pat: &Patside, mc: &mut MatchContext, cm: &CodeMap) -> ChezSyntax {
    match pat {
        Patside::Dctor(name, pats) => {
            let mut andforms = Vec::new();
            andforms.push(ChezSyntax::Raw("and".to_string()));
            andforms.push(ChezSyntax::Call(vec![ChezSyntax::Raw(format!("{}?", span_str(cm, name))),
                                                         tochez_scrut_accessors(mc)]));
            
            for (n, pat) in pats.iter().enumerate() {
                mc.accessors.push(ChezSyntax::Raw(format!("{}-{}-get", span_str(cm, name), n)));
                let residual = tochez_scrut_patatom(pat, mc, cm);
                mc.accessors.pop();
                match residual {
                    None => (),
                    Some(form) => andforms.push(form),
                }
            }
            ChezSyntax::Call(andforms)
        },
        Patside::Atom(patatom) => {
            tochez_scrut_patatom(patatom, mc, cm).unwrap_or(ChezSyntax::Raw("#t".to_string()))
        },
    }
}

fn tochez_scrut_pat(pat: &Pat, guard: &Option<Expr>, mc: &mut MatchContext, cm: &CodeMap) -> ChezSyntax {
    match pat {
        Pat::PatOf(lhs, rhs) => {
            // p1 | p2 | p3   if guard
            
            /*
            let mut forms = Vec::new();
            forms.push(tochez_patside(lhs, cm));
            for side in rhs {
                forms.push(tochez_patside(side, cm));
            }
            ChezSyntax::Call(forms)
             */
            tochez_scrut_patside(lhs, mc, cm)
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

fn tochez_scrut_cont(pm: &PatMatch, cont: ChezSyntax, cm: &CodeMap) -> ChezSyntax {
    let mut mc = MatchContext { accessors: Vec::new(), binders: Vec::new(), boundvals: Vec::new() };

    mc.accessors.push(ChezSyntax::Raw("_scrutinee".to_string()));

    match pm {
        PatMatch::PatMatch(pat, guard, stmts) => {
            let body = tochez_stmts(stmts, cm);
            let guards = tochez_scrut_pat(pat, guard, &mut mc, cm);
            // Without guard:
            // (if (...guards...) (let-values ((binders) (boundvals)) body) cont)
            match guard {
                None => {
                    let mut forms = Vec::new();
                    forms.push(ChezSyntax::Raw("if".to_string()));
                    forms.push(guards);
                    forms.push(tochez_let_values(mc, body));
                    forms.push(cont);
                    ChezSyntax::Call(forms)
                },
                Some(guard) => {
                    ChezSyntax::Raw("...guard!!...".to_string())
                },
            }
            // With guard:
            // (if (...guards...) (let-values ((binders) (boundvals)) (if guard body cont)) cont)
            // Except we don't want to duplicate cont, so we let-bind the cont expression and call its binder.
        },
    }
}

fn tochez_expr(ast: &Expr, cm: &CodeMap) -> ChezSyntax {
    match &*ast.0.node {
        Expr_::Lit(Lit::Num(tok)) => {
            let s = span_str(cm, tok);
            if s.contains('.') {
                ChezSyntax::Raw(s)
            } else {
                let d = crate::syn::parse_int(&s);
                ChezSyntax::Raw(format!("{}", crate::syn::recompose(&d)))
            }
        },
        Expr_::Lit(Lit::Str(tok)) => {
            let s = span_str(cm, tok);
            ChezSyntax::Raw(s)
        },
        Expr_::Var(name) => {
            let s = span_str(cm, name);
            ChezSyntax::Raw(s)
        },
        Expr_::Call(args) => {
            if args.len() == 1 {
                // In foster syntax, Call[e] == e, not (e); the equivalent to (e) is Call[LValue[e, !]]
                tochez_expr(&args[0], cm)
            } else {
                let args = args.iter().map(|a| tochez_expr(a, cm)).collect();
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
        Expr_::Handler(expr, _effmatches, _final) => {
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
            forms.push(ChezSyntax::Raw(s.to_string()));
            for e in exprs {
                forms.push(tochez_expr(&e, cm));
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

            let mut form = ChezSyntax::Raw("\"case match failure\"".to_string());

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

fn tyformal_name(cm: &CodeMap, tyformal: &Tyformal) -> String {
    match tyformal {
        Tyformal::Tyformal(name, _) => span_str(cm, name),
        Tyformal::TyformalParens(name, _, _) => span_str(cm, name),
    }
}

pub fn tochez_transunit(ast: &TransUnit, cm: &CodeMap) -> ChezSyntax {
    let mut ss = vec![];

    ss.push(ChezSyntax::Raw("(import (rnrs arithmetic bitwise))".to_string()));
    ss.push(ChezSyntax::Raw("(import (rnrs io simple))".to_string()));
    ss.push(ChezSyntax::Raw("\n".to_string()));
    ss.push(ChezSyntax::Raw("(define print_i64 (lambda (x) (write x) (newline)))".to_string()));
    ss.push(ChezSyntax::Raw("(define sext_i32_to_i64 (lambda (x) x))".to_string()));
    ss.push(ChezSyntax::Raw("\n".to_string()));

    for item in &ast.0 {
        match item {
            Spanned { span, node: Item::Import(Import { name, path, .. }) } => {
                let name = span_str(cm, name);
                let path = span_str(cm, path);
                ss.push(ChezSyntax::Raw(format!(";; (import ({} {}))\n", name, path)));
            },
            Spanned { span, node: Item::Decl(name, ty, _eq) } => {
                //let name = span_str(cm, name);
                //let ty = span_str(cm, *ty);
                //let ty = "...ty...";
                //ss.push(ChezSyntax::Raw(format!("(declare {} {})", name, ty)));

                // drop type declarations
            },
            Spanned { span, node: Item::Defn(name, expr, _eq) } => {
                let name = span_str(cm, name);
                let csexpr: ChezSyntax = tochez_expr(expr, cm);
                let raw_define = ChezSyntax::Raw("define".to_string());
                let origsrc = span_str(cm, span);
                /*
                ss.push(ChezSyntax::Raw(origsrc));
                ss.push(ChezSyntax::Raw(format!("{:?}", expr)));
                ss.push(ChezSyntax::Raw(format!("{:?}", csexpr)));
                */
                ss.push(ChezSyntax::Call(vec![raw_define, ChezSyntax::Raw(name), csexpr]));
            },
            Spanned { span, node: Item::TypeCase(tyformal, tyformals, datactors) } => {
                for ctor in datactors {
                    match ctor {
                        DataCtor::DataCtor(name, tys) => {
                            let ctorname = span_str(cm, name);
                            let mut ctorfields = Vec::new();
                            ctorfields.push(ChezSyntax::Raw("fields".to_string()));
                            for (n, _) in tys.iter().enumerate() {
                                let immut = ChezSyntax::Raw("immutable".to_string());
                                let fieldname = ChezSyntax::Raw(format!("{}-{}", ctorname, n));
                                let accessor = ChezSyntax::Raw(format!("{}-{}-get", ctorname, n));
                                ctorfields.push(ChezSyntax::Call(vec![immut, fieldname, accessor]));
                            }
                            let fields = ChezSyntax::Call(ctorfields);
                            ss.push(ChezSyntax::Call(vec![ChezSyntax::Raw("define-record-type".to_string()), ChezSyntax::Raw(ctorname.clone()), fields]));

                            ss.push(ChezSyntax::Call(vec![ChezSyntax::Raw(format!("define {} make-{}", ctorname, ctorname))]));
                        }
                    }
                }
            },
            Spanned { span, node: Item::Effect(tyformal, tyformals, effectctors) } => {
                //let tyformal = span_str(cm, *tyformal);
                let tyformal = "...tyformal...";
                //let tyformals = span_str(cm, *tyformals);
                let tyformals = "...tyformals...";
                //let effectctors = span_str(cm, *effectctors);
                let effectctors = "...effectctors...";
                ss.push(ChezSyntax::Raw(format!("(effect {} {} {})", tyformal, tyformals, effectctors)));
            },
            Spanned { span, node: Item::ForeignImport(name, ty, _eq) } => {
                let name = span_str(cm, name);
                //let ty = span_str(cm, *ty);
                let ty = "...ty...";
                ss.push(ChezSyntax::Raw(format!("(foreign-import {} {})", name, ty)));
            },
            Spanned { span, node: Item::ForeignType(tyformal) } => {
                //let tyformal = span_str(cm, *tyformal);
                let tyformal = "...tyformal...";
                ss.push(ChezSyntax::Raw(format!("(foreign-type {})", tyformal)));
            },
            Spanned { span, node: Item::Unexpected(_) } => {
                ss.push(ChezSyntax::Raw(format!("(unexpected)")));
            },
        }
    }
    ChezSyntax::TopForms(ss)
}