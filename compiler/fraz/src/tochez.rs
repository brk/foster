use std::vec;

use crate::syn::*;
use codemap::Spanned;
use codemap::Span;
use codemap::CodeMap;

#[derive(Debug,PartialEq,Hash)]
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

fn tochez_stmts(stmts: &Stmts, cm: &CodeMap) -> ChezSyntax {
    ChezSyntax::Raw("...stmts...".to_string())
}

fn tochez_type(typ: &Type, cm: &CodeMap) -> ChezSyntax {
    ChezSyntax::Raw("...type...".to_string())
}

fn tochez_suffix(suffix: &Suffix, expr: ChezSyntax, cm: &CodeMap) -> ChezSyntax {
    match suffix {
        Suffix::Caret(_) => {
            ChezSyntax::Call(vec![ChezSyntax::Raw("deref".to_string()), expr])
        },
        Suffix::DotSqBrackets(_, _) => {
            ChezSyntax::Raw("...dotsqbrackets...".to_string())
        },
        Suffix::RawSqBrackets(_, _) => {
            ChezSyntax::Raw("...rawsqbrackets...".to_string())
        },
        Suffix::TypeApp(_, _) => {
            ChezSyntax::Raw("...typeapp...".to_string())
        },
        Suffix::Bang(_) => {
            ChezSyntax::Call(vec![expr])
        },
        Suffix::DotIdent(_, _) => {
            ChezSyntax::Raw("...dotident...".to_string())
        },
    }
}

fn span_str(cm: &CodeMap, span: &Span) -> String {
    cm.find_file(span.low()).source_slice(*span).to_string()
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
            ChezSyntax::Call(vec![ChezSyntax::Raw("the".to_string()), expr, ty])
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
        Expr_::Handler(expr, effmatches, _final) => {
            ChezSyntax::Raw("...handler...".to_string())
        },
        Expr_::ValAbs(tyformals, formals, stmts) => {
            ChezSyntax::Raw("...valabs...".to_string())
        },
        Expr_::LValue(expr, suffixes) => {
            let mut expr = tochez_expr(&expr, cm);
            for suffix in suffixes {
                expr = tochez_suffix(&suffix, expr, cm);
            }
            expr
        },
        Expr_::Prim(tok, exprs) => {
            let s = span_str(cm, tok);
            let mut forms = Vec::new();
            forms.push(ChezSyntax::Raw("prim".to_string()));
            forms.push(ChezSyntax::Raw(s));
            for e in exprs {
                forms.push(tochez_expr(&e, cm));
            }
            ChezSyntax::Call(forms)
        },
        Expr_::Chain(expr, chain) => {
            let mut expr = tochez_expr(&expr, cm);
            for (binop, rhs) in chain {
                let mut forms = Vec::new();
                forms.push(ChezSyntax::Raw("chain".to_string()));
                forms.push(expr);
                forms.push(tochez_expr(&rhs, cm));
                expr = ChezSyntax::Call(forms);
            }
            expr
        },
        Expr_::Case(expr, patmatches) => {
            /*
            let expr = tochez_expr(&expr, cm);
            let mut forms = Vec::new();
            forms.push(ChezSyntax::Raw("case".to_string()));
            forms.push(expr);
            for patmatch in patmatches {
                forms.push(tochez_patmatch(&patmatch, cm));
            }
            ChezSyntax::Call(forms)
            */
            ChezSyntax::Raw("...case...".to_string())
        },
    }
}

pub fn tochez_transunit(ast: &TransUnit, cm: &CodeMap) -> ChezSyntax {
    let mut ss = vec![];
    for item in &ast.0 {
        match item {
            Spanned { span, node: Item::Import(Import { name, path, .. }) } => {
                let name = span_str(cm, name);
                let path = span_str(cm, path);
                ss.push(ChezSyntax::Raw(format!("(import ({} {}))", name, path)));
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
                //let tyformal = span_str(cm, *tyformal);
                //let tyformals = span_str(cm, *tyformals);
                let tyformal = "...tyformal...";
                let tyformals = "...tyformals...";
                //let datactors = span_str(cm, *datactors);
                let datactors = "...datactors...";
                ss.push(ChezSyntax::Raw(format!("(typecase {} {} {})", tyformal, tyformals, datactors)));
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