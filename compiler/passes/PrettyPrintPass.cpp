// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/PrettyPrintPass.h"
#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h" // for reconstructing explicit parens

////////////////////////////////////////////////////////////////////

class ScopedParens {
  PrettyPrintPass* p;
  bool enable;
public:
  ScopedParens(PrettyPrintPass* p, bool enable = true)
    : p(p), enable(enable) {
    if (enable) {
      p->scan(PrettyPrintPass::PPToken("("));
    }
  }
  
  ~ScopedParens() {
    if (enable) {
      p->scan(PrettyPrintPass::PPToken(")"));
    }
  }
};

// Note: to get explicit parenthesization, recurse() should be called
// instead of ast->accept(); in pretty printing bodies.
inline void recurse(PrettyPrintPass* p, ExprAST* ast, bool wrapInParens) {
  if (!ast) {
    p->scan(PrettyPrintPass::PPToken("<nil>"));
  } else {
    ScopedParens sp(p, wrapInParens);
    ast->accept(p);
  }
}

bool isAtom(ExprAST* ast) {
  if (dynamic_cast<BoolAST*>(ast)) return true;
  if (dynamic_cast<IntAST*>(ast)) return true;
  if (dynamic_cast<VariableAST*>(ast)) return true;
  if (dynamic_cast<NilExprAST*>(ast)) return true;
  return false;
}

bool isDelimited(ExprAST* ast) {
  if (isAtom(ast)) return true;
  if (dynamic_cast<DerefExprAST*>(ast)) return true;
  return false;
}

bool needsParens(BinaryOpExprAST* ast, ExprAST* child) {
  return !isDelimited(child);
}

////////////////////////////////////////////////////////////////////

void PrettyPrintPass::emit(ExprAST* ast, bool forceParens) {
  recurse(this, ast, forceParens || foster::wasExplicitlyParenthesized(ast));
}

////////////////////////////////////////////////////////////////////

void PrettyPrintPass::visit(BoolAST* ast) {
  scan(PPToken( (ast->boolValue) ? "true" : "false" ));
}

void PrettyPrintPass::visit(IntAST* ast) {
  scan(PPToken(ast->getOriginalText()));
}

// name (: type)
void PrettyPrintPass::visit(VariableAST* ast) {
  scan(tBlockOpen);
  scan(PPToken(ast->name));
  if (this->printVarTypes) {
    scan(PPToken(":"));
    /*if (ast->tyExpr) {
      ast->tyExpr->accept(this);
    } else*/ if (ast->type) {
      // TODO this isn't kosher for round-tripping, need to write a
      // pretty-printer for types...
      scan(PPToken(str(ast->type->getLLVMType())));
    }
  }
  scan(tBlockClose);
}

void PrettyPrintPass::visit(UnaryOpExprAST* ast) {
  scan(PPToken(ast->op));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}

// $0 op $1
void PrettyPrintPass::visit(BinaryOpExprAST* ast) {
  scan(tBlockOpen);
  {
    emit(ast->parts[0], needsParens(ast, ast->parts[0]));
    scan(PPToken(" "));
    scan(PPToken(ast->op));
    scan(PPToken(" "));
    emit(ast->parts[1], needsParens(ast, ast->parts[1]));
  }
  scan(tBlockClose);
}

// fn Name (inArgs to outArgs)
void PrettyPrintPass::visit(PrototypeAST* ast) {
  scan(tBlockOpen);
  //scan(tBlockOpen);
  scan(PPToken("fn"));
  scan(PPToken(" "));
  scan(PPToken(ast->name));
  scan(PPToken(" "));
  //scan(tBlockClose);
  //scan(tBlockOpen);
  scan(PPToken("("));
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    scan(PPToken(" "));
    this->printVarTypes = true;
    emit(ast->inArgs[i]);
    this->printVarTypes = false;
  }
  if (ast->resultTy != NULL) {
    scan(PPToken(" to "));
    scan(PPToken(str(ast->resultTy)));
  }
  scan(PPToken(" "));
  scan(PPToken(")"));
  //scan(tBlockClose);
  scan(tBlockClose);
}

// fnProto fnBody
void PrettyPrintPass::visit(FnAST* ast) {
  bool isTopLevelFn = ast->parent == NULL;
  if (isTopLevelFn) { scan(tNewline); }

  emit(ast->proto);

  if (!isTopLevelFn) { scan(tNewline); }

  if (ast->body) {
    emit(ast->body);

    if (isTopLevelFn) { scan(tNewline); }
  }
}

void PrettyPrintPass::visit(ModuleAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    emit(ast->parts[i]);
    scan(tNewline);
  }
}

void PrettyPrintPass::visit(ClosureAST* ast) {
  scan(tBlockOpen);
  scan(PPToken("<closure "));
  if (ast->fn) {
    scan(PPToken(str(ast->fn->proto->type)));
  }
  scan(PPToken(">"));
  scan(tBlockClose);
}

// if $0 { $1 } else { $2 }
void PrettyPrintPass::visit(IfExprAST* ast) {
  //scan(tBlockOpen);
  scan(PPToken("if "));
  emit(ast->testExpr);
  //scan(tBlockClose);

  scan(PPToken(" "));
  scan(tOptNewline);

  emit(ast->thenExpr);

  scan(PPToken(" else "));
  scan(tOptNewline);

  emit(ast->elseExpr);
}

// for $0 in $1 to $2 do $3
void PrettyPrintPass::visit(ForRangeExprAST* ast) {
  //scan(tBlockOpen);
  scan(PPToken("for "));
  scan(PPToken(ast->var->name));
  //scan(tBlockClose);

  scan(PPToken(" in "));
  emit(ast->startExpr);
  scan(PPToken(" to "));
  emit(ast->endExpr);

  if (ast->incrExpr) {
	scan(PPToken(" by "));
	emit(ast->incrExpr);
  }

  scan(PPToken(" do "));
  scan(tOptNewline);

  emit(ast->bodyExpr);
}

void PrettyPrintPass::visit(NilExprAST* ast) {
  scan(PPToken("nil"));
}

void PrettyPrintPass::visit(RefExprAST* ast) {
  if (ast->isNullable) {
	scan(PPToken("?ref "));
  } else {
	scan(PPToken("ref "));
  }

  emit(ast->parts[0]);
}

void PrettyPrintPass::visit(DerefExprAST* ast) {
  scan(PPToken("deref("));
  emit(ast->parts[0]);
  scan(PPToken(")"));
}

void PrettyPrintPass::visit(AssignExprAST* ast) {
  scan(PPToken("set "));
  emit(ast->parts[0]);
  scan(PPToken(" = "));
  emit(ast->parts[1]);
}

// $0 [ $1 ]
void PrettyPrintPass::visit(SubscriptAST* ast) {
  //scan(tBlockOpen);
  emit(ast->parts[0]);

  scan(PPToken("["));
  emit(ast->parts[1]);
  scan(PPToken("]"));
  //scan(tBlockClose);
}

// { $0 ; $1 ; ... ; $n }
void PrettyPrintPass::visit(SeqAST* ast) {
  scan(tBlockOpen);
  scan(tIndent);
  FnAST* followingFn = dynamic_cast<FnAST*>(ast->parent);
  if (followingFn) {
    scan(PPToken(" {"));
    scan(tNewline);
  } else {
    scan(PPToken("{ "));
  }

  for (size_t i = 0; i < ast->parts.size(); ++i) {
    scan(tBlockOpen);
    emit(ast->parts[i]);
    scan(tBlockClose);

    if (i != ast->parts.size() - 1) {
      if (CallAST* wasCall = dynamic_cast<CallAST*>(ast->parts[i])) {
        scan(tNewline);
      } else {
        scan(PPToken("; "));
      }
    }
  }

  scan(tDedent);

  if (followingFn) {
    scan(tNewline);
    scan(PPToken("}"));
  } else {
    scan(PPToken(" }"));
  }

  scan(tBlockClose);
}

// $0 ( $1, $2, ... , $n )
void PrettyPrintPass::visit(CallAST* ast) {
  scan(tBlockOpen);
  scan(tBlockOpen);
  emit(ast->parts[0]);
  scan(tBlockClose);
  scan(tBlockOpen);
  scan(PPToken("("));

  if (ast->parts.size() > 1) {
    scan(tIndent);
  }

  bool first = true;
  for (size_t i = 1; i < ast->parts.size(); ++i) {
    if (!first) {
      scan(PPToken(","));
      scan(PPToken(" "));
    }
    first = false;

    if (i == ast->parts.size() -1) {
      // dedent "early" because a dedent followed directly
      // by a close-paren doesn't do much for us...
      scan(tDedent);
    }

    scan(tBlockOpen);
    emit(ast->parts[i]);
    scan(tBlockClose);
  }

  scan(PPToken(")"));
  scan(tBlockClose);
  scan(tBlockClose);
}
// array $0
void PrettyPrintPass::visit(ArrayExprAST* ast) {
  scan(PPToken("array"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}

// tuple $0
void PrettyPrintPass::visit(TupleExprAST* ast) {
  scan(PPToken("tuple"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}


// simd-vector $0
void PrettyPrintPass::visit(SimdVectorAST* ast) {
  scan(PPToken("simd-vector"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}

// __COMPILES__ $0
void PrettyPrintPass::visit(BuiltinCompilesExprAST* ast) {
  //scan(tBlockClose);
  scan(PPToken("__COMPILES__"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
  //scan(tBlockClose);
}

