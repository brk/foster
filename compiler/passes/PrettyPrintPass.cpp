// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/PrettyPrintPass.h"
#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h" // for reconstructing explicit parens

#include <sstream>

#include "base/PughSinofskyPrettyPrinter.h"
#include "parse/ExprASTVisitor.h"

struct PrettyPrintPass : public ExprASTVisitor {
  #include "parse/ExprASTVisitor.decls.inc.h"
  
  // This can be used in lieu of ast->accept(ppp)
  // to ensure proper outer parens,
  // mainly useful for unit tests.
  void emit(ExprAST*, bool forceOuterParens = false);
  
  virtual void visitChildren(ExprAST* ast) {
   // Only visit children manually!
  }
  
  typedef foster::PughSinofskyPrettyPrinter PrettyPrinter;
  
private:
  PrettyPrinter pp;
  // Controls whether type ascriptions on variable names are printed.
  // Used to print ascriptions on fn formals but not let bindings.
  bool printVarTypes;
  bool printSignaturesOnly;
  
public:
  PrettyPrintPass(llvm::raw_ostream& out, int width, int indent_width)
    : pp(out, width, indent_width),
      printVarTypes(false),
      printSignaturesOnly(false) {}

  void setPrintSignaturesOnly(bool newval) { printSignaturesOnly = newval; }
  void scan(const PrettyPrinter::PPToken& token) { pp.scan(token); }
  
  ~PrettyPrintPass() {}
  
  friend class ScopedBlock;
  friend class ScopedIndent;
};

namespace foster {
  void prettyPrintExpr(ExprAST* t,
		 llvm::raw_ostream& out, int width, int indent_width,
                 bool printSignaturesOnly) {
    PrettyPrintPass pp(out, width, indent_width);
    pp.setPrintSignaturesOnly(printSignaturesOnly);
    pp.emit(t);
  }
}


////////////////////////////////////////////////////////////////////

typedef PrettyPrintPass::PrettyPrinter::PPToken PPToken;

class ScopedParens {
  PrettyPrintPass* p;
  bool enable;
public:
  ScopedParens(PrettyPrintPass* p, bool enable = true)
    : p(p), enable(enable) {
    if (enable) {
      p->scan(PPToken("("));
    }
  }
  
  ~ScopedParens() {
    if (enable) {
      p->scan(PPToken(")"));
    }
  }
};

class ScopedBlock {
  PrettyPrintPass* p;
public:
  ScopedBlock(PrettyPrintPass* p) : p(p) {
    p->scan(p->pp.tBlockOpen);
  }
  
  ~ScopedBlock() {
    p->scan(p->pp.tBlockClose);
  }
};


class ScopedIndent {
  PrettyPrintPass* p;
public:
  ScopedIndent(PrettyPrintPass* p) : p(p) {
    p->scan(p->pp.tIndent);
  }
  
  ~ScopedIndent() {
    p->scan(p->pp.tDedent);
  }
};

// Note: to get explicit parenthesization, recurse() should be called
// instead of ast->accept(); in pretty printing bodies.
inline void recurse(PrettyPrintPass* p, ExprAST* ast, bool wrapInParens) {
  if (!ast) {
    p->scan(PPToken("<nil>"));
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
  ScopedBlock sb(this);
  scan(PPToken(ast->name));
  //std::stringstream ss; ss << "@" << ast; scan(PPToken(ss.str()));
  if (this->printVarTypes) {
    scan(PPToken(":"));
    if (ast->type) {
      // TODO eventually this should scan tokens, not a full string.
      scan(PPToken(str(ast->type)));
    }
  }
}

// op arg
void PrettyPrintPass::visit(UnaryOpExprAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken(ast->op));
  scan(pp.tOptNewline);
  scan(PPToken(" "));
  emit(ast->parts[0]);
}

// $0 op $1
void PrettyPrintPass::visit(BinaryOpExprAST* ast) {
  ScopedBlock sb(this);
  
  emit(ast->parts[0], needsParens(ast, ast->parts[0]));
  scan(PPToken(" "));
  scan(PPToken(ast->op));
  scan(pp.tOptNewline);
  scan(PPToken(" "));
  emit(ast->parts[1], needsParens(ast, ast->parts[1]));
}

// fn Name (inArgs to outArgs)
void PrettyPrintPass::visit(PrototypeAST* ast) {
  ScopedBlock sb(this);
  { ScopedBlock sb(this);
  scan(PPToken("fn"));
  scan(PPToken(" "));
  scan(PPToken(ast->name));
  }
  
  { ScopedBlock sb(this);
  scan(PPToken(" "));
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
  } // block for params
}

// fnProto fnBody
void PrettyPrintPass::visit(FnAST* ast) {
  bool isTopLevelFn = ast->parent == NULL;
  if (isTopLevelFn) { scan(pp.tNewline); }

  emit(ast->getProto());

  if (!this->printSignaturesOnly) {
    if (!isTopLevelFn) { scan(pp.tNewline); }

    if (ast->getBody()) {
      emit(ast->getBody());
    }
  }
}

void PrettyPrintPass::visit(NamedTypeDeclAST* ast) {
  scan(PPToken("type = "));
  ScopedBlock sb(this);
  scan(PPToken(str(ast->type))); // TODO avoid str(type)
  scan(pp.tNewline);
}

void PrettyPrintPass::visit(ModuleAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    emit(ast->parts[i]);
    scan(pp.tNewline);
  }
}

void PrettyPrintPass::visit(ClosureAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("<closure "));
  if (ast->fn) {
    emit(ast->fn);
  }
  scan(PPToken(">"));
}

// if $0 then $1 else $2
void PrettyPrintPass::visit(IfExprAST* ast) {
  ScopedBlock sb(this);
  
  { ScopedBlock sb(this);
  scan(PPToken("if "));
  emit(ast->getTestExpr());
  }
  
  scan(pp.tConnNewline);
  
  { ScopedBlock sb(this);
  scan(PPToken(" then "));
  emit(ast->getThenExpr());
  }

  scan(pp.tConnNewline);
  
  { ScopedBlock sb(this);
  scan(PPToken(" else "));
  emit(ast->getElseExpr());
  }
}

// for $0 in $1 to $2 do $3
void PrettyPrintPass::visit(ForRangeExprAST* ast) {
  { ScopedBlock sb(this);
    scan(PPToken("for "));
    scan(PPToken(ast->var->name));
  
    scan(PPToken(" in "));
    emit(ast->getStartExpr());
    scan(PPToken(" to "));
    emit(ast->getEndExpr());
  
    if (ast->hadExplicitIncrExpr()) {
      scan(PPToken(" by "));
      emit(ast->getIncrExpr());
    }
    
    scan(PPToken(" do "));
  }
  
  scan(pp.tOptNewline);
  
  emit(ast->getBodyExpr());
}

void PrettyPrintPass::visit(NilExprAST* ast) {
  scan(PPToken("nil"));
}

void PrettyPrintPass::visit(RefExprAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("ref "));
  emit(ast->parts[0]);
}

void PrettyPrintPass::visit(DerefExprAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("deref("));
  emit(ast->parts[0]);
  scan(PPToken(")"));
}

void PrettyPrintPass::visit(AssignExprAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("set "));
  emit(ast->parts[0]);
  scan(PPToken(" = "));
  scan(pp.tOptNewline);
  emit(ast->parts[1]);
}

// $0 [ $1 ]
void PrettyPrintPass::visit(SubscriptAST* ast) {
  ScopedBlock sb(this);
  emit(ast->parts[0]);

  scan(PPToken("["));
  emit(ast->parts[1]);
  scan(PPToken("]"));
}

// { $0 ; $1 ; ... ; $n }
void PrettyPrintPass::visit(SeqAST* ast) {
  ScopedBlock sb(this);
  FnAST* followingFn = NULL;
  {
  ScopedIndent si(this);
  followingFn = dynamic_cast<FnAST*>(ast->parent);
  if (followingFn) {
    scan(PPToken(" {"));
    scan(pp.tNewline);
  } else {
    scan(PPToken("{ "));
  }

  for (size_t i = 0; i < ast->parts.size(); ++i) {
    { ScopedBlock sb(this);
    emit(ast->parts[i]);
    }

    if (i != ast->parts.size() - 1) {
      if (CallAST* wasCall = dynamic_cast<CallAST*>(ast->parts[i])) {
        scan(pp.tNewline);
      } else {
        scan(PPToken("; "));
      }
    }
  }

  } // indent/dedent

  if (followingFn) {
    scan(pp.tNewline);
    scan(PPToken("}"));
  } else {
    scan(PPToken(" }"));
  }
}

// $0 ( $1, $2, ... , $n )
void PrettyPrintPass::visit(CallAST* ast) {
  ScopedBlock sb(this);
  
  { ScopedBlock sb(this);
  emit(ast->parts[0]);
  }
  { ScopedBlock sb(this);
  scan(PPToken("("));

  if (ast->parts.size() > 1) {
    scan(pp.tIndent);
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
      scan(pp.tDedent);
    }

    emit(ast->parts[i]);
  }

  scan(PPToken(")"));
  } // scoped block
}
#if 0
// array $0
void PrettyPrintPass::visit(ArrayExprAST* ast) {
  scan(PPToken("array"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}
#endif
// tuple $0
void PrettyPrintPass::visit(TupleExprAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("tuple"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}


// simd-vector $0
void PrettyPrintPass::visit(SimdVectorAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("simd-vector"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}

// __COMPILES__ $0
void PrettyPrintPass::visit(BuiltinCompilesExprAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("__COMPILES__"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

#include "parse/TypeASTVisitor.h"

namespace {

struct PrettyPrintTypePass;
inline void recurse(PrettyPrintTypePass* p, TypeAST* ast);

struct PrettyPrintTypePass : public TypeASTVisitor {
  #include "parse/TypeASTVisitor.decls.inc.h"

  virtual void visitChildren(ExprAST* ast) {
   // Only visit children manually!
  }
  inline void emit(TypeAST* t) { recurse(this, t); }

  typedef foster::PughSinofskyPrettyPrinter PrettyPrinter;

private:
  PrettyPrinter pp;

public:
  PrettyPrintTypePass(llvm::raw_ostream& out, int width, int indent_width)
    : pp(out, width, indent_width) {}

  void scan(const PrettyPrinter::PPToken& token) { pp.scan(token); }

  ~PrettyPrintTypePass() {}
};

inline void recurse(PrettyPrintTypePass* p, TypeAST* ast) {
  if (!ast) {
    p->scan(PPToken("<nil>"));
  } else {
    ast->accept(p);
  }
}

typedef PrettyPrintTypePass::PrettyPrinter::PPToken PPToken;

////////////////////////////////////////////////////////////////////

void PrettyPrintTypePass::visit(NamedTypeAST* ast) {
  scan(PPToken(ast->getName()));
}

void PrettyPrintTypePass::visit(TypeVariableAST* ast) {
  scan(PPToken("TypeVar("));
  scan(PPToken(ast->getTypeVariableName()));
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(FnTypeAST* ast) {
  int np = ast->getNumParams();
  scan(PPToken("("));
  if (np > 1) { scan(PPToken("(")); }
  for (int i = 0; i < np; ++i) {
    if (i > 0) {
      scan(PPToken(", "));
    }
    emit(ast->getParamType(i));
  }
  if (np > 1) { scan(PPToken(")")); }
  scan(PPToken(" "));
  scan(PPToken("=>"));
  scan(PPToken(" "));
  emit(ast->getReturnType());
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(RefTypeAST* ast) {
  scan(PPToken("ref("));
  emit(ast->getElementType());
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(TupleTypeAST* ast) {
  scan(PPToken(" { "));
  for (int i = 0; i < ast->getNumContainedTypes(); ++i) {
    if (i > 0) {
      scan(PPToken(", "));
    }
    emit(ast->getContainedType(i));
  }
  scan(PPToken(" } "));
}

void PrettyPrintTypePass::visit(ClosureTypeAST* ast) {
  scan(PPToken("closure("));
  emit(ast->getFnType());
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(SimdVectorTypeAST* ast) {
  scan(PPToken("simd-vector("));
  std::stringstream ss; ss << ast->getNumElements();
  scan(PPToken(ss.str()));
  scan(PPToken(", "));
  emit(ast->getContainedType(0));
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(LiteralIntValueTypeAST* ast) {
  std::stringstream ss; ss << ast->getNumericalValue();
  scan(PPToken(ss.str()));
}

} // unnamed namespace

namespace foster {

void prettyPrintType(TypeAST* t,
                     llvm::raw_ostream& out, int width, int indent_width) {
  PrettyPrintTypePass pp(out, width, indent_width);
  t->accept(&pp);
}

} // namespace foster
