// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/PrettyPrintPass.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ANTLRtoFosterAST.h" // for reconstructing explicit parens

#include <sstream>

#include "base/PughSinofskyPrettyPrinter.h"
#include "parse/ExprASTVisitor.h"

#include "pystring/pystring.h"


struct PrettyPrintPass : public ExprASTVisitor {
  #include "parse/ExprASTVisitor.decls.inc.h"

  // This can be used in lieu of ast->accept(ppp)
  // to ensure proper outer parens,
  // mainly useful for unit tests.
  void emit(const ExprAST*, bool forceOuterParens = false);

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
  void emitType(const TypeAST* ty);

  ~PrettyPrintPass() {}

  friend class ScopedBlock;
  friend class ScopedIndent;
};

namespace foster {
  void prettyPrintExpr(const ExprAST* t,
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
inline void recurse(PrettyPrintPass* p, const ExprAST* ast, bool wrapInParens) {
  if (!ast) {
    p->scan(PPToken("<nil>"));
  } else {
    ScopedParens sp(p, wrapInParens);
    (const_cast<ExprAST*>(ast))->accept(p);
  }
}

bool isAtom(ExprAST* ast) {
  if (dynamic_cast<BoolAST*>(ast)) return true;
  if (dynamic_cast<IntAST*>(ast)) return true;
  if (dynamic_cast<VariableAST*>(ast)) return true;
  return false;
}

bool isDelimited(ExprAST* ast) {
  if (isAtom(ast)) return true;
  return false;
}

bool needsParens(ExprAST* child) {
  return !isDelimited(child);
}

////////////////////////////////////////////////////////////////////

void PrettyPrintPass::emitType(const TypeAST* ty) {
  scan(PPToken(str(ty)));
}

void PrettyPrintPass::emit(const ExprAST* ast, bool forceParens) {
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
      emitType(ast->type);
    }
  }
}

std::string getPrimitiveOpName(const std::string& varname) {
  if (!pystring::startswith(varname, "primitive_")) {
    return "";
  }
  std::vector<std::string> parts;
  pystring::split(varname, parts, "_");
  return parts[1];
}

// $0 op $1
void prettyPrintBinaryExpr(PrettyPrintPass* pass,
                           CallAST* call) {
  ExprAST* e1 = call->parts[1];
  ExprAST* e2 = call->parts[2];
  VariableAST* var = dynamic_cast<VariableAST*>(call->parts[0]);
  std::string op = getPrimitiveOpName(var->getName());

  ScopedBlock sb(pass);

  pass->emit(e1, needsParens(e1));
  pass->scan(PPToken(" "));
  pass->scan(PPToken(op));
  //pass->scan(pass->pp.tOptNewline);
  pass->scan(PPToken(" "));
  pass->emit(e2, needsParens(e2));
}

// fn Name (inArgs to outArgs)
void PrettyPrintPass::visit(PrototypeAST* ast) {
  ScopedBlock sb(this);
  { ScopedBlock sb(this);
  scan(PPToken("fn"));
  scan(PPToken(" "));
  scan(PPToken(ast->getName()));
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
  emit(ast->getProto());

  if (!this->printSignaturesOnly) {
    if (ast->getBody()) {
      emit(ast->getBody());
    }
  }
}

void PrettyPrintPass::visit(ModuleAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    emit(ast->parts[i]);
    scan(pp.tNewline);
  }
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
  scan(PPToken(" {"));
  scan(pp.tNewline);

  for (size_t i = 0; i < ast->parts.size(); ++i) {
    { ScopedBlock sb(this);
    emit(ast->parts[i]);
    }

    if (i != ast->parts.size() - 1) {
      if (dynamic_cast<CallAST*>(ast->parts[i])) {
        scan(pp.tNewline);
      } else {
        scan(PPToken("; "));
        scan(pp.tConnNewline);
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

bool isPrimitiveBinopCall(CallAST* call) {
  ExprAST* base = call->parts[0];
  if (VariableAST* var = dynamic_cast<VariableAST*>(base)) {
    const std::string& opName = getPrimitiveOpName(var->getName());
    return !opName.empty();
  } else {
    return false;
  }
}

// $0 ( $1, $2, ... , $n )
void PrettyPrintPass::visit(CallAST* ast) {
  if (isPrimitiveBinopCall(ast)) {
    prettyPrintBinaryExpr(this, ast);
    return;
  }

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

// $0.[$ty]
void PrettyPrintPass::visit(ETypeAppAST* ast) {
  emit(ast->parts[0]);
  scan(PPToken(".["));
  emitType(ast->typeArg);
  scan(PPToken("]"));
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

/*
// simd-vector $0
void PrettyPrintPass::visit(SimdVectorAST* ast) {
  ScopedBlock sb(this);
  scan(PPToken("simd-vector"));
  scan(PPToken(" "));
  emit(ast->parts[0]);
}
*/

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
  if (np > 1) { scan(PPToken("|")); }
  for (int i = 0; i < np; ++i) {
    if (i > 0) {
      scan(PPToken(", "));
    }
    emit(ast->getParamType(i));
  }
  if (np > 1) { scan(PPToken("|")); }
  scan(PPToken(" "));
  scan(PPToken("=" + ast->getCallingConventionName() + ">"));
  scan(PPToken(" "));
  emit(ast->getReturnType());
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(RefTypeAST* ast) {
  scan(PPToken("ref("));
  emit(ast->getElementType());
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(CoroTypeAST* ast) {
  scan(PPToken("Coro("));
  emit(ast->getContainedType(0));
  scan(PPToken(", "));
  emit(ast->getContainedType(1));
  scan(PPToken(")"));
}

void PrettyPrintTypePass::visit(CArrayTypeAST* ast) {
  std::stringstream ss; ss << ast->getSize();
  scan(PPToken("CArray["));
  emit(ast->getContainedType(0));
  scan(PPToken("]("));
  scan(PPToken(ss.str()));
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

} // unnamed namespace

namespace foster {

void prettyPrintType(const TypeAST* t,
                     llvm::raw_ostream& out, int width, int indent_width) {
  PrettyPrintTypePass pp(out, width, indent_width);
  const_cast<TypeAST*>(t)->accept(&pp);
}

} // namespace foster
