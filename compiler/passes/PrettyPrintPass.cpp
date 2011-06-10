// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/PrettyPrintPass.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ANTLRtoFosterAST.h" // for reconstructing explicit parens

#include <sstream>

#include "base/PughSinofskyPrettyPrinter.h"

#include "pystring/pystring.h"


struct PrettyPrintPass {
  // This can be used in lieu of ast->accept(ppp)
  // to ensure proper outer parens,
  // mainly useful for unit tests.
  void emit(const ExprAST*, bool forceOuterParens = false);
  void emit(const Pattern*, bool forceOuterParens = false);

  typedef foster::PughSinofskyPrettyPrinter PrettyPrinter;

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

////////////////////////////////////////////////////////////////////

typedef PrettyPrintPass::PrettyPrinter::PPToken PPToken;

class ScopedParens {
  PrettyPrintPass* pass;
  bool enable;
public:
  ScopedParens(PrettyPrintPass* p, bool enable = true)
    : pass(p), enable(enable) {
    if (enable) {
      pass->scan(PPToken("("));
    }
  }

  ~ScopedParens() {
    if (enable) {
      pass->scan(PPToken(")"));
    }
  }
};

class ScopedBlock {
  PrettyPrintPass* pass;
public:
  ScopedBlock(PrettyPrintPass* p) : pass(p) {
    pass->scan(pass->pp.tBlockOpen);
  }

  ~ScopedBlock() {
    pass->scan(pass->pp.tBlockClose);
  }
};

class ScopedIndent {
  PrettyPrintPass* pass;
public:
  ScopedIndent(PrettyPrintPass* p) : pass(p) {
    pass->scan(pass->pp.tIndent);
  }

  ~ScopedIndent() {
    pass->scan(pass->pp.tDedent);
  }
};

// Note: to get explicit parenthesization, recurse() should be called
// instead of ast->accept(); in pretty printing bodies.
inline void recurse(PrettyPrintPass* p, const ExprAST* ast, bool wrapInParens) {
  if (!ast) {
    p->scan(PPToken("<nil>"));
  } else {
    ScopedParens sp(p, wrapInParens);
    (const_cast<ExprAST*>(ast))->show(p);
  }
}

inline void recurse(PrettyPrintPass* p, const Pattern* ast) {
  if (!ast) {
    p->scan(PPToken("<nil>"));
  } else {
    (const_cast<Pattern*>(ast))->show(p);
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

void PrettyPrintPass::emit(const Pattern* ast, bool forceParens) {
  recurse(this, ast);
}

////////////////////////////////////////////////////////////////////

void BoolAST::show(PrettyPrintPass* pass) {
  pass->scan(PPToken( (boolValue) ? "true" : "false" ));
}

void IntAST::show(PrettyPrintPass* pass) {
  pass->scan(PPToken(this->getOriginalText()));
}

// name (: type)
void VariableAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  pass->scan(PPToken(this->name));
  //std::stringstream ss; ss << "@" << this; pass->scan(PPToken(ss.str()));
  if (pass->printVarTypes) {
    pass->scan(PPToken(":"));
    if (this->type) {
      pass->emitType(this->type);
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

void showFormal(Formal* f, PrettyPrintPass* pass) {
  ASSERT(false && "showFormal() not yet implemented");
}

void ValAbs::show(PrettyPrintPass* pass) {
  { ScopedBlock sb(pass);
    pass->scan(PPToken("{"));
    { ScopedBlock sb2(pass);
      for (size_t i = 0; i < this->formals.size(); ++i) {
        showFormal(formals[i], pass);
        pass->scan(PPToken(" => "));
      }
    }
    pass->emit(this->parts[0]);
    pass->scan(PPToken("}"));
  }
}

void WildcardPattern::show(PrettyPrintPass* pass) {
  pass->scan(PPToken("_"));
}

void LiteralPattern::show(PrettyPrintPass* pass) {
  pass->emit(this->pattern);
}

void TuplePattern::show(PrettyPrintPass* pass) {
  ASSERT(false && "PrettyPrintPass/TuplePattern not yet implemented");
}

// case e (of p)+ end
void CaseExpr::show(PrettyPrintPass* pass) {
  { ScopedBlock sb(pass);
  pass->scan(PPToken("case "));
  pass->emit(this->parts[0]);
  }

  { ScopedBlock sb(pass);
    for (size_t i = 0; i < branches.size(); ++i) {
      pass->scan(PPToken("of "));
      { ScopedBlock sb(pass);
        pass->emit(branches[i].first);
      }
      pass->scan(PPToken(" -> "));
      { ScopedBlock sb(pass);
        pass->emit(branches[i].second);
      }
    }
  }
  { ScopedBlock sb(pass);
  pass->scan(PPToken("end"));
  }
}

// if $0 then $1 else $2
void IfExprAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);

  { ScopedBlock sb(pass);
  pass->scan(PPToken("if "));
  pass->emit(this->getTestExpr());
  }

  pass->scan(pass->pp.tConnNewline);

  { ScopedBlock sb(pass);
  pass->scan(PPToken(" then "));
  pass->emit(this->getThenExpr());
  }

  pass->scan(pass->pp.tConnNewline);

  { ScopedBlock sb(pass);
  pass->scan(PPToken(" else "));
  pass->emit(this->getElseExpr());
  }
}
// (ref $0)
void AllocAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  pass->scan(PPToken("(ref "));
  pass->emit(this->parts[0]);
  pass->scan(PPToken(")"));
}


// $0^
void DerefAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  pass->emit(this->parts[0]);
  pass->scan(PPToken("^"));
}

// $0 >^ $1
void StoreAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  pass->emit(this->parts[0]);
  pass->scan(PPToken(" >^ "));
  pass->emit(this->parts[1]);
}

// $0 [ $1 ]
void SubscriptAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  pass->emit(this->parts[0]);

  pass->scan(PPToken("["));
  pass->emit(this->parts[1]);
  pass->scan(PPToken("]"));
}

// let $0 = $1 in $2
void LetAST::show(PrettyPrintPass* pass) {
  pass->scan(PPToken("let "));
  pass->emit(this->parts[0]);
  pass->scan(PPToken(" = "));
  pass->emit(this->parts[1]);
  pass->scan(PPToken(" in "));
  ScopedBlock sb(pass);
  pass->emit(this->parts[2]);
}

// { $0 ; $1 ; ... ; $n }
void SeqAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  {
  ScopedIndent si(pass);
  pass->scan(PPToken(" {"));
  pass->scan(pass->pp.tNewline);

  for (size_t i = 0; i < this->parts.size(); ++i) {
    { ScopedBlock sb(pass);
    pass->emit(this->parts[i]);
    }

    if (i != this->parts.size() - 1) {
      if (dynamic_cast<CallAST*>(this->parts[i])) {
        pass->scan(pass->pp.tNewline);
      } else {
        pass->scan(PPToken("; "));
        pass->scan(pass->pp.tConnNewline);
      }
    }
  }

  } // indent/dedent

  pass->scan(PPToken(" }"));
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
void CallAST::show(PrettyPrintPass* pass) {
  if (isPrimitiveBinopCall(this)) {
    prettyPrintBinaryExpr(pass, this);
    return;
  }

  ScopedBlock sb(pass);

  { ScopedBlock sb(pass);
  pass->emit(this->parts[0]);
  }
  { ScopedBlock sb(pass);
  pass->scan(PPToken("("));

  if (this->parts.size() > 1) {
    pass->scan(pass->pp.tIndent);
  }

  bool first = true;
  for (size_t i = 1; i < this->parts.size(); ++i) {
    if (!first) {
      pass->scan(PPToken(","));
      pass->scan(PPToken(" "));
    }
    first = false;

    if (i == this->parts.size() -1) {
      // dedent "early" because a dedent followed directly
      // by a close-paren doesn't do much for us...
      pass->scan(pass->pp.tDedent);
    }

    pass->emit(this->parts[i]);
  }

  pass->scan(PPToken(")"));
  } // scoped block
}

// $0.[$ty]
void ETypeAppAST::show(PrettyPrintPass* pass) {
  pass->emit(this->parts[0]);
  pass->scan(PPToken(".["));
  pass->emitType(this->typeArg);
  pass->scan(PPToken("]"));
}

// tuple $0
void TupleExprAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  pass->scan(PPToken("tuple"));
  pass->scan(PPToken(" "));
  pass->emit(this->parts[0]);
}

// __COMPILES__ $0
void BuiltinCompilesExprAST::show(PrettyPrintPass* pass) {
  ScopedBlock sb(pass);
  pass->scan(PPToken("__COMPILES__"));
  pass->scan(PPToken(" "));
  pass->emit(this->parts[0]);
}

////////////////////////////////////////////////////////////////////

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
////////////////////////////////////////////////////////////////////

inline void recurse(PrettyPrintTypePass* const p, TypeAST* ast);

struct PrettyPrintTypePass {
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

inline void recurse(PrettyPrintTypePass* pass, TypeAST* ast) {
  if (!ast) {
    pass->scan(PPToken("<nil>"));
  } else {
    ast->show(pass);
  }
}

typedef PrettyPrintTypePass::PrettyPrinter::PPToken PPToken;

////////////////////////////////////////////////////////////////////

void NamedTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(this->getName()));
}

void TypeVariableAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken("TypeVar("));
  pass->scan(PPToken(this->getTypeVariableName()));
  pass->scan(PPToken(")"));
}

void FnTypeAST::show(PrettyPrintTypePass* pass){
  int np = this->getNumParams();
  pass->scan(PPToken("("));
  if (np > 1) { pass->scan(PPToken("|")); }
  for (int i = 0; i < np; ++i) {
    if (i > 0) {
      pass->scan(PPToken(", "));
    }
    pass->emit(this->getParamType(i));
  }
  if (np > 1) { pass->scan(PPToken("|")); }
  pass->scan(PPToken(" "));
  string arrow = "=" + this->getCallingConventionName() +
        (this->isMarkedAsClosure() ? " func" : " proc") + ">";
  pass->scan(PPToken(arrow));
  pass->scan(PPToken(" "));
  pass->emit(this->getReturnType());
  pass->scan(PPToken(")"));
}

void RefTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken("ref("));
  pass->emit(this->getElementType());
  pass->scan(PPToken(")"));
}

void CoroTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken("Coro("));
  pass->emit(this->getContainedType(0));
  pass->scan(PPToken(", "));
  pass->emit(this->getContainedType(1));
  pass->scan(PPToken(")"));
}

void CArrayTypeAST::show(PrettyPrintTypePass* pass){
  std::stringstream ss; ss << this->getSize();
  pass->scan(PPToken("CArray["));
  pass->emit(this->getContainedType(0));
  pass->scan(PPToken("]("));
  pass->scan(PPToken(ss.str()));
  pass->scan(PPToken(")"));
}

void TupleTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(" { "));
  for (int i = 0; i < this->getNumContainedTypes(); ++i) {
    if (i > 0) {
      pass->scan(PPToken(", "));
    }
    pass->emit(this->getContainedType(i));
  }
  pass->scan(PPToken(" } "));
}

namespace foster {

void prettyPrintType(const TypeAST* t,
                     llvm::raw_ostream& out, int width, int indent_width) {
  PrettyPrintTypePass pp(out, width, indent_width);
  const_cast<TypeAST*>(t)->show(&pp);
}

} // namespace foster

