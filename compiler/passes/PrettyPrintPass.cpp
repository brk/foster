// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/PrettyPrintPass.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ANTLRtoFosterAST.h" // for reconstructing explicit parens

#include <sstream>
#include <string>

#include "base/PughSinofskyPrettyPrinter.h"

#include "llvm/Support/raw_os_ostream.h"

using std::string;

std::ostream& operator<<(std::ostream& out, const TypeAST& type) {
  llvm::raw_os_ostream rout(out);
  foster::prettyPrintType(&type, rout, 40);
  return out;
}

string str(const TypeAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

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

typedef PrettyPrintTypePass::PrettyPrinter::PPToken PPToken;

inline void recurse(PrettyPrintTypePass* pass, TypeAST* ast) {
  if (!ast) {
    pass->scan(PPToken("<nil>"));
  } else {
    ast->show(pass);
  }
}

////////////////////////////////////////////////////////////////////

void PrimitiveTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(this->getName()));
}

void NamedTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(this->getName()));
}

void DataTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(this->getName()));
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

void ArrayTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken("(Array "));
  pass->emit(this->getContainedType(0));
  pass->scan(PPToken(")"));
}

void VoidTypeAST::show(PrettyPrintTypePass* pass) {
  pass->scan(PPToken("void"));
}

void TupleTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(" {{ "));
  for (int i = 0; i < this->getNumContainedTypes(); ++i) {
    if (i > 0) {
      pass->scan(PPToken(", "));
    }
    pass->emit(this->getContainedType(i));
  }
  pass->scan(PPToken(" }} "));
}

void StructTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(" {# "));
  for (int i = 0; i < this->getNumContainedTypes(); ++i) {
    if (i > 0) {
      pass->scan(PPToken(", "));
    }
    pass->emit(this->getContainedType(i));
  }
  pass->scan(PPToken(" #} "));
}

void TypeTypeAppAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken(" ( "));
  for (int i = 0; i < this->getNumContainedTypes(); ++i) {
    if (i > 0) {
      pass->scan(PPToken(" "));
    }
    pass->emit(this->getContainedType(i));
  }
  pass->scan(PPToken(" ) "));
}

void ForallTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken("(forall ... "));
  pass->emit(this->quant);
  pass->scan(PPToken(")"));
}

void RefinedTypeAST::show(PrettyPrintTypePass* pass){
  pass->scan(PPToken("% "));
  pass->scan(PPToken(this->name));
  pass->scan(PPToken(" : "));
  pass->emit(this->underlyingType);
  pass->scan(PPToken(" : "));
  pass->scan(PPToken("...(refinement)..."));
}

namespace foster {

void prettyPrintType(const TypeAST* t,
                     llvm::raw_ostream& out, int width, int indent_width) {
  PrettyPrintTypePass pp(out, width, indent_width);
  const_cast<TypeAST*>(t)->show(&pp);
}

} // namespace foster

