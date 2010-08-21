// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_PRETTYPRINT_PUGH
#define FOSTER_PASSES_PRETTYPRINT_PUGH

#include "parse/ExprASTVisitor.h"
#include "passes/PughSinofskyPrettyPrinter.h"

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
  PrettyPrintPass(std::ostream& out, int width = 80, int indent_width = 2)
    : pp(out, width, indent_width),
      printVarTypes(false),
      printSignaturesOnly(false) {}

  void setPrintSignaturesOnly(bool newval) { printSignaturesOnly = newval; }
  void scan(const PrettyPrinter::PPToken& token) { pp.scan(token); }
  
  ~PrettyPrintPass() {}
};

class TypeAST;

namespace foster {

void prettyPrintType(TypeAST* t,
                     std::ostream& out, int width = 80, int indent_width = 2);

} // namespace foster

#endif // header guard

