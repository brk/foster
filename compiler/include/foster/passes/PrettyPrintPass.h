// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_PRETTYPRINT_PUGH
#define FOSTER_PASSES_PRETTYPRINT_PUGH

#include "parse/ExprASTVisitor.h"
#include "passes/PughSinofskyPrettyPrinter.h"

#include <string>
#include <deque>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;

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
  
  bool printVarTypes;
  PrettyPrinter pp;
  
  PrettyPrintPass(std::ostream& out, int width = 80, int indent_width = 2)
    : printVarTypes(false), pp(out, width, indent_width) {}
    
  void scan(const PrettyPrinter::PPToken& token) { pp.scan(token); }
  
  ~PrettyPrintPass() {}
};

#endif // header guard

