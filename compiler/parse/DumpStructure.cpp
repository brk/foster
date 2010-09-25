// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/DumpStructure.h"
#include "parse/FosterAST.h"

#include "llvm/Support/raw_ostream.h"

/*
Produce output like this:
http://blogs.msdn.com/b/ericlippert/archive/2010/09/09/old-school-tree-display.aspx

a
├─b
│ ├─c
│ │ └─d
│ └─e
│   └─f
└─g
  ├─h
  │ └─i
  └─j
*/

#define CONST(Type) const Type* const

struct DumpExpr {
  llvm::raw_ostream& out;
  enum status { eFirstChild, eMiddleChild, eLastChild, eAfterChild };

  std::vector<status> stages;
  DumpExpr(llvm::raw_ostream& out) : out(out) {}

  status statusFor(int i, int n) {
    if (i == n - 1) return eLastChild;
    if (i == 0) return eFirstChild;
    return eMiddleChild;
  }

  void dump(CONST(ExprAST) ast) {
    dumpLine(ast);
    stages.push_back(eFirstChild);

    for (unsigned i = 0; i < ast->parts.size(); ++i) {
      stages.back() = statusFor(i, ast->parts.size());
      dump(ast->parts[i]);
    }

    if (CONST(PrototypeAST) e = dynamic_cast<CONST(PrototypeAST)>(ast)) {
      for (unsigned i = 0; i < e->inArgs.size(); ++i) {
        stages.back() = statusFor(i, e->inArgs.size());
        dump(e->inArgs[i]);
      }
    }

    if (CONST(ClosureAST) e = dynamic_cast<CONST(ClosureAST)>(ast)) {
      stages.back() = eLastChild;
      dump(e->fn);
    }

    stages.pop_back();
  }

  void dumpLine(CONST(ExprAST) ast) {
    for (unsigned i = 0; i < stages.size(); ++i) {
      printStage(stages[i]);
    }
    int prefixLength = stages.size() * 2;
    std::string msg = getMessage(ast);
    std::string spaces(std::max(4, int(80 - prefixLength - msg.size())), ' ');
    out << msg << spaces << ast << "\n";
  }

  std::string getMessage(CONST(ExprAST) ast) {
    if (CONST(VariableAST) e = dynamic_cast<CONST(VariableAST)>(ast)) {
      return std::string(e->tag) + " " + e->getName() + " :: " + str(ast->type);
    }
    if (CONST(FnAST) e = dynamic_cast<CONST(FnAST)>(ast)) {
      return std::string(e->tag) + " " + e->getName();
    }
    if (CONST(PrototypeAST) e = dynamic_cast<CONST(PrototypeAST)>(ast)) {
      return std::string(e->tag) + " " + e->getName() + " " + str(ast->type);
    }
    return std::string(ast->tag);
  }

  void printStage(status& s) {
    switch (s) {
      case eFirstChild:  out << "├─"; s = eMiddleChild; break;
      case eMiddleChild: out << "│ "; s = eMiddleChild; break;
      case eLastChild:   out << "└─"; s = eAfterChild; break;
      case eAfterChild:  out << "  "; s = eAfterChild; break;
    }
  }
};

namespace foster {

  void dumpExprStructure(llvm::raw_ostream& out, CONST(ExprAST) ast) {
    out << "\n";
    DumpExpr dumper(out); dumper.dump(ast);
    out << "\n";
  }

}
