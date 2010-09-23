// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/DefaultExprASTVisitor.h"

#include "passes/ComputeFreeNames.h"

using std::map;
using std::string;
using std::set;
using std::vector;
using std::stringstream;

struct ComputeFreeVariableNames : public DefaultExprASTVisitor {
  VariableBindingInfo& names;
  bool annotateVarsWithBindingScopeInfo;

  ComputeFreeVariableNames(VariableBindingInfo& names, bool annotateVars)
    : names(names), annotateVarsWithBindingScopeInfo(annotateVars) { }

  virtual void visit(VariableAST*);
  virtual void visit(FnAST*);
  virtual void visit(ClosureAST*);
  virtual void visit(PrototypeAST*);
};

namespace foster {

  // Updates the given maps with information about which variables are
  // free and which are not free in any given expression.
  void computeFreeVariableNames(ExprAST* ast,
                                VariableBindingInfo& names,
                                bool annotateVarsWithBindingInfo) {
    ComputeFreeVariableNames cf(names, annotateVarsWithBindingInfo);
    ast->accept(&cf);
  }

}


////////////////////////////////////////////////////////////////////

//void ComputeFreeVariableNames::visit(ArrayExprAST* ast)           { this->visitChildren(ast); }

void ComputeFreeVariableNames::visit(VariableAST* ast) {
  string name = ast->getName();
  if (annotateVarsWithBindingScopeInfo) {
    ast->name = names.annotateWithBindingInfo(name);
  }
  names.markNameAsMentioned(name);
}

void ComputeFreeVariableNames::visit(ClosureAST* ast) {
  if (ast->fn) {
    onVisitChild(ast, ast->fn);
  }
  visitChildren(ast);
}

void ComputeFreeVariableNames::visit(FnAST* ast) {
  names.pushBinder(ast);
  this->onVisitChild(ast, ast->getProto()); // Mark formals as bound.

  names.markAsBound(ast->getProto()->name); // Ensure the function name is
                                            // not free in its own body.
  this->onVisitChild(ast, ast->getBody());
  names.popBinder(ast);
}

void ComputeFreeVariableNames::visit(PrototypeAST* ast) {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    names.markAsBound(ast->inArgs[i]->getName());
    onVisitChild(ast, ast->inArgs[i]);
  }
}
