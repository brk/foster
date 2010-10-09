// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/ParsingContext.h"
#include "passes/CaptureAvoidingSubstitution.h"
#include "parse/FosterAST.h"
#include "base/Assert.h"

#include <vector>
#include <set>

using namespace std;

using foster::ParsingContext;

#include "parse/ExprASTVisitor.h"

struct CaptureAvoidingSubstitution : public ExprASTVisitor {

  const std::string& varName;
  ExprAST* replacement;
  const std::map<FnAST*, std::set<std::string> >& boundVarsPerFn;

  CaptureAvoidingSubstitution(const std::string& varName, ExprAST* replacement,
    const std::map<FnAST*, std::set<std::string> >& boundVarsPerFn)
  : varName(varName), replacement(replacement), boundVarsPerFn(boundVarsPerFn) {}

  virtual void visitChildren(ExprAST* ast);

  // Note! child is a pointer to a pointer!
  void cavsVisitChild(ExprAST* ast, ExprAST** child);
  ExprAST* newChild; // Hack side-channel return value

# include "parse/ExprASTVisitor.decls.inc.h"
};

////////////////////////////////////////////////////////////////////

void captureAvoidingSubstitution(ExprAST* ast,
  const std::string& varName, ExprAST* replacement,
  const std::map<FnAST*, std::set<std::string> >& boundVarsPerFn) {

  CaptureAvoidingSubstitution rex(varName, replacement, boundVarsPerFn);

  ast->accept(&rex);
}

////////////////////////////////////////////////////////////////////

void CaptureAvoidingSubstitution::visitChildren(ExprAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      this->cavsVisitChild(ast, &ast->parts[i]);
    } else {
      llvm::errs() << "visitChildren saw null part " << i << " for ast node "
                  << str(ast) << "\n";
    }
  }
  this->newChild = ast;
}

void CaptureAvoidingSubstitution::cavsVisitChild(ExprAST*, ExprAST** child) {
  ExprAST* originalChild = *child;
  this->newChild = originalChild;
  originalChild->accept(this); // may write to newChild...
  ASSERT(this->newChild != NULL);
  if (originalChild != this->newChild) {
    ParsingContext::setParent(this->newChild,
      ParsingContext::getParent(originalChild));
    llvm::outs() << "onVisitChild replacing " << str(originalChild) << " with " << str(newChild) << "\n";
    (*child) = this->newChild;
  }
}

// NOTE: For now, ints and bools may not be rewritten.
void CaptureAvoidingSubstitution::visit(BoolAST* ast)                { }
void CaptureAvoidingSubstitution::visit(IntAST* ast)                 { }
void CaptureAvoidingSubstitution::visit(NamedTypeDeclAST* ast) { return; }
void CaptureAvoidingSubstitution::visit(ModuleAST* ast)              { visitChildren(ast); }
void CaptureAvoidingSubstitution::visit(IfExprAST* ast)              { visitChildren(ast); }
void CaptureAvoidingSubstitution::visit(NilExprAST* ast)             { visitChildren(ast); }
void CaptureAvoidingSubstitution::visit(SubscriptAST* ast)           { visitChildren(ast); }
//void CaptureAvoidingSubstitution::visit(SimdVectorAST* ast)          { visitChildren(ast); }
void CaptureAvoidingSubstitution::visit(SeqAST* ast)                 { visitChildren(ast); }
void CaptureAvoidingSubstitution::visit(CallAST* ast)                { visitChildren(ast); }
//void CaptureAvoidingSubstitution::visit(ArrayExprAST* ast)           { visitChildren(ast); }
void CaptureAvoidingSubstitution::visit(TupleExprAST* ast)           { visitChildren(ast); }
void CaptureAvoidingSubstitution::visit(BuiltinCompilesExprAST* ast) { visitChildren(ast); }

void CaptureAvoidingSubstitution::visit(VariableAST* ast)            {
  if (varName == ast->name) {
    llvm::outs() << "varast setting replacmeent for var " << varName << "\n";
    this->newChild = replacement;
  }
}

void CaptureAvoidingSubstitution::visit(PrototypeAST* ast)           {
  // Prototypes can't be rewritten.
}
void CaptureAvoidingSubstitution::visit(FnAST* ast)                  {
  // Ignore closure environment.

  // Only replace variable in functions which don't bind it. E.g. with
  //   f = (x, y) => { (x + y +  z ) + ((y, z) => { x + y + z })() }
  // substituting SSS for z in f would yield
  //   f = (x, y) => { (x + y + SSS) + ((y, z) => { x + y + z })() }
  std::map<FnAST*, std::set<std::string> >::const_iterator it = boundVarsPerFn.find(ast);
  if (it != boundVarsPerFn.end()) {
    if (it->second.count(varName) == 0) {
      cavsVisitChild(ast, &ast->getBody());
    }
  }
}

