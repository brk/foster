// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/DefaultExprASTVisitor.h"

// No children in these AST nodes
void DefaultExprASTVisitor::visit(BoolAST* ast)                { return; }
void DefaultExprASTVisitor::visit(IntAST* ast)                 { return; }
void DefaultExprASTVisitor::visit(VariableAST* ast)            { return; }
void DefaultExprASTVisitor::visit(NilExprAST* ast)             { return; }
void DefaultExprASTVisitor::visit(NamedTypeDeclAST* ast)       { return; }

// Just recurse...
// (the |if (0)|s are because some types visit children in their ->accept() implementations.
void DefaultExprASTVisitor::visit(ModuleAST* ast)              { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(IfExprAST* ast)              { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(SubscriptAST* ast)           { if (0) this->visitChildren(ast); }
//void DefaultExprASTVisitor::visit(SimdVectorAST* ast)          { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(SeqAST* ast)                 { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(CallAST* ast)                { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(ETypeAppAST* ast)            { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(TupleExprAST* ast)           { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(BuiltinCompilesExprAST* ast) { this->visitChildren(ast); }
//void DefaultExprASTVisitor::visit(ArrayExprAST* ast)           { this->visitChildren(ast); }

// These two require special handling, since they don't store
// (all of) their subcomponents in their parts array.

void DefaultExprASTVisitor::visit(FnAST* ast) {
  if (ast->isClosure()) {
    for (size_t i = 0; i < ast->environmentParts->size(); ++i) {
      onVisitChild(ast, (*(ast->environmentParts))[i]);
    }
  }
  onVisitChild(ast, ast->proto);
  onVisitChild(ast, ast->getBody());
}

void DefaultExprASTVisitor::visit(PrototypeAST* ast)           {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    onVisitChild(ast, ast->inArgs[i]);
  }
}
