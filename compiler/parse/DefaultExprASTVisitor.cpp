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
void DefaultExprASTVisitor::visit(UnaryOpExprAST* ast)         { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(BinaryOpExprAST* ast)        { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(FnAST* ast)                  { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(ModuleAST* ast)              { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(IfExprAST* ast)              { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(RefExprAST* ast)             { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(DerefExprAST* ast)           { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(AssignExprAST* ast)          { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(SubscriptAST* ast)           { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(SimdVectorAST* ast)          { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(SeqAST* ast)                 { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(CallAST* ast)                { this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(TupleExprAST* ast)           { if (0) this->visitChildren(ast); }
void DefaultExprASTVisitor::visit(BuiltinCompilesExprAST* ast) { this->visitChildren(ast); }
//void DefaultExprASTVisitor::visit(ArrayExprAST* ast)           { this->visitChildren(ast); }

// These three require special handling, since they don't store
// (all of) their subcomponents in their parts array.

void DefaultExprASTVisitor::visit(ForRangeExprAST* ast)              {
  onVisitChild(ast, ast->var);
  visitChildren(ast);
}

void DefaultExprASTVisitor::visit(ClosureAST* ast) {
  if (ast->fn) {
    onVisitChild(ast, ast->fn);
  }
  visitChildren(ast);
}

void DefaultExprASTVisitor::visit(PrototypeAST* ast)           {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    onVisitChild(ast, ast->inArgs[i]);
  }
}
