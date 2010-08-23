// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterAST.h"
#include "passes/AddParentLinksPass.h"

void includeParentNameInAnonFunctions(FnAST* ast);

// The work of adding parent links is done in the onVisitChild()
// function defined in AddParentLinksPass.h
// Thus, the visit() implementations for simple AST nodes and
// AST nodes that store children in their |parts| are trivial.

void AddParentLinksPass::visit(BoolAST* ast)                { return; }
void AddParentLinksPass::visit(IntAST* ast)                 { return; }
void AddParentLinksPass::visit(VariableAST* ast)            { return; }
void AddParentLinksPass::visit(UnaryOpExprAST* ast)         { return; }
void AddParentLinksPass::visit(BinaryOpExprAST* ast)        { return; }
void AddParentLinksPass::visit(PrototypeAST* ast)           {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    onVisitChild(ast, ast->inArgs[i]);
  }
}
void AddParentLinksPass::visit(FnAST* ast)                  {
  onVisitChild(ast, ast->proto);
  onVisitChild(ast, ast->body);
  includeParentNameInAnonFunctions(ast);
}
void AddParentLinksPass::visit(ClosureAST* ast) {
  if (ast->fn) {
    onVisitChild(ast, ast->fn);
  }
}
void AddParentLinksPass::visit(ModuleAST* ast)              {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    onVisitChild(NULL, ast->parts[i]);
  }
}
void AddParentLinksPass::visit(NamedTypeDeclAST* ast) {
  return;
}
void AddParentLinksPass::visit(IfExprAST* ast)              {
  visitChildren(ast);
}
void AddParentLinksPass::visit(ForRangeExprAST* ast)              {
  onVisitChild(ast, ast->startExpr);
  onVisitChild(ast, ast->endExpr);
  if (ast->incrExpr) { onVisitChild(ast, ast->incrExpr); }
  onVisitChild(ast, ast->bodyExpr);
}
void AddParentLinksPass::visit(NilExprAST* ast)             { return; }
void AddParentLinksPass::visit(RefExprAST* ast)             { return; }
void AddParentLinksPass::visit(DerefExprAST* ast)           { return; }
void AddParentLinksPass::visit(AssignExprAST* ast)          { return; }
void AddParentLinksPass::visit(SubscriptAST* ast)           { return; }
void AddParentLinksPass::visit(SimdVectorAST* ast)          { return; }
void AddParentLinksPass::visit(SeqAST* ast)                 { return; }
void AddParentLinksPass::visit(CallAST* ast)                { visitChildren(ast); }
//void AddParentLinksPass::visit(ArrayExprAST* ast)           { return; }
void AddParentLinksPass::visit(TupleExprAST* ast)           { return; }
void AddParentLinksPass::visit(BuiltinCompilesExprAST* ast) { visitChildren(ast); }

void includeParentNameInAnonFunctions(FnAST* ast) {
  string& name = ast->proto->name;

  // Not an anonymous function, nothing to do here.
  if (name.find("<anon_fn") != 0) {
    std::cout << "\t\tNot an anonymous function: " << name << std::endl;
    return;
  } else {
    std::cout << "\t\tFound an anonymous function: " << name << std::endl;
  }

  FnAST* parentFn = NULL;
  ExprAST* parent = ast->parent;
  while (parent != NULL) {
    parentFn = dynamic_cast<FnAST*>(parent);
    if (parentFn) {
      break;
    } else {
      parent = parent->parent;
    }
  }

  if (!parent) {
    std::cerr << "Odd, couldn't find parent fn ast for anonymous function "
              << ast->proto->name << std::endl;
    return;
  }

  ast->parent = parent;
}
