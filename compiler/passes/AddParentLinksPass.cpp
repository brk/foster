// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/AddParentLinksPass.h"

#include "parse/DefaultExprASTVisitor.h"

struct AddParentLinksPass : public DefaultExprASTVisitor {
  virtual void onVisitChild(ExprAST* ast, ExprAST* child) {
    child->parent = ast;
    child->accept(this);
  }

  virtual void visit(FnAST* ast);
  virtual void visit(ModuleAST* ast);

  using DefaultExprASTVisitor::visit;
};

namespace foster {
  void addParentLinks(ExprAST* ast) {
    AddParentLinksPass p; ast->accept(&p);
  }
}


void includeParentNameInAnonFunctions(FnAST* ast);

////////////////////////////////////////////////////////////////////

// The work of adding parent links is done in the onVisitChild()
// function defined in AddParentLinksPass.h
// Thus, the visit() implementations for simple AST nodes and
// AST nodes that store children in their |parts| are trivial.

void AddParentLinksPass::visit(FnAST* ast)                  {
  visitChildren(ast);
  includeParentNameInAnonFunctions(ast);
}
void AddParentLinksPass::visit(ModuleAST* ast)              {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    onVisitChild(NULL, ast->parts[i]);
  }
}

////////////////////////////////////////////////////////////////////

void includeParentNameInAnonFunctions(FnAST* ast) {
  string& name = ast->getName();

  // Not an anonymous function, nothing to do here.
  if (name.find("<anon_fn") != 0) {
    llvm::outs() << "\t\tNot an anonymous function: " << name << "\n";
    return;
  } else {
    llvm::outs() << "\t\tFound an anonymous function: " << name << "\n";
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
    llvm::errs() << "Odd, couldn't find parent fn ast for anonymous function "
              << ast->getName() << "\n";
    return;
  }

  ast->parent = parent;
}
