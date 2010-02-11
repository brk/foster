// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "AddParentLinksPass.h"
#include "FosterAST.h"

void includeParentNameInAnonFunctions(FnAST* ast);

void AddParentLinksPass::visit(BoolAST* ast)                { return; }
void AddParentLinksPass::visit(IntAST* ast)                 { return; }
void AddParentLinksPass::visit(VariableAST* ast)            { return; }
void AddParentLinksPass::visit(UnaryOpExprAST* ast)         { return; }
void AddParentLinksPass::visit(BinaryOpExprAST* ast)        { return; }
void AddParentLinksPass::visit(PrototypeAST* ast)           {
  for (int i = 0; i < ast->inArgs.size(); ++i) {
    onVisitChild(ast, ast->inArgs[i]);
  }
  for (int i = 0; i < ast->outArgs.size(); ++i) {
    onVisitChild(ast, ast->outArgs[i]);
  }
}
void AddParentLinksPass::visit(FnAST* ast)                  {
  onVisitChild(ast, ast->Proto);
  onVisitChild(ast, ast->Body);
  includeParentNameInAnonFunctions(ast);
}
void AddParentLinksPass::visit(IfExprAST* ast)              {
  onVisitChild(ast, ast->ifExpr);
  onVisitChild(ast, ast->thenExpr);
  onVisitChild(ast, ast->elseExpr);
}
void AddParentLinksPass::visit(SubscriptAST* ast)           { return; }
void AddParentLinksPass::visit(SimdVectorAST* ast)          { return; }
void AddParentLinksPass::visit(SeqAST* ast)                 { return; }
void AddParentLinksPass::visit(CallAST* ast)                {
  visitChildren(ast); return;
}
void AddParentLinksPass::visit(ArrayExprAST* ast)           { return; }
void AddParentLinksPass::visit(TupleExprAST* ast)           { return; }
void AddParentLinksPass::visit(UnpackExprAST* ast)          { return; }
void AddParentLinksPass::visit(BuiltinCompilesExprAST* ast) { return; }

void includeParentNameInAnonFunctions(FnAST* ast) {
  string& name = ast->Proto->Name;

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
    std::cerr << "Odd, couldn't find parent fn ast for anonymous function " << ast->Proto->Name << std::endl;
    return;
  }

  name.replace(0, 1, "<" + parentFn->Proto->Name + "__");
}
