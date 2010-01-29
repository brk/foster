// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "AddParentLinksPass.h"
#include "FosterAST.h"

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
}
void AddParentLinksPass::visit(IfExprAST* ast)              {
  onVisitChild(ast, ast->ifExpr);
  onVisitChild(ast, ast->thenExpr);
  onVisitChild(ast, ast->elseExpr);
}
void AddParentLinksPass::visit(SubscriptAST* ast)           { return; }
void AddParentLinksPass::visit(SimdVectorAST* ast)          { return; }
void AddParentLinksPass::visit(SeqAST* ast)                 { return; }
void AddParentLinksPass::visit(CallAST* ast)                { return; }
void AddParentLinksPass::visit(ArrayExprAST* ast)           { return; }
void AddParentLinksPass::visit(TupleExprAST* ast)           { return; }
void AddParentLinksPass::visit(UnpackExprAST* ast)          { return; }
void AddParentLinksPass::visit(BuiltinCompilesExprAST* ast) { return; }

