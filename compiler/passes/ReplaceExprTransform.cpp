// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/ParsingContext.h"
#include "passes/ReplaceExprTransform.h"
#include "parse/FosterAST.h"
#include "base/Assert.h"

#include <vector>
#include <map>
#include <set>

using namespace std;

// For now, rewriting goes bottom-up: children are rewritten first,
// then their parents, and rewritten compound nodes do NOT get their
// children inspected again. Hopefully it will be flexible enough.

void ReplaceExprTransform::visitChildren(ExprAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      this->onVisitChild(ast, &ast->parts[i]);
    } else {
      llvm::errs() << "visitChildren saw null part " << i << " for ast node "
                  << str(ast) << "\n";
    }
  }
}

// Note! child is a *reference* to a pointer!
void ReplaceExprTransform::onVisitChild(ExprAST*, ExprAST** child) {
  this->newChild = NULL;
  (*child)->accept(this); // Should write to newChild...
  ASSERT(this->newChild != NULL);
  if (*child != this->newChild) {
    foster::ParsingContext::setParent(this->newChild,
      foster::ParsingContext::getParent(*child));
    (*child) = this->newChild;
  }
}

ExprAST* ReplaceExprTransform::rewrite(ExprAST* ast) {
  if (this->staticReplacements.count(ast) == 1) {
    return this->staticReplacements[ast];
  }
  // TODO implement custom/"dynamic" replacements
  return ast;
}

// NOTE: For now, ints and bools may not be rewritten.
void ReplaceExprTransform::visit(BoolAST* ast)                { this->newChild = ast; }
void ReplaceExprTransform::visit(IntAST* ast)                 { this->newChild = ast; }
void ReplaceExprTransform::visit(VariableAST* ast)            { this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(IfExprAST* ast)              { visitChildren(ast); this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(NilExprAST* ast)             { visitChildren(ast); this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(SubscriptAST* ast)           { visitChildren(ast); this->newChild = rewrite(ast); }
//void ReplaceExprTransform::visit(SimdVectorAST* ast)          { visitChildren(ast); this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(SeqAST* ast)                 { visitChildren(ast); this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(CallAST* ast)                { visitChildren(ast); this->newChild = rewrite(ast); }
//void ReplaceExprTransform::visit(ArrayExprAST* ast)           { visitChildren(ast); this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(TupleExprAST* ast)           { visitChildren(ast); this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(BuiltinCompilesExprAST* ast) { visitChildren(ast); this->newChild = rewrite(ast); }
void ReplaceExprTransform::visit(NamedTypeDeclAST* ast)       { return; }

void ReplaceExprTransform::visit(PrototypeAST* ast)           {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    // Manually add variance, blah.
    ExprAST* var = ast->inArgs[i];
    onVisitChild(ast, &var);
    if (var && var != ast->inArgs[i]) {
      if (VariableAST* varvar = dynamic_cast<VariableAST*>(var)) {
        ast->inArgs[i] = varvar;
      } else {
        llvm::errs() << "Error in ReplaceExprTransform: can't replace "
            << str(ast->inArgs[i]) << " with " << str(var) << "\n";
      }
    }
  }
  this->newChild = ast; // Prototypes can't be rewritten to anything else...
}

void ReplaceExprTransform::visit(FnAST* ast) {
  // TODO need anything special for closures?

  ast->getProto()->accept(this); // No chance of rewriting to proto to a different node type!
  onVisitChild(ast, &ast->getBody());
  this->newChild = rewrite(ast);
}

void ReplaceExprTransform::visit(ModuleAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    onVisitChild(ast, &ast->parts[i]);
  }
  // No replacing entire modules...
}
