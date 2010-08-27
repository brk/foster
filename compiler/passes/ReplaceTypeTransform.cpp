// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "passes/ReplaceTypeTransform.h"
#include "parse/FosterAST.h"

#include "llvm/Support/Debug.h"

#include <vector>
#include <map>
#include <set>

using namespace std;

bool ReplaceTypeTransform::subst(TypeAST*& ty) {
  if (!ty) return false;
  
  TypeAST* oldResultType = resultType;
  resultType = ty;
  ty->accept(this);
  bool changingType = resultType != ty; 
  if (changingType) {
    llvm::outs() << "replacing " << str(ty) << " with " << str(resultType) << "\n";
  }
  ty = resultType;
  resultType = oldResultType;
  return changingType;
}

void ReplaceTypeTransform::visit(NamedTypeAST* ast) {
}

void ReplaceTypeTransform::visit(TypeVariableAST* ast) {
  TypeAST* newType = typeVarSubst[ast->getTypeVariableName()];
  setResultType(newType);
}

void ReplaceTypeTransform::visit(FnTypeAST* ast) {
  for (size_t i = 0; i < ast->getNumParams(); ++i) {
    subst(ast->getParamType(i));
  }
  subst(ast->getReturnType());
}

void ReplaceTypeTransform::visit(RefTypeAST* ast) {
  subst(ast->getElementType());
}

void ReplaceTypeTransform::visit(TupleTypeAST* ast) {
  for (size_t i = 0; i < ast->getNumContainedTypes(); ++i) {
    subst(ast->getContainedType(i));
  }
}

void ReplaceTypeTransform::visit(ClosureTypeAST* ast) {
  llvm::outs() << "ignoring closure type ast while substituting types...\n";
}

void ReplaceTypeTransform::visit(SimdVectorTypeAST* ast) {
  subst(ast->getContainedType(0));
}

void ReplaceTypeTransform::visit(LiteralIntValueTypeAST* ast) {
  // ignore?
}

////////////////////////////////////////////////////////////////////

#include "parse/ExprASTVisitor.h"
 
struct ReplaceTypeInExprTransform : public ExprASTVisitor {
  ReplaceTypeTransform& replaceTypeTransform;

  void applyTypeSubst(ExprAST* ast);

  ReplaceTypeInExprTransform(ReplaceTypeTransform& rtt) : replaceTypeTransform(rtt) {}

  virtual void visitChildren(ExprAST* ast);

# include "parse/ExprASTVisitor.decls.inc.h"
};

void ReplaceTypeInExprTransform::visitChildren(ExprAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
     ast->parts[i]->accept(this);
    } else {
     llvm::errs() << "visitChildren saw null part " << i << " for ast node " << str(ast) << "\n";
    }
  }
  applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::applyTypeSubst(ExprAST* ast) {
  if (ast->type) {
    replaceTypeTransform.subst(ast->type);
  } else {
    llvm::errs() << "Ack! ReplaceTypeInExprTransform saw " 
                 << ast->tag << " expr with a NULL type!\n";
  }
}
 
 // NOTE: For now, ints and bools may not be rewritten.
void ReplaceTypeInExprTransform::visit(BoolAST* ast)                { }
void ReplaceTypeInExprTransform::visit(IntAST* ast)                 { }
void ReplaceTypeInExprTransform::visit(VariableAST* ast)            { applyTypeSubst(ast); }
void ReplaceTypeInExprTransform::visit(UnaryOpExprAST* ast)         { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(BinaryOpExprAST* ast)        { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(PrototypeAST* ast)           {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    (ast->inArgs[i])->accept(this);
  }
  replaceTypeTransform.subst(ast->resultTy);
}
void ReplaceTypeInExprTransform::visit(FnAST* ast)                  {
  (ast->proto)->accept(this);
  (ast->body)->accept(this);
  applyTypeSubst(ast);  
}
 
void ReplaceTypeInExprTransform::visit(ClosureAST* ast) {  
  ast->fn->accept(this);
  visitChildren(ast);
}
void ReplaceTypeInExprTransform::visit(NamedTypeDeclAST* ast) { applyTypeSubst(ast); }
void ReplaceTypeInExprTransform::visit(ModuleAST* ast) { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(IfExprAST* ast)              {
  visitChildren(ast); applyTypeSubst(ast);
}
void ReplaceTypeInExprTransform::visit(ForRangeExprAST* ast)              {
  visitChildren(ast); applyTypeSubst(ast);
}
void ReplaceTypeInExprTransform::visit(NilExprAST* ast)             { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(RefExprAST* ast)             { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(DerefExprAST* ast)           { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(AssignExprAST* ast)          { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(SubscriptAST* ast)           { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(SimdVectorAST* ast)          { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(SeqAST* ast)                 { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(CallAST* ast)                { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(TupleExprAST* ast)           { visitChildren(ast); }
void ReplaceTypeInExprTransform::visit(BuiltinCompilesExprAST* ast) { visitChildren(ast); }

namespace foster {
  void replaceTypesIn(ExprAST* ast, ReplaceTypeTransform& rtt) {
    ReplaceTypeInExprTransform rtet(rtt);
    ast->accept(&rtet);
  }
}
