// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "parse/CompilationContext.h"

#include "passes/ReplaceTypeTransform.h"
#include "parse/FosterAST.h"

#include "llvm/Support/Debug.h"

#include <vector>
#include <map>
#include <set>

using namespace std;

using foster::currentOuts;
using foster::currentErrs;
using foster::dbg;

bool ReplaceTypeTransform::subst(TypeAST*& ty) {
  if (!ty) return false;

  TypeAST* oldResultType = resultType;
  resultType = ty;
  ty->accept(this);
  bool changingType = resultType != ty;
  if (changingType && resultType) {
    dbg("replacetypes") << str(ty) << " with\t" << str(resultType) << "\n";
    ty = resultType;
  }
  resultType = oldResultType;
  return changingType;
}

void ReplaceTypeTransform::visit(NamedTypeAST* ast) {
}

void ReplaceTypeTransform::visit(TypeVariableAST* ast) {
  TypeAST* newType = typeVarSubst[ast->getTypeVariableName()];
  if (newType) {
    setResultType(newType);
  }
}

void ReplaceTypeTransform::visit(FnTypeAST* ast) {
  for (int i = 0; i < ast->getNumParams(); ++i) {
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
  if (ast->fntype) { ast->getFnType()->accept(this); }
  if (ast->clotype) { ast->clotype->accept(this); }
}

/*
void ReplaceTypeTransform::visit(SimdVectorTypeAST* ast) {
  subst(ast->getContainedType(0));
}
*/

void ReplaceTypeTransform::visit(LiteralIntValueTypeAST* ast) {
  // ignore?
}

////////////////////////////////////////////////////////////////////

#include "parse/DefaultExprASTVisitor.h"

struct ReplaceTypeInExprTransform : public DefaultExprASTVisitor {
  ReplaceTypeTransform& replaceTypeTransform;

  void applyTypeSubst(ExprAST* ast);

  ReplaceTypeInExprTransform(ReplaceTypeTransform& rtt) : replaceTypeTransform(rtt) {}

  virtual void visitChildren(ExprAST* ast);

  virtual void visit(FnAST*);
  virtual void visit(IntAST*);
  virtual void visit(IfExprAST*);
  virtual void visit(ModuleAST*);
  virtual void visit(ClosureAST*);
  virtual void visit(VariableAST*);
  virtual void visit(PrototypeAST*);
  virtual void visit(NamedTypeDeclAST*);
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

////////////////////////////////////////////////////////////////////

void ReplaceTypeInExprTransform::visit(IntAST* ast) {
  applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::visit(VariableAST* ast) {
  applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::visit(PrototypeAST* ast) {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    (ast->inArgs[i])->accept(this);
  }
  replaceTypeTransform.subst(ast->resultTy);
  applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::visit(FnAST* ast) {
  visitChildren(ast); applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::visit(ClosureAST* ast) {
  ASSERT(ast->fn);
  ast->fn->accept(this); visitChildren(ast); applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::visit(NamedTypeDeclAST* ast) {
  applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::visit(ModuleAST* ast) {
  visitChildren(ast); applyTypeSubst(ast);
}

void ReplaceTypeInExprTransform::visit(IfExprAST* ast) {
  visitChildren(ast); applyTypeSubst(ast);
}


namespace foster {
  void replaceTypesIn(ExprAST* ast, ReplaceTypeTransform& rtt) {
    ReplaceTypeInExprTransform rtet(rtt);
    ast->accept(&rtet);
  }
}
