// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_REPLACE_TYPE_H
#define FOSTER_PASSES_REPLACE_TYPE_H

#include "parse/TypeASTVisitor.h"

#include <map>
#include <string>

struct ExprAST;
struct TypeAST;

struct ReplaceTypeTransform : public TypeASTVisitor {
  TypeAST* resultType;
  bool alteredType;

  TypeAST* getResultType() { return resultType; }
  void resetResultType(TypeAST* ty) { resultType = ty; alteredType = false; } 
  void setResultType(TypeAST* ty) { resultType = ty; alteredType = true; }

  typedef std::map<std::string, TypeAST*> TypeVarSubstitution;
  TypeVarSubstitution& typeVarSubst;
  ReplaceTypeTransform(TypeVarSubstitution& tvs)
    :  resultType(NULL), alteredType(false), typeVarSubst(tvs) {}

  void subst(TypeAST*& ty);
  virtual void visitChildren(TypeAST* ast) {
    // Only visit children manually!
  }

  #include "parse/TypeASTVisitor.decls.inc.h"
};

namespace foster {
  void replaceTypesIn(ExprAST* ast, ReplaceTypeTransform& rtt);
}

#endif // header guard

