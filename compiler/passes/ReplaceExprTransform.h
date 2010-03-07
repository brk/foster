// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_Foster_ReplaceExprTransform
#define H_Foster_ReplaceExprTransform

#include "FosterASTVisitor.h"

#include <map>
#include <vector>

struct ExprReplacer {
  // Subclasses may set this description string for debugging purposes.
  string description;

  // "No replacement" is signified by directly returning the input.
  virtual ExprAST* maybeReplace(ExprAST*) = 0;
};

struct ReplaceExprTransform : public FosterASTVisitor {

  // These are public; clients should directly register whatever
  // replacements they might wish to apply to the tree.
  std::map<ExprAST*, ExprAST*> staticReplacements;
  std::vector<ExprReplacer> dynamicReplacements;

  ReplaceExprTransform() {}

  virtual void visitChildren(ExprAST* ast);

  // Note! child is a pointer to a pointer!
  void onVisitChild(ExprAST* ast, ExprAST** child);
  ExprAST* newChild; // Hack side-channel return value

  ExprAST* rewrite(ExprAST* ast);

#   define FOSTER_AST_INCLUDED_VIA_DECLS_H
#   include "FosterASTVisitor.base.inc.h"
#   undef  FOSTER_AST_INCLUDED_VIA_DECLS_H
};

#endif // header guard
