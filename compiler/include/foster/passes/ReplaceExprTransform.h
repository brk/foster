// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_REPLACEEXPR
#define FOSTER_PASSES_REPLACEEXPR

#include "parse/ExprASTVisitor.h"

#include <map>
#include <vector>

struct ExprReplacer {
  // Subclasses may set this description string for debugging purposes.
  string description;

  // "No replacement" is signified by directly returning the input.
  virtual ExprAST* maybeReplace(ExprAST*) = 0;
  virtual ~ExprReplacer() {}
};

struct ReplaceExprTransform : public ExprASTVisitor {

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


  using ExprASTVisitor::onVisitChild;

# include "parse/ExprASTVisitor.decls.inc.h"
};

#endif // header guard

