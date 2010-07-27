// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_ADDPARENTLINKS
#define FOSTER_PASSES_ADDPARENTLINKS

#include "parse/FosterASTVisitor.h"

struct AddParentLinksPass : public FosterASTVisitor {
  #include "parse/FosterASTVisitor.decls.inc.h"
  
  virtual void onVisitChild(ExprAST* ast, ExprAST* child) {
    child->parent = ast;
    child->accept(this);
  }
};

#endif // header guard

