// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b4cf7a48af8e2_37764720
#define H_4b4cf7a48af8e2_37764720

#include "FosterASTVisitor.h"

struct AddParentLinksPass : public FosterASTVisitor {
  #include "FosterASTVisitor.decls.inc.h"
  
  virtual void onVisitChild(ExprAST* ast, ExprAST* child) {
    child->parent = ast;
    child->accept(this);
  }
};


#endif // header guard

