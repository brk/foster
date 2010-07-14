// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_BUILD_CFG
#define FOSTER_PASSES_BUILD_CFG

#include "parse/FosterASTVisitor.h"

#include "cfg/CFG.h"

struct BuildCFG : public FosterASTVisitor {
  #include "parse/FosterASTVisitor.decls.inc.h"

  virtual void visitChildren(ExprAST* ast) {
    // Only visit children manually!
  }

  foster::CFG* currentRoot;
  FnAST* currentFn;
};

#endif // header guard
