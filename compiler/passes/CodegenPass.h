// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CODEGEN
#define FOSTER_PASSES_CODEGEN

#include "FosterASTVisitor.h"
#include <stack>

struct CodegenPass : public FosterASTVisitor {
  #include "FosterASTVisitor.decls.inc.h"

  // The insertPointStack is used to tranparently perform function hoisting
  // while doing our normal codegen tree traversal. Specifically, this stack
  // allows us to return to the "parent" function context after finishing
  // codegenning a nested child function's body.
  std::stack<llvm::BasicBlock*> insertPointStack;
};

#endif // header guard

