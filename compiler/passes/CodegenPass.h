// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b3f24ef542273_50678977
#define H_4b3f24ef542273_50678977

#include "FosterASTVisitor.h"
#include <stack>

struct CodegenPass : public FosterASTVisitor {
  #include "FosterASTVisitor.decls.inc.h"

  std::stack<llvm::BasicBlock*> insertPointStack;
};

#endif // header guard


  
