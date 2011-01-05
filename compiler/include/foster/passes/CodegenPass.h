// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CODEGEN_H
#define FOSTER_PASSES_CODEGEN_H

struct ExprAST;
struct CodegenPass; // for CFG.cpp

namespace llvm {
  struct Module;
}

namespace foster {
  void codegen(ExprAST* ast, llvm::Module*);
  void codegen(ExprAST* ast, CodegenPass*);
}

#endif // header guard

