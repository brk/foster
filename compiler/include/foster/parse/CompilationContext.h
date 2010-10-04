// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_COMPILATION_CONTEXT_H
#define FOSTER_COMPILATION_CONTEXT_H

#include "llvm/Support/IRBuilder.h"

namespace llvm {
  class Module;
  class raw_ostream;
}

struct ExprAST;
struct TypeAST;

namespace foster {

void initializeLLVM();

extern llvm::IRBuilder<> builder;

} // namespace foster

#endif
