// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_COMPILATION_CONTEXT_H
#define FOSTER_COMPILATION_CONTEXT_H

#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Module.h"

namespace foster {

void initializeLLVM();

extern llvm::ExecutionEngine* ee;
extern llvm::IRBuilder<> builder;
extern llvm::Module* module;

} // namespace foster

#endif
