// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_COMPILATION_CONTEXT_H
#define FOSTER_COMPILATION_CONTEXT_H

#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Module.h"

#include "parse/OperatorPrecedence.h"

#include <stack>

struct TypeAST;

// Defined in ANTLRtoFosterAST.cpp; the header
// is not #included due to ANTLR macro conflicts.
void initMaps();

namespace foster {

void initializeLLVM();

class CompilationContext;
extern std::stack<CompilationContext*> gCompilationContexts;

class CompilationContext {
public:
  CompilationContext();
  OperatorPrecedenceTable prec;
};

extern llvm::ExecutionEngine* ee;
extern llvm::IRBuilder<> builder;
extern llvm::Module* module;

TypeAST* TypeASTFor(const std::string& name);
const llvm::Type* LLVMTypeFor(const std::string& name);

} // namespace foster

#endif
