// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/LLVMContext.h"
#include "llvm/Target/TargetSelect.h"

#include "base/Assert.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterSymbolTable.h"
#include "parse/CompilationContext.h"

#include <map>
#include <string>

using llvm::getGlobalContext;

using std::map;
using std::string;

namespace foster {

llvm::ExecutionEngine* ee;
llvm::IRBuilder<> builder(llvm::getGlobalContext());
llvm::Module* module;

map<string, const llvm::Type*> gCachedLLVMTypes;

TypeAST*    TypeASTFor(const string& name) {
  if (gCachedLLVMTypes.count(name) == 1) {
    return TypeAST::get(gCachedLLVMTypes[name]);
  } else if (TypeAST* ty = gTypeScope.lookup(name, "")) {
    return ty;
  } else {
    if (const llvm::Type* ty = LLVMTypeFor(name)) {
      ASSERT(false) << "WARNING: have LLVMTypeFor("<<name<<")"
                    << " but no TypeASTFor(...)";
    }
    return NULL;
  }
}

const llvm::Type* LLVMTypeFor(const string& name) {
  if (gCachedLLVMTypes.count(name) == 1) {
    return gCachedLLVMTypes[name];
  } else {
    return foster::module->getTypeByName(name);
  }
}

void initCachedLLVMTypeNames() {
  gCachedLLVMTypes["i1"] = llvm::IntegerType::get(getGlobalContext(), 1);
  gCachedLLVMTypes["i8"] = llvm::IntegerType::get(getGlobalContext(), 8);
  gCachedLLVMTypes["i16"] = llvm::IntegerType::get(getGlobalContext(), 16);
  gCachedLLVMTypes["i32"] = llvm::IntegerType::get(getGlobalContext(), 32);
  gCachedLLVMTypes["i64"] = llvm::IntegerType::get(getGlobalContext(), 64);

  gCachedLLVMTypes["i8*"] = llvm::PointerType::getUnqual(gCachedLLVMTypes["i8"]);
  gCachedLLVMTypes["i8**"] = llvm::PointerType::getUnqual(gCachedLLVMTypes["i8*"]);
}


/// Macros in TargetSelect.h conflict with those from ANTLR, so this code
/// must be in a source file that does not include any ANTLR files.
void initializeLLVM() {
  llvm::InitializeNativeTarget();

  // Initializing the native target doesn't initialize the native
  // target's ASM printer, so we have to do it ourselves.
#if LLVM_NATIVE_ARCH == X86Target
  LLVMInitializeX86AsmPrinter();
#else
  std::cerr << "Warning: not initializing any asm printer!" << std::endl;
#endif

  initCachedLLVMTypeNames();
}

} // namespace foster
