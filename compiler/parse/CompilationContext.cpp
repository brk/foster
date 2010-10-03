// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/CompilationContext.h"

#include "llvm/LLVMContext.h"
#include "llvm/Target/TargetSelect.h"

namespace foster {

  llvm::IRBuilder<> builder(llvm::getGlobalContext());


  void initCachedLLVMTypeNames();

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

