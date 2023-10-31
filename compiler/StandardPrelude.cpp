// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Intrinsics.h"

#include "base/LLVMUtils.h" // for str(TypeAST*)

#include "base/Assert.h"

#include <vector>
#include <sstream>

using std::string;

using namespace llvm;

namespace foster {

void putFunctionInScope(const Function& f, Module* linkee) {
  // Ensure that, when parsing, function calls to this name will find it
  FunctionType* fnty = f.getFunctionType();

  // Ensure that codegen for the given function finds the 'declare'
  // TODO make lazy prototype?
  linkee->getOrInsertFunction(f.getName(), fnty, f.getAttributes());
}

// Add module m's C-linkage functions in the global scopes,
// and also add prototypes to the linkee module.
void putModuleFunctionsInScope(Module* m, Module* linkee) {
  if (!m) return;

  for (auto &f : *m) {
    const llvm::StringRef name = f.getName();
    bool isCxxLinkage = name.startswith("_Z");

    bool hasDef = !f.isDeclaration();
    if (hasDef && !isCxxLinkage
               && !name.startswith("__cxx_")) {
      putFunctionInScope(f, linkee);
    }
  }
}

} // namespace foster

