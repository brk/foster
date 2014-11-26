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

bool gPrintLLVMImports = false;

// Add prototypes for module m's C-linkage functions to the linkee module.
void putModuleMembersInScope(Module* m, Module* linkee) {
  if (!m) return;

  // Collect global variables from the module.
  for (Module::global_iterator it = m->global_begin();
                              it != m->global_end(); ++it) {
    const GlobalVariable& gv = *it;
    if (!gv.isConstant()) {
      outs() << "<internal>\tskipping non-const global\t" << gv.getName() << "\n";
      continue;
    }

    if (gPrintLLVMImports) {
      outs() << "<internal>\tglobal\t" << gv.getName() << "\n";
    }
    linkee->getOrInsertGlobal(gv.getName(), gv.getType());
  }

  // These functions will not be linked in, to keep the postlinked
  // Module as clean as possible.
  std::set<string> functionsToRemove;

  // Collect C-linkage function declarations from the module.
  // Functions with C++ linkage are not included.
  // Functions with definitions are only included if they are explicitly
  // marked (via a foster_ prefix) as being intended for inclusion.
  //
  // This allows a library wrapper to define functions that should be
  // included (such as those that concreteize macro definitions), and
  // also those which should not be included (such as
  // force_these_symbols_to_be_included()).
  for (auto &f : *m) {
    llvm::StringRef name = f.getName();
    bool isCxxLinkage = name.startswith("_Z")
                     || name.startswith("__cxx_");
    if (isCxxLinkage) continue;

    bool hasDef = !f.isDeclaration();
    if (hasDef) {
      if (!name.startswith("foster_")) {
        // drop from original module
        functionsToRemove.insert(name);
        continue;
      }
    }

    Type* ty = f.getType();
    // We get a pointer-to-whatever-function type, because f is a global
    // value (therefore ptr), but we want just the function type.
    if (PointerType* pty = dyn_cast<PointerType>(ty)) {
      ty = pty->getElementType();
    }

    if (FunctionType* fnty = dyn_cast<FunctionType>(ty)) {
      linkee->getOrInsertFunction(StringRef(name), fnty,
                                  f.getAttributes());

      if (gPrintLLVMImports) {
        outs() << "<internal>\t" << hasDef << "\t" << name << " \n";
      }
    } else {
      ASSERT(false) << "how could a function not have function type?!?";
    }
  }

  // Don't link in functions that were just included to force
  // LLVM to include declarations in the module in the first place.
  for (auto it : functionsToRemove) {
    if (gPrintLLVMImports) {
      outs() << "not including function " << it << "\n";
    }
    m->getFunctionList().erase(m->getFunction(it));
  }
}

void putFunctionInScope(const Function& f, Module* linkee) {
   // Ensure that, when parsing, function calls to this name will find it
   Type* ty = f.getType();
   // We get a pointer-to-whatever-function type, because f is a global
   // value (therefore ptr), but we want just the function type.
   if (PointerType* pty = dyn_cast<PointerType>(ty)) {
     ty = pty->getElementType();
   }

   if (FunctionType* fnty = dyn_cast<FunctionType>(ty)) {
     // Ensure that codegen for the given function finds the 'declare'
     // TODO make lazy prototype?
     linkee->getOrInsertFunction(StringRef(f.getName()), fnty,
                                 f.getAttributes());

     if (gPrintLLVMImports) {
       outs() << "inserting variable in global scope: " << f.getName() << " : "
              << str(fnty) << "\n";
     }
   } else {
     ASSERT(false) << "how could a function not have function type?!?";
   }
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

