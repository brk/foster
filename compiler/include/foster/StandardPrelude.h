// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_STANDARD_PRELUDE_HELPERS_H
#define FOSTER_STANDARD_PRELUDE_HELPERS_H

#include <set>
#include <string>

namespace llvm {
  class Module;
}

namespace foster {

extern std::set<std::string> globalNames;

// Add module m's C-linkage functions in the global scopes,
// and also add prototypes to the linkee module.
void putModuleMembersInScope(llvm::Module* m, llvm::Module* linkee);

void createLLVMBitIntrinsics();

}

#endif
