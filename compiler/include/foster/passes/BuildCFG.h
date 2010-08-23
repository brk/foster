// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_BUILD_CFG
#define FOSTER_PASSES_BUILD_CFG

struct ModuleAST;

#include "cfg/CFG.h"

namespace foster {
  void buildCFG(ModuleAST* ast);
}

#endif // header guard
