// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CLOSURECONVERSION
#define FOSTER_PASSES_CLOSURECONVERSION

#include <set>
#include <string>

struct ModuleAST;

namespace foster {
  void performClosureConversion(const std::set<std::string>& globalNames,
                                ModuleAST* mod);
}

#endif // header guard

