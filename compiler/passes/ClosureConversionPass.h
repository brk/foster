// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CLOSURECONVERSION
#define FOSTER_PASSES_CLOSURECONVERSION

#include "parse/FosterASTVisitor.h"

#include <set>
#include <string>

struct ClosureConversionPass : public FosterASTVisitor {
  #include "parse/FosterASTVisitor.decls.inc.h"
  std::set<std::string> globalNames;
  ClosureConversionPass(const std::set<std::string>& globalNames) : globalNames(globalNames) {}
};

#endif // header guard

