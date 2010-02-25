// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b7b8b4e1ce078_82130601
#define H_4b7b8b4e1ce078_82130601

#include "FosterASTVisitor.h"

#include <set>
#include <string>

struct ClosureConversionPass : public FosterASTVisitor {
  #include "FosterASTVisitor.decls.inc.h"
  const std::set<std::string>& globalNames;
  ClosureConversionPass(const std::set<std::string>& globalNames) : globalNames(globalNames) {}
};


#endif // header guard

