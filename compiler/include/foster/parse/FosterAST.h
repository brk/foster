// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "base/InputFile.h"

#include <vector>
#include <string>
#include <map>

#include "city.h"

#include "antlr3interfaces.h"

struct InputModule {
  std::string hash;
  pANTLR3_BASE_TREE tree;
  const foster::InputFile* source;
  std::vector<pANTLR3_COMMON_TOKEN> hiddenTokens;

  explicit InputModule(
    pANTLR3_BASE_TREE tree,
    const foster::InputFile* source,
    std::string hash,
    std::vector<pANTLR3_COMMON_TOKEN> hiddenTokens) :
      hash(hash), tree(tree), source(source), hiddenTokens(hiddenTokens) { }
};

struct InputWholeProgram {
  std::map<uint128, InputModule*> seen;
  std::vector<InputModule*> modules;

  explicit InputWholeProgram() {}

  int getModuleCount() { return modules.size(); }
  InputModule* getInputModule(int x) { return modules[x]; }
};

#endif // header guard

