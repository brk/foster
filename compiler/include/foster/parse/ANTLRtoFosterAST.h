// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef ANTLR_TO_FOSTER_AST
#define ANTLR_TO_FOSTER_AST

#include <antlr3defs.h>
#include <string>
#include <vector>
#include <iosfwd>

typedef pANTLR3_BASE_TREE pTree;

struct InputWholeProgram;

namespace foster {

struct ANTLRContext;
class InputFile;

InputWholeProgram* parseWholeProgram(const InputFile& file,
                                   const std::vector<std::string> searchPaths,
                                   unsigned* outNumANTLRErrors);

void dumpModuleTokens(const InputFile& file);

} // namespace foster

#endif // header guard

