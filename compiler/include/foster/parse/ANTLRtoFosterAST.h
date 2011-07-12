// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef ANTLR_TO_FOSTER_AST
#define ANTLR_TO_FOSTER_AST

#include <antlr3defs.h>
#include <string>
#include <iosfwd>

typedef pANTLR3_BASE_TREE pTree;

class ModuleAST;

namespace foster {

class ANTLRContext;
struct InputFile;

ModuleAST* parseModule(const InputFile& file,
                       const std::string& moduleName,
                       unsigned* outNumANTLRErrors);

} // namespace foster

#endif // header guard

