// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef ANTLR_TO_FOSTER_AST
#define ANTLR_TO_FOSTER_AST

#include <antlr3defs.h>
#include <string>
#include <iosfwd>

typedef pANTLR3_BASE_TREE pTree;

class TypeAST;
TypeAST* TypeAST_from(pTree tree);

void initMaps();

void dumpANTLRTree(std::ostream& out, pTree tree, int depth);

std::string stringTreeFrom(pTree tree);
std::string str(pANTLR3_COMMON_TOKEN tok);

bool isBitwiseOpName(const std::string& op);


class ExprAST;
class ModuleAST;

namespace foster {

class ANTLRContext;

void deleteANTLRContext(ANTLRContext* ctx);

struct InputFile;

ExprAST* parseExpr(const std::string& source,
                   pTree& outTree,
                   unsigned& outNumANTLRErrors);

ModuleAST* parseModule(const InputFile& file,
                       pTree& outTree,
                       ANTLRContext*& outContext,
                       unsigned& outNumANTLRErrors);

} // namespace foster

#endif // header guard

