// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef ANTLR_TO_FOSTER_AST
#define ANTLR_TO_FOSTER_AST

#include <antlr3defs.h>
#include <string>
#include <iosfwd>

typedef pANTLR3_BASE_TREE pTree;

void installTreeTokenBoundaryTracker(pANTLR3_BASE_TREE_ADAPTOR adaptor);

class ModuleAST;
ModuleAST* parseTopLevel(pTree tree);

class TypeAST;
TypeAST* TypeAST_from(pTree tree);

void initMaps();

void dumpANTLRTree(std::ostream& out, pTree tree, int depth);

std::string str(pANTLR3_STRING pstr);

std::string str(pANTLR3_COMMON_TOKEN tok);

bool isBitwiseOpName(const std::string& op);

#endif // header guard

