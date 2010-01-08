// vim: set foldmethod=marker :
// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b2d1929175588_52157406
#define H_4b2d1929175588_52157406

#include <antlr3defs.h>
#include <string>

typedef pANTLR3_BASE_TREE pTree;

class ExprAST;

ExprAST* ExprAST_from(pTree tree, int depth, bool infn);
void initMaps();

std::string str(pANTLR3_STRING pstr);

std::string str(pANTLR3_COMMON_TOKEN tok);

#endif // header guard

