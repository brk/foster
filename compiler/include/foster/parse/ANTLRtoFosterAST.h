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

class IntAST;
class ExprAST;
class ModuleAST;

namespace llvm {
class APInt;
}

namespace foster {

bool wasExplicitlyParenthesized(ExprAST* ast);

class SourceRange;

IntAST* parseInt(const std::string& clean,
                 const std::string& alltext,
                 int base,
                 const SourceRange& sourceRange);

llvm::APInt* parseAPIntFromClean(const std::string& clean, int base,
                                 const SourceRange& sourceRange);
  
class ANTLRContext;

void deleteANTLRContext(ANTLRContext* ctx);

struct InputFile;
struct CompilationContext;

ExprAST* parseExpr(const std::string& source,
                   unsigned& outNumANTLRErrors,
                   CompilationContext* cc);

ModuleAST* parseModule(const InputFile& file,
                       pTree& outTree,
                       ANTLRContext*& outContext,
                       unsigned& outNumANTLRErrors,
                       CompilationContext* cc);

} // namespace foster

#endif // header guard

