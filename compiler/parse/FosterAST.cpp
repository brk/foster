// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/DumpStructure.h"

#include "passes/PrettyPrintPass.h"

#include "llvm/DerivedTypes.h"
#include "llvm/Support/raw_os_ostream.h"

#include <map>
#include <vector>
#include <sstream>

using foster::EDiag;
using foster::show;
using foster::currentErrs;
using foster::SourceRange;
using foster::SourceRangeHighlighter;
using foster::SourceLocation;

using llvm::Type;
using llvm::getGlobalContext;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;

using std::vector;
using std::string;


std::ostream& operator<<(std::ostream& out, const TypeAST& type) {
  llvm::raw_os_ostream rout(out);
  foster::prettyPrintType(&type, rout, 40);
  return out;
}

std::ostream& operator<<(std::ostream& out, const ExprAST& expr) {
  return expr.operator<<(out);
}


string str(const ExprAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

string str(const TypeAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

namespace foster {

SourceRangeHighlighter show(ExprAST* ast) {
  if (!ast) {
    SourceLocation empty = SourceLocation::getInvalidLocation();
    return SourceRangeHighlighter(SourceRange(NULL, empty, empty, NULL), empty);
  }
  return show(ast->sourceRange);
}

char kDefaultFnLiteralCallingConvention[] = "fastcc";

} // namespace foster

////////////////////////////////////////////////////////////////////

IntAST::IntAST(const string& originalText,
              foster::SourceRange sourceRange)
        : ExprAST("IntAST", sourceRange), text(originalText) {}

std::string IntAST::getOriginalText() const { return text; }

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

PrototypeAST::PrototypeAST(TypeAST* retTy, const string& name,
             const std::vector<VariableAST*>& inArgs,
             foster::SourceRange sourceRange)
    : ExprAST("PrototypeAST", sourceRange),
      name(name), inArgs(inArgs), resultTy(retTy) {
        ASSERT(resultTy != NULL) << "proto: " << name << foster::show(sourceRange);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

std::ostream& ExprAST::operator<<(std::ostream& out) const {
  llvm::raw_os_ostream raw(out);
  foster::dumpExprStructure(raw, this);
}

