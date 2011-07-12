// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "parse/FosterAST.h"
#include "passes/PrettyPrintPass.h" // for prettyPrintType

#include "llvm/Support/raw_os_ostream.h"

#include <sstream>

using foster::EDiag;
using foster::show;
using foster::currentErrs;
using foster::SourceRange;
using foster::SourceRangeHighlighter;
using foster::SourceLocation;

using std::string;

std::ostream& operator<<(std::ostream& out, const TypeAST& type) {
  llvm::raw_os_ostream rout(out);
  foster::prettyPrintType(&type, rout, 40);
  return out;
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


