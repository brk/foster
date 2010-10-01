// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "gtest/gtest.h"

#include "parse/ANTLRtoFosterAST.h"
#include "passes/TypecheckPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ComputeFreeNames.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/CompilationContext.h"

#include "llvm/Support/raw_ostream.h"

#include "pystring/pystring.h"

#include <vector>
#include <map>
#include <string>

using std::string;

// terrible hack!
namespace foster {
extern std::map<std::string, const llvm::Type*> gCachedLLVMTypes;
}

namespace {

void initCachedLLVMTypes() {
  static bool done = false;
  if (done) return;
  done = true;
  foster::gCachedLLVMTypes["i32"] = TypeAST::i(32)->getLLVMType();
  foster::gCachedLLVMTypes["i64"] = TypeAST::i(64)->getLLVMType();
  foster::gCachedLLVMTypes["void"] = TypeAST::getVoid()->getLLVMType();
}

foster::CompilationContext cc1;
foster::CompilationContext cc2;

ExprAST* parse(foster::CompilationContext& cc, const string& s) {
  unsigned errs = 0;
  ExprAST* rv = foster::parseExpr(s, errs, &cc);
  return errs == 0 ? rv : NULL;
}


ExprAST* elaborate(foster::CompilationContext& cc, ExprAST* e) {
  if (e) {
    foster::CompilationContext::pushContext(&cc);
    foster::typecheck(e);
    foster::CompilationContext::popCurrentContext();
  }
  return e;
}

string pr(ExprAST* ast) {
  std::string s; llvm::raw_string_ostream out(s);
  foster::prettyPrintExpr(ast, out, 55);
  return out.str();
}

#define STR(x) #x

////////////////////////////////////////////////////////////////////

void filterVarNames(std::vector<std::string>& v, const std::string& s) {
  std::string s_no_parens = pystring::replace(s,           "(", " ");
  s_no_parens = pystring::replace(s_no_parens, ")", " ");

  std::vector<std::string> chunks;
  pystring::split(s_no_parens, chunks);
  for (size_t i = 0; i < chunks.size(); ++i) {
    std::vector<std::string> parts;
    pystring::split(chunks[i], parts, ":");
    if (!parts[0].empty()) {
      char c = parts[0][0];
      if ( c == 'x' || c == 'y' || c == 'z' ) {
        v.push_back(parts[0]);
      }
    }
  }
}

TEST(ComputeFreeNames, annotate_names) {
  initCachedLLVMTypes();
  ExprAST* e = parse(cc1, STR(
    fn (x : i32, z: i32, y : i32) {
    fn (x : i32) { x + y + z +
    fn (y : i32) { x + y + z } } }
));

  string unann = pr(e);


  std::set<std::string> globalNames;
  VariableBindingInfo vbi(globalNames);
  foster::computeFreeVariableNames(e, vbi, true);

  string ann = pr(e);

  EXPECT_NE(unann, ann);

  std::vector<std::string> ann_varnames;
  std::vector<std::string> unann_varnames;
  std::vector<std::string> exp_varnames;

  filterVarNames(ann_varnames, ann);
  filterVarNames(unann_varnames, unann);

  EXPECT_EQ("x z y x x y z y x y z", pystring::join(" ", unann_varnames));

  // Names are annotated with inner-to-outer scoping info, with inner scopes
  // getting higher numbers.
  string expected = "\n"
"fn <anon_fn_0> ( x_b0:i32 z_b0:i32 y_b0:i32 to i32 ){ <closure \n"
"  fn <anon_fn_1> ( x_b1:i32 to i32 ){ ((x_b1 +\n"
"     y_f1_b0) + z_f1_b0) + (<closure \n"
"    fn <anon_fn_2> ( y_b2:i32 to i32 ){ (x_f2_b1 +\n"
"       y_b2) + z_f2_f1_b0 }>) }> }";

  filterVarNames(exp_varnames, expected);

  const char* ann_names = "x_b0 z_b0 y_b0 x_b1 x_b1 y_f1_b0 z_f1_b0 "
                          "y_b2 x_f2_b1 y_b2 z_f2_f1_b0";
  EXPECT_EQ(ann_names, pystring::join(" ", ann_varnames));
  EXPECT_EQ(ann_names, pystring::join(" ", exp_varnames));
}

#undef STR


} // unnamed namespace


