// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ParsingContext.h"

#include "passes/PassUtils.h"

#include <vector>

namespace foster {

void typecheckTuple(TupleExprAST* ast, const Exprs& parts) {
  std::vector<TypeAST*> tupleFieldTypes;
  if (foster::typesOf(parts, "tuple", tupleFieldTypes)) {
    ast->type = TupleTypeAST::get(tupleFieldTypes);
  } else {
    EDiag() << "unable to typecheck tuple " << show(ast);
  }
}

/// Return true if each expression has a valid type scheme, false otherwise.
///
bool typesOf(const std::vector<ExprAST*>& parts,
             const std::string& contextStr,
             std::vector<TypeAST*>& types) {
  for (size_t i = 0; i < parts.size(); ++i) {
    ExprAST* expr = parts[i];
    if (!expr) {
      return false;
    }

    TypeAST* ty = expr->type;
    if (!ty) {
      EDiag() << contextStr << " had null constituent type for subexpression "
              << show(expr);
      return false;
    }

    types.push_back(ty);
  }
  return true;
}

} // namespace foster
