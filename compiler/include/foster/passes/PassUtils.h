// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_PASS_UTILS_H
#define FOSTER_PASSES_PASS_UTILS_H

#include <string>
#include <vector>

struct ExprAST;
struct TypeAST;
struct PrototypeAST;
struct FnTypeAST;
struct TupleExprAST;

namespace foster {

void typecheckTuple(TupleExprAST* ast, const std::vector<ExprAST*>& parts);

bool typesOf(const std::vector<ExprAST*>& exprs,
             const std::string& contextStr,
             std::vector<TypeAST*>& types);

} // namespace foster

#endif
