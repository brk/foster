// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_TYPECHECK
#define FOSTER_PASSES_TYPECHECK

#include <string>

struct ExprAST;

namespace foster {

bool typecheck(ExprAST*);

} // namespace foster

bool isPrintRef(const ExprAST* base);

inline bool isArithOp(const std::string& op) {
  return op == "+" || op == "-" || op == "/" || op == "*";
}

inline bool isCmpOp(const std::string& op) {
  return op == "<" || op == "<=" || op == ">" || op == ">="
      || op == "==" || op == "!=";
}


#endif // header guard

