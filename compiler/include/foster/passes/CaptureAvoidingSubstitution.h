// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CAPTURE_AVOIDING_SUBSTITUTION
#define FOSTER_PASSES_CAPTURE_AVOIDING_SUBSTITUTION

#include <map>
#include <set>
#include <string>

struct ExprAST;
struct FnAST;

void captureAvoidingSubstitution(ExprAST* ast,
  const std::string& varName, ExprAST* replacement,
  const std::map<FnAST*, std::set<std::string> >& boundVarsPerFn);

#endif // header guard

