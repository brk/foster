// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_COMPUTE_FREE_NAMES_H     
#define FOSTER_PASSES_COMPUTE_FREE_NAMES_H

#include <map>
#include <string>
#include <set>
#include <vector>
#include <sstream>

#include "base/Assert.h"

#include "llvm/Support/raw_ostream.h"

struct VariableBindingInfo;
struct ExprAST;

namespace foster {
  void computeFreeVariableNames(ExprAST* ast,
                                VariableBindingInfo& names,
                                bool annotateVarsWithBindingInfo = false);
}

class VariableBindingInfo {
  // To avoid blowup of these sets, we only store direct information
  // for nodes that actually bind variables. Binding info for other nodes
  // may be computed by traversing the binder stack.
  std::map<ExprAST*, std::set<std::string> > namesFreeIn;
  std::map<ExprAST*, std::set<std::string> > namesBoundBy;
  
  std::vector<ExprAST*> binderStack;
  
  const std::set<std::string>& globallyBoundNames;
public:
  VariableBindingInfo(const std::set<std::string>& globallyBoundNames)
    : globallyBoundNames(globallyBoundNames) {}
  
  void pushBinder(ExprAST* binder) {
    binderStack.push_back(binder);
  }

  void popBinder(ExprAST* binder) {
    ASSERT(!binderStack.empty());
    ExprAST* prevBinder = binderStack.back();
    binderStack.pop_back();
    ASSERT(binder == prevBinder) << "binder mismatch when computing free vars";
  }
 
  void markAsBound(const std::string& name) {
    ASSERT(!binderStack.empty());
    namesBoundBy[binderStack.back()].insert(name);
  }

  void markNameAsMentioned(const std::string& name) {
    if (!isLocallyBound(name)) {
      foundFreeName(name);
    }
  }
  
  bool isGloballyBound(const std::string& name) {
    return globallyBoundNames.count(name) == 1;
  }
  
  std::string annotateWithBindingInfo(const std::string& name) {
    std::stringstream ss; ss << name;
    if (isGloballyBound(name)) {
      ss << "_gb"; return ss.str();
    }

    for (size_t i = binderStack.size() - 1; i >= 0; --i) {
      ExprAST* binder = binderStack[i];
      if (namesBoundBy[binder].count(name) == 1) {
        ss << "_b" << i; return ss.str();
      }
      ss << "_f" << i;
      
      if (i == 0) break;
    }
    return ss.str();
  }

private:
  bool isLocallyBound(const std::string& name) {
    ASSERT(!binderStack.empty());
    return isGloballyBound(name)
        || namesBoundBy[binderStack.back()].count(name) == 1;
  }
  
  // Mark the variable as being free in this and all parent scopes in which the
  // variable has not been marked as bound. This handles the case in which
  // a variable is free in a parent scope but only appears in a nested scope.
  void foundFreeName(const std::string& name) {
    for (size_t i = binderStack.size() - 1; i >= 0; --i) {
      ExprAST* binder = binderStack[i];
      if (namesBoundBy[binder].count(name) == 1) {
        break;
      }
      namesFreeIn[binder].insert(name);
      if (i == 0) break;
    }
  }
};

//  fn (x) {
//     y (x, z)  // y free ; z free; x bound
//     fn (y) {
//       y(x, z) // y bound; z free; x free (locally)
//     }
//  }

#endif

