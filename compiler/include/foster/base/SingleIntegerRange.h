// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_SINGLE_INTEGER_RANGE_H
#define FOSTER_SINGLE_INTEGER_RANGE_H

// Implementation of contiguous integer range constraints
// based on the paper
//
// A Class of Polynomially Solvable Range Constraints for
// Interval Analysis without Widenings and Narrowings
//
// by Zhendong Su and David Wagner.
//
// http://www.eecs.berkeley.edu/~daw/papers/range-tacas04.pdf

#include <string>
#include <set>

namespace llvm {
  class raw_ostream;
  class APInt;
}

namespace foster {

  struct SingleIntegerRange;
  struct Valuation;
  struct SingleIntegerRangeConstraint;
  struct SingleIntegerRangeVariable;
  
  struct SingleIntegerRangeExpr {
    virtual SingleIntegerRange* evaluate(Valuation* p) = 0;
    virtual SingleIntegerRangeExpr* negate() = 0;
    virtual llvm::raw_ostream& dump(llvm::raw_ostream&) const = 0;
    virtual void variablesUsed(std::set<SingleIntegerRangeVariable*>& vars) = 0;
  };
  
  struct SingleIntegerRangeConstraintSet {
    void insert(SingleIntegerRangeConstraint*);
    SingleIntegerRange* solve();
    SingleIntegerRangeConstraintSet();
  private:
    struct Impl; Impl* impl;
  };

  bool isEmpty(SingleIntegerRange*);
  SingleIntegerRange* getConstantRange(int x);
  SingleIntegerRange* getConstantRange(int x, int y);
  SingleIntegerRange* getMinRange(int x);
  SingleIntegerRange* getMaxRange(int x);
  SingleIntegerRange* getTopRange();
  
  const SingleIntegerRange* computeMeet(const SingleIntegerRange* a, const SingleIntegerRange *b);
  const SingleIntegerRange* computeJoin(const SingleIntegerRange* a, const SingleIntegerRange *b);
  
  const llvm::APInt* getNewAPInt(int n);
  SingleIntegerRangeExpr* mult(const llvm::APInt* n,
                               SingleIntegerRangeVariable* v);
  
  SingleIntegerRangeExpr* expr(SingleIntegerRange*);
  SingleIntegerRangeExpr* expr(SingleIntegerRangeVariable*);
  SingleIntegerRangeExpr* plus(SingleIntegerRangeExpr*, SingleIntegerRangeExpr*);
  SingleIntegerRangeVariable* getVariable(const std::string& name);
  SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                              SingleIntegerRangeVariable*);
  SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                              SingleIntegerRange* r,
                                              SingleIntegerRangeVariable*);
  bool satisfies(Valuation*, SingleIntegerRangeConstraint*);

  llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRange& e);
  llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeConstraint& e);
  llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeVariable& e);
    
  inline llvm::raw_ostream&
  operator<<(llvm::raw_ostream& out, const SingleIntegerRangeExpr& e) {
    return e.dump(out);
  }
}

#endif // include guard
