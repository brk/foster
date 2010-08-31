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

namespace llvm {
  class raw_ostream;
}

namespace foster {

  struct SingleIntegerRange;
  struct Valuation;
  struct SingleIntegerRangeConstraint;
  struct SingleIntegerRangeVariable;
  
  struct SingleIntegerRangeExpr {
    virtual SingleIntegerRange* evaluate(Valuation* p) = 0;
    virtual llvm::raw_ostream& dump(llvm::raw_ostream&) const = 0;
  };

  bool isEmpty(SingleIntegerRange*);
  SingleIntegerRange* getConstantRange(int x, int y);
  SingleIntegerRange* getMinRange(int x);
  SingleIntegerRange* getMaxRange(int x);
  SingleIntegerRange* getTopRange();
  SingleIntegerRangeExpr* expr(SingleIntegerRange*);
  SingleIntegerRangeVariable* getVariable(const std::string& name);
  SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                              const std::string& var);
  SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                              SingleIntegerRange* r,
                                              const std::string& var);

  llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRange& e);
  llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeConstraint& e);
  llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeVariable& e);
    
  inline llvm::raw_ostream&
  operator<<(llvm::raw_ostream& out, const SingleIntegerRangeExpr& e) {
    return e.dump(out);
  }
}

#endif // include guard
