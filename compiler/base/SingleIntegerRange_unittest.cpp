// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/SingleIntegerRange.h"
#include "gtest/gtest.h"

#include "llvm/Support/raw_ostream.h"

using namespace foster;

namespace {
  
  template <typename T>
  std::string pr(T* r) {
    std::string s;
    llvm::raw_string_ostream ss(s);
    ss << *r;
    return ss.str();
  }

TEST(SingleIntegerRange, simple_printing) {
  SingleIntegerRange* zz = getConstantRange(0, 0);
  EXPECT_EQ("[0, 0]", pr(zz));
  
  SingleIntegerRange* zo = getConstantRange(0, 1);
  EXPECT_EQ("[0, 1]", pr(zo));
  
  SingleIntegerRange* oz = getConstantRange(1, 0);
  EXPECT_EQ("[empty]", pr(oz));
  
  SingleIntegerRange* nz = getConstantRange(-1, 0);
  EXPECT_EQ("[-1, 0]", pr(nz));
}

TEST(SingleIntegerRange, unbounded_range_printing) {
  SingleIntegerRange* minr = getMinRange(42);
  EXPECT_EQ("[42, +inf]", pr(minr));
  
  SingleIntegerRange* maxr = getMaxRange(42);
  EXPECT_EQ("[-inf, 42]", pr(maxr));
  
  SingleIntegerRange* topr = getTopRange();
  EXPECT_EQ("[-inf, +inf]", pr(topr));
  
  EXPECT_EQ(getTopRange(), getTopRange());
}
  
TEST(SingleIntegerRange, emptiness) {
  SingleIntegerRange* zerozero = getConstantRange(0, 0);
  EXPECT_FALSE(isEmpty(zerozero));
  
  SingleIntegerRange* zeroone = getConstantRange(0, 1);
  EXPECT_FALSE(isEmpty(zeroone));
  
  SingleIntegerRange* onezero = getConstantRange(1, 0);
  EXPECT_TRUE(isEmpty(onezero));
  
  SingleIntegerRange* nz = getConstantRange(-1, 0);
  EXPECT_FALSE(isEmpty(nz));
  
  SingleIntegerRange* zn = getConstantRange(0, -1);
  EXPECT_TRUE(isEmpty(zn));
}

TEST(SingleIntegerRangeConstraints, constraint_printing) {
  SingleIntegerRange* zz = getConstantRange(0, 0);
  SingleIntegerRangeConstraint* c = getConstraint(expr(zz), getVariable("X"));
  EXPECT_EQ("[0, 0] <= X", pr(c));
  
  SingleIntegerRange* nz = getConstantRange(-1, 0);
  
  SingleIntegerRangeConstraint* c2 = getConstraint(expr(zz), nz, getVariable("X"));
  EXPECT_EQ("[0, 0] meet [-1, 0] <= X", pr(c2));
}

TEST(SingleIntegerRangeConstraints, simple_meet_join) {
  const SingleIntegerRange* _01_34 = computeJoin(getConstantRange(0,1),
                                                 getConstantRange(3,4));
  EXPECT_EQ("[0, 4]", pr(_01_34));
  const SingleIntegerRange* _22 = computeMeet(_01_34, getConstantRange(2));
  EXPECT_EQ("[2, 2]", pr(_22));
}

/*
TEST(SingleIntegerRangeConstraints, ex1) {
  SingleIntegerRangeConstraintSet cs;
  // [0,0] <= X
  cs.insert(getConstraint(expr(getConstantRange(0, 0)), getVariable("X")));
  // X + 1 <= X
  cs.insert(getConstraint(plus(expr(getVariable("X")),
                               expr(getConstantRange(1))),
                          getVariable("X")));
  
  SingleIntegerRange* sol = cs.solve();
  EXPECT_EQ("[0, +inf]", pr(sol));
}

TEST(SingleIntegerRangeConstraints, ex2) {
  SingleIntegerRangeConstraintSet cs;
  // [0,0] <= X
  cs.insert(getConstraint(expr(getConstantRange(0, 0)), getVariable("X")));
  // X + 1 /\ (-inf, 10) <= X
  cs.insert(getConstraint(plus(expr(getVariable("X")),
                               expr(getConstantRange(1))),
                          getMaxRange(10),
                          getVariable("X")));
  
  SingleIntegerRange* sol = cs.solve();
  EXPECT_EQ("[0, 10]", pr(sol));
}
*/

#define EXPECTED_FAIL_EQ EXPECT_NE

TEST(SingleIntegerRangeConstraints, simple_loop) {
  SingleIntegerRangeConstraintSet cs;
  // [3,5] <= X
  cs.insert(getConstraint(expr(getConstantRange(3, 5)), getVariable("X")));
  // (7X + 11) /\ (13, 17) <= X
  cs.insert(getConstraint(plus(mult(getNewAPInt(7), getVariable("X")),
                               expr(getConstantRange(11))),
                          getConstantRange(13, 17),
                          getVariable("X")));
  
  SingleIntegerRange* sol = cs.solve();
  EXPECTED_FAIL_EQ("[0, 10]", pr(sol));
}

///////////////////////////////////

TEST(SingleIntegerRangeConstraints, multi_loop) {
  SingleIntegerRangeConstraintSet cs;
  // [3,5] <= X
  cs.insert(getConstraint(expr(getConstantRange(3, 5)), getVariable("X")));
  // (7X + 11) /\ (13, 17) <= X
  cs.insert(getConstraint(plus(mult(getNewAPInt(7), getVariable("X")),
                               expr(getConstantRange(11))),
                          getConstantRange(13, 17),
                          getVariable("X")));
  // (23X + 31) /\ (37, 41) <= X
  cs.insert(getConstraint(plus(mult(getNewAPInt(23), getVariable("X")),
                               expr(getConstantRange(31))),
                          getConstantRange(37, 41),
                          getVariable("X")));
  
  SingleIntegerRange* sol = cs.solve();
  EXPECTED_FAIL_EQ("[0, 10]", pr(sol));
}

/////////////////////////////////



} // unnamed namespace

