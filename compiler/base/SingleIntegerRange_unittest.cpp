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
  EXPECT_EQ("[1, 0]", pr(oz));
  
  SingleIntegerRange* nz = getConstantRange(-1, 0);
  EXPECT_EQ("[-1, 0]", pr(nz));
  
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
  SingleIntegerRangeConstraint* c = getConstraint(expr(zz), "X");
  EXPECT_EQ("[0, 0] <= X", pr(c));
  
  SingleIntegerRange* nz = getConstantRange(-1, 0);
  
  SingleIntegerRangeConstraint* c2 = getConstraint(expr(zz), nz, "X");
  EXPECT_EQ("[0, 0] meet [-1, 0] <= X", pr(c2));
}

TEST(SingleIntegerRangeConstraints, ex1) {
  //SingleIntegerRangeConstraintSet cs;
  //cs.insert();
}

/////////////////////////////////



} // unnamed namespace

