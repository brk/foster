// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/FilteringIterator.h"
#include "gtest/gtest.h"

namespace {

struct Base { int x; Base(int x) : x(x) {}
  virtual ~Base() {}
};
struct Derived : public Base {
  int y; Derived(int x, int y) : Base(x), y(y) {}
};

TEST(FilteringIterator, someOfSome) {
  std::vector<Base*> bases;
  bases.push_back(new Base(1));
  bases.push_back(new Derived(2, 2));
  bases.push_back(new Base(3));
  bases.push_back(new Derived(4, 4));
  bases.push_back(new Base(5));

  typedef foster::dynamic_cast_filtering_iterator<Base, Derived> iter;
  iter begin = iter(bases.begin(), bases.end());
  iter end   = iter(bases.end(), bases.end());

  Derived* d2 = *begin; ++begin;
  Derived* d4 = *begin; ++begin;
  EXPECT_EQ(2, d2->x);
  EXPECT_EQ(4, d4->x);
  EXPECT_TRUE(begin == end);
}

TEST(FilteringIterator, noneOfSome) {
  std::vector<Base*> bases;
  bases.push_back(new Base(1));
  bases.push_back(new Base(3));
  bases.push_back(new Base(5));

  typedef foster::dynamic_cast_filtering_iterator<Base, Derived> iter;
  iter begin = iter(bases.begin(), bases.end());
  iter end   = iter(bases.end(), bases.end());

  EXPECT_TRUE(begin == end);
}

TEST(FilteringIterator, none) {
  std::vector<Base*> bases;

  typedef foster::dynamic_cast_filtering_iterator<Base, Derived> iter;
  iter begin = iter(bases.begin(), bases.end());
  iter end   = iter(bases.end(), bases.end());

  EXPECT_TRUE(begin == end);
}

} // unnamed namespace

