// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "gtest/gtest.h"

#include "base/SourceRange.h"

using foster::SourceRange;
using foster::SourceLocation;

namespace {

TEST(SourceRange, emptyRangeIsNotValid) {
  EXPECT_FALSE(SourceRange(NULL, SourceLocation(-1, -1), SourceLocation(-1, -1))
      .isValid());

  EXPECT_FALSE(SourceRange::getEmptyRange().isValid());
}

TEST(SourceRange, rangeOperators) {
  EXPECT_EQ(SourceRange(NULL, SourceLocation(-1, -1), SourceLocation(-1, -1))
           , SourceRange::getEmptyRange());

  EXPECT_EQ(SourceRange::getEmptyRange()
           , SourceRange(NULL, SourceLocation(-1, -1), SourceLocation(-1, -1)));

  EXPECT_FALSE(SourceRange(NULL, SourceLocation(-1, -1), SourceLocation(-1, -1))
           != SourceRange::getEmptyRange());

  EXPECT_NE(SourceRange(NULL, SourceLocation(99, -1), SourceLocation(-1, -1))
           , SourceRange::getEmptyRange());

  EXPECT_FALSE(SourceRange(NULL, SourceLocation(99, -1), SourceLocation(-1, -1))
            == SourceRange::getEmptyRange());
}

} // unnamed namespace

