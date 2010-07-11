// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "gtest/gtest.h"

#include "base/Assert.h"

namespace {

TEST(FosterAssert, dies) {
  ::testing::FLAGS_gtest_death_test_style = "threadsafe";
  ASSERT_DEATH( { ASSERT(false) << "blah"; }  ,  "blah" );
}

} // unnamed namespace
