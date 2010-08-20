// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "gtest/gtest.h"

#include "base/FreshNameGenerator.h"

namespace {

TEST(FreshNameGenerator, expectedSequenceAlone) {
  foster::FreshNameGenerator names;
  ASSERT_EQ("n", names.fresh("n"));
  ASSERT_EQ("n1", names.fresh("n"));
  ASSERT_EQ("n2", names.fresh("n"));
}

TEST(FreshNameGenerator, templateHandlingBasic) {
  foster::FreshNameGenerator names;
  ASSERT_EQ("n_0_x", names.fresh("n_%d_x"));
  ASSERT_EQ("n_1_x", names.fresh("n_%d_x"));
  ASSERT_EQ("n_2_x", names.fresh("n_%d_x"));
}

TEST(FreshNameGenerator, templateHandlingMultipleSlots) {
  foster::FreshNameGenerator names;
  ASSERT_EQ("n_0_%d_x", names.fresh("n_%d_%d_x"));
  ASSERT_EQ("n_1_%d_x", names.fresh("n_%d_%d_x"));
}

TEST(FreshNameGenerator, noCrossSourceInterference) {
  foster::FreshNameGenerator namesA;
  foster::FreshNameGenerator namesB;
  ASSERT_EQ("n", namesA.fresh("n"));
  ASSERT_EQ("n1", namesA.fresh("n"));
  ASSERT_EQ("n2", namesA.fresh("n"));


  ASSERT_EQ("n", namesB.fresh("n"));
  ASSERT_EQ("n1", namesB.fresh("n"));
  ASSERT_EQ("n2", namesB.fresh("n"));
}

TEST(FreshNameGenerator, noIntraSourceInterference) {
  foster::FreshNameGenerator names;
  ASSERT_EQ("n", names.fresh("n"));
  ASSERT_EQ("k", names.fresh("k"));
  ASSERT_EQ("n1", names.fresh("n"));
  ASSERT_EQ("k1", names.fresh("k"));
}

} // unnamed namespace
