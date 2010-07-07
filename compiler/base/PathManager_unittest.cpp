// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/PathManager.h"
#include "gtest/gtest.h"

// hack to avoid making a separate static library to link to
#include "base/PathManager.cpp"

using foster::PathManager;
using llvm::sys::Path;

namespace {

TEST(PathManager, singleEntryReturnsLastPart) {
  PathManager pm;
  Path p("first/second/last.suffix");
  pm.registerPath(p);
  EXPECT_EQ("last.suffix",
    pm.getShortestUnambiguousSuffix(p));
}

TEST(PathManager, unregisteredReturnsWholePath) {
  PathManager pm;
  std::string pstr("first/second/last.suffix");
  Path p(pstr);
  // no path registration
  EXPECT_EQ(pstr,
    pm.getShortestUnambiguousSuffix(p));
}

TEST(PathManager, returnsWholePathComponents) {
  PathManager pm;
  Path p("first/second/last.suffix");
  pm.registerPath(p);
  pm.registerPath(Path("Xond/last.suffix"));
  EXPECT_EQ("second/last.suffix",
    pm.getShortestUnambiguousSuffix(p));
}

TEST(PathManager, returnsWholePathComponents2) {
  PathManager pm;
  Path p("first/last.suffix");
  pm.registerPath(p);
  pm.registerPath(Path("Xst/last.suffix"));
  EXPECT_EQ("first/last.suffix",
    pm.getShortestUnambiguousSuffix(p));
}

TEST(PathManager, returnsWholePathComponents3) {
  PathManager pm;
  Path p("/first/last.suffix");
  pm.registerPath(p);
  pm.registerPath(Path("Xst/last.suffix"));
  EXPECT_EQ("/first/last.suffix",
    pm.getShortestUnambiguousSuffix(p));
}

} // unnamed namespace

