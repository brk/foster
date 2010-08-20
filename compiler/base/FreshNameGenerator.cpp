// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/FreshNameGenerator.h"

#include <map>
#include <sstream>

namespace foster {

struct FreshNameGenerator::Impl {
  std::map<std::string, size_t> counts;
};

FreshNameGenerator::FreshNameGenerator() {
  impl = new Impl();
}

std::string FreshNameGenerator::fresh(std::string like) {
  std::stringstream ss;
  size_t pos = like.find("%d", 0);
  size_t curr = impl->counts[like]++;
  if (std::string::npos == pos) { // append uniquifier, if any
    if (curr == 0) {
      ss << like; // Only append integer when we see second copy of symbol
    } else {
      ss << like << curr;
    }
  } else { // If it's a template, make the substitution, even the first time
    ss << curr; // int>string
    like.replace(pos, 2, ss.str());
    ss.str("");
    ss.clear(); // reset
    ss << like;
  }
  return ss.str();
}

} // namespace foster
