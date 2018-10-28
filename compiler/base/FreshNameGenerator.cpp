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
  size_t curr = impl->counts[like]++;
  std::stringstream ss; ss << like;
  if (curr > 0) { ss << curr; }
  return ss.str();
}

} // namespace foster
