// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_BASE_TIMINGS_REPOSITORY
#define FOSTER_BASE_TIMINGS_REPOSITORY

#include "llvm/System/DataTypes.h"

#include <map>
#include <string>

using std::string;

namespace foster {

class TimingsRepository {
  std::map<string, uint64_t> totals;
  std::map<string, uint64_t> locals;
  std::map<string, string> descriptions;

public:
  void describe(string path, string desc) {
    descriptions[path] += desc;
  }

  void incr(const char* dottedpath, uint64_t n);
  void print();
};

} // namespace foster

#endif // include guard
