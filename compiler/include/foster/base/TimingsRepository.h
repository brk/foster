// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_BASE_TIMINGS_REPOSITORY
#define FOSTER_BASE_TIMINGS_REPOSITORY

#include "llvm/Support/DataTypes.h"
#include "llvm/Support/Path.h"

#include <map>
#include <string>
#include <chrono>

using std::string;

namespace foster {

class TimingsRepository {
  std::map<string, uint64_t> total_us;
  std::map<string, uint64_t> local_us;
  std::map<string, string> descriptions;

public:
  void describe(string path, string desc) {
    descriptions[path] += desc;
  }

  void incr(const char* dottedpath, uint64_t n);
  void print(const std::string& title);
};

extern TimingsRepository gTimings;

struct ScopedTimer {
  ScopedTimer(const char* stat)
     : stat(stat), start(std::chrono::high_resolution_clock::now()) {}
  ~ScopedTimer() {
    auto end = std::chrono::high_resolution_clock::now();
    auto usecs = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
    gTimings.incr(stat, usecs);
  }
private:
  const char* stat;
  std::chrono::time_point<std::chrono::high_resolution_clock> start;
};

} // namespace foster

#endif // include guard
