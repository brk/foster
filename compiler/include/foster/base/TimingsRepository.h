// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_BASE_TIMINGS_REPOSITORY
#define FOSTER_BASE_TIMINGS_REPOSITORY

#include "base/LLVMUtils.h"

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
  void print(const std::string& title);
};

extern TimingsRepository gTimings;

struct ScopedTimer {
  ScopedTimer(const char* stat)
     : stat(stat), start(llvm::sys::TimeValue::now()) {}
  ~ScopedTimer() {
    llvm::sys::TimeValue end = llvm::sys::TimeValue::now();
    gTimings.incr(stat, (end - start).msec());
  }
private:
  const char* stat;
  llvm::sys::TimeValue start;
};

} // namespace foster

#endif // include guard
