// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_CHECK_H
#define FOSTER_CHECK_H

#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

#define ASSERT(cond) \
  (cond) \
    ? llvm::nulls() \
    : foster::LogWrapper(llvm::errs(), __FILE__, __LINE__, __PRETTY_FUNCTION__, #cond).get_raw_ostream()

namespace foster {

class LogWrapper {
  llvm::raw_ostream& out;
public:
  LogWrapper(llvm::raw_ostream& out, const char* file, int line,
             const char* func, const char* cond) : out(out) {
    out << file << ":" << line << ": ASSERT(" << cond << ") failed. ";
  }

  llvm::raw_ostream& get_raw_ostream() { return out; }

  ~LogWrapper() { out << "\n"; abort(); }
};

} // namespace foster

#endif
