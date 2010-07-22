// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_CHECK_H
#define FOSTER_CHECK_H

#include "base/Diagnostics.h"
#include <cstdlib>

#define ASSERT(cond) \
  (cond) \
    ? foster::DiagIgnore::get() \
    : foster::DiagWrapper(__FILE__, __LINE__, __PRETTY_FUNCTION__, #cond).getDiag()

namespace foster {

class DiagWrapper {
  foster::EDiag* diag;
public:
  DiagWrapper(const char* file, int line,
             const char* func, const char* cond);

  foster::DiagBase& getDiag() { return *diag; }

  ~DiagWrapper();
};


class DiagIgnore : public DiagBase {
public:
  static DiagBase& get() { static DiagIgnore d; return d; }

private:
  DiagIgnore() : DiagBase(llvm::nulls(), "none") {}
  ~DiagIgnore();

protected:
  virtual void add(int64_t i) {}
  virtual void add(const char* str) {}
  virtual void add(const std::string& str) {}
  virtual void add(const SourceRangeHighlighter& h) {}
};

} // namespace foster

#endif
