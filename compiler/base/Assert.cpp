// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include <cstdlib> // for abort()

#include "llvm/Support/raw_ostream.h"

namespace foster {

struct DiagWrapper::Impl {
  foster::SimpleEDiag* diag;
};

foster::DiagBase& DiagWrapper::getDiag() { return *(impl->diag); }

DiagWrapper::DiagWrapper(const char* file, int line,
                         const char* func, const char* cond) {
  impl = new Impl();
  impl->diag = new foster::SimpleEDiag();
  //getDiag().changeColor(llvm::raw_ostream::RED);
  getDiag() << file << ":" << line << ": ASSERT(" << cond << ") failed. ";
  //getDiag().resetColor();
}

DiagWrapper::~DiagWrapper() {
  getDiag() << "\n";
  delete impl->diag;
  delete impl;
  abort();
}


class DiagIgnore : public DiagBase {
public:
  static DiagBase& get() { static DiagIgnore d; return d; }

private:
  DiagIgnore() : DiagBase(llvm::nulls(), "none") {}
  ~DiagIgnore() {}

protected:
  virtual void add(int64_t i) {}
  virtual void add(const char* str) {}
  virtual void add(const std::string& str) {}
  virtual void add(const SourceRangeHighlighter& h) {}

  friend foster::DiagBase& getNullDiag();
};

foster::DiagBase& getNullDiag() { static DiagIgnore s; return s; }

} // namespace foster

