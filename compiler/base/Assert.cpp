// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "llvm/Support/raw_ostream.h"

namespace foster {

DiagWrapper::DiagWrapper(const char* file, int line,
             const char* func, const char* cond) {
  diag = new foster::EDiag();
  getDiag() << file << ":" << line << ": ASSERT(" << cond << ") failed. ";
}

DiagWrapper::~DiagWrapper() {
  getDiag() << "\n";
  delete diag;
  abort();
}

DiagIgnore::~DiagIgnore() {}


} // namespace foster

