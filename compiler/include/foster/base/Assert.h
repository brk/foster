// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_ASSERT_H
#define FOSTER_ASSERT_H

#include "base/Diagnostics.h"

#include <string>

#define ASSERT(cond) \
  (cond) \
    ? foster::getNullDiag() \
    : foster::DiagWrapper(__FILE__, __LINE__, __PRETTY_FUNCTION__, #cond).getDiag()

namespace foster {

class DiagWrapper {
  struct Impl; Impl* impl;
public:
  DiagWrapper(const char* file, int line,
             const char* func, const char* cond);

  foster::DiagBase& getDiag();

  ~DiagWrapper();
};

foster::DiagBase& getNullDiag();

} // namespace foster

#endif
