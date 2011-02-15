// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_FRESH_NAME_GENERATOR_H
#define FOSTER_FRESH_NAME_GENERATOR_H

#include <string>

namespace foster {

class FreshNameGenerator {
public:
  FreshNameGenerator();

  /// Generates a unique name given a base string;
  /// each template gets a separate sequence of
  /// uniquifying numbers appended to it.
  std::string fresh(std::string like);

private:
  struct Impl;
  Impl* impl;
};

} // namespace foster

#endif
