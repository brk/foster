// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"

#include "llvm/Support/Path.h"

#include <map>
#include <string>

namespace foster {

InputFile::InputFile(llvm::sys::Path path) : path(path) {
  buf = new InputTextBuffer(path);
}

std::string InputFile::getShortName() const {
  if (!this) {
    return "<unknown file>";
  }

  return path.str();
}

} // namespace foster
