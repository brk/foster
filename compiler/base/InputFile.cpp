// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "base/PathManager.h"
#include "llvm/System/Path.h"

#include <map>
#include <string>

namespace foster {

InputFile::InputFile(const llvm::sys::Path& path) : path(path) {
  buf = new InputTextBuffer(path);
}

std::string InputFile::getShortName() const {
  if (!this) {
    return "<unknown file>";
  }

  return path.str();
}

////////////////////////////////////////////////////////////////////

struct InputFileRegistry::Impl {
  std::map<std::string, InputFile*> inputFileFor;
};


InputFileRegistry gInputFileRegistry;


InputFile* InputFileRegistry::getOrCreateInputFileForAbsolutePath(
                                                const llvm::sys::Path& path) {
  InputFile* rv = impl->inputFileFor[path.str()];
  if (!rv) {
    impl->inputFileFor[path.str()] = rv = new InputFile(path);
  }
  return rv;
}

InputFileRegistry::InputFileRegistry() {
  impl = new InputFileRegistry::Impl();
}

} // namespace foster
