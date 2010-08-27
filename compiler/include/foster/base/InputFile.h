// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/ADT/StringRef.h"
#include <vector>
#include <string>

#ifndef FOSTER_INPUT_FILE_H
#define FOSTER_INPUT_FILE_H

namespace llvm {
  namespace sys {
    class Path;
  }
}

namespace foster {

class InputTextBuffer;
  
class InputFile {
  const llvm::sys::Path& path;
  InputTextBuffer* buf;

public:
  // precondition: file specified by filePath exists, and is readable
  InputFile(const llvm::sys::Path& path);

  InputTextBuffer* getBuffer() const { return buf; }
  const llvm::sys::Path& getPath() const { return path; }
  std::string getShortSuffixPath() const;
};

class InputFileRegistry {
public:
  InputFileRegistry();
  InputFile* getOrCreateInputFileForAbsolutePath(const llvm::sys::Path& path);

private:
  struct Impl; Impl* impl;
};

extern InputFileRegistry gInputFileRegistry;

} // namespace foster

#endif
