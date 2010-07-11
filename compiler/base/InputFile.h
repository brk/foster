// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/ADT/StringRef.h"
#include <vector>

#ifndef FOSTER_INPUT_FILE_H
#define FOSTER_INPUT_FILE_H

namespace llvm {
  class MemoryBuffer;
  namespace sys {
    class Path;
  }
}

namespace foster {

class InputFile {
  const llvm::sys::Path& path;
  llvm::MemoryBuffer* buf;
  std::vector<llvm::StringRef> lineCache;
  void initializeLineCache();

public:
  // precondition: file specified by filePath exists, and is readable
  InputFile(const llvm::sys::Path& path);

  llvm::MemoryBuffer* getBuffer() const { return buf; }
  const llvm::sys::Path& getPath() const { return path; }
  std::string getShortSuffixPath() const;
  llvm::StringRef getLine(int n) const;
};

}

#endif
