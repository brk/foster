// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/ADT/StringRef.h"
#include <vector>

#ifndef FOSTER_INPUT_TEXT_BUFFER_H
#define FOSTER_INPUT_TEXT_BUFFER_H

// InputTextBuffer is a wrapper around a llvm::MemoryBuffer
// with a cache of line offsets and lengths, thus providing
// a line-oriented view of a text buffer.

namespace llvm {
  class MemoryBuffer;
  namespace sys {
    class Path;
  }
}

namespace foster {

class InputTextBuffer {
  llvm::MemoryBuffer* buf;
  std::vector<llvm::StringRef> lineCache;
  void initializeLineCache();

public:
  // precondition: file specified by filePath exists, and is readable
  InputTextBuffer(const llvm::sys::Path& path);
  
  InputTextBuffer(const char* data, size_t length);

  llvm::MemoryBuffer* getMemoryBuffer() const { return buf; }
  llvm::StringRef getLine(int n) const;
};

} // namespace foster

#endif // header guard

