// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/Assert.h"
#include "base/PathManager.h"
#include "llvm/System/Path.h"
#include "llvm/Support/MemoryBuffer.h"

namespace foster {

InputFile::InputFile(const llvm::sys::Path& path) : path(path) {
  buf = llvm::MemoryBuffer::getFile(path.str());
  gPathManager.registerPath(path);
  initializeLineCache();
}

void InputFile::initializeLineCache() {
  const char* data = this->buf->getBufferStart();
  int currentLineStart = 0;
  int currentLineNumber = 0;
  int i = 0, e = this->buf->getBufferSize();
  while (i < e) {
    if (data[i] == '\n') {
      int len = i - currentLineStart;
      llvm::StringRef line = llvm::StringRef(&data[currentLineStart], len);
      this->lineCache.push_back(line);

      ++currentLineNumber;
      currentLineStart = i + 1;
    }
    ++i;
  }

  if (data[i-1] != '\n') {
    int len = (i - 1) - currentLineStart;
    this->lineCache.push_back(llvm::StringRef(&data[currentLineStart], len));
  }
}

llvm::StringRef InputFile::getLine(int n) const {
  ASSERT(n < lineCache.size());
  return this->lineCache[n];
}

std::string InputFile::getShortSuffixPath() const {
  return gPathManager.getShortestUnambiguousSuffix(path);
}

} // namespace foster
