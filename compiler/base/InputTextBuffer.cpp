// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/InputTextBuffer.h"

#include "llvm/ADT/OwningPtr.h"
#include "llvm/Support/MemoryBuffer.h"

using llvm::MemoryBuffer;
using llvm::StringRef;

#include "llvm/Support/Path.h"
#include "llvm/Support/system_error.h"
using llvm::error_code;

namespace foster {

struct InputTextBuffer::Impl {
  llvm::OwningPtr<MemoryBuffer> buf;
  std::vector<StringRef> lineCache;

  void initializeLineCache() {
    const char* data = buf->getBufferStart();
    ASSERT(data != NULL);
    int currentLineStart = 0;
    int currentLineNumber = 0;
    int i = 0, e = buf->getBufferSize();
    while (i < e) {
      if (data[i] == '\n') {
        int len = i - currentLineStart;
        StringRef line = StringRef(&data[currentLineStart], len);
        this->lineCache.push_back(line);

        ++currentLineNumber;
        currentLineStart = i + 1;
      }
      ++i;
    }

    if (data[i-1] != '\n') {
      int len = i - currentLineStart;
      this->lineCache.push_back(StringRef(&data[currentLineStart], len));
    }
  }

  Impl(MemoryBuffer* buf) : buf(buf) {
    ASSERT(buf != NULL);
    initializeLineCache();
  }
};

InputTextBuffer::InputTextBuffer(const llvm::sys::Path& path) {
  llvm::OwningPtr<MemoryBuffer> membuf;
  error_code err = MemoryBuffer::getFile(path.str(), membuf);
  ASSERT(!err) << "error message is: " << err.message();
  impl = new Impl(membuf.take());
}

InputTextBuffer::InputTextBuffer(const char* data, size_t length) {
  impl = new Impl(MemoryBuffer::getMemBufferCopy(StringRef(data, length)));
}

MemoryBuffer*
InputTextBuffer::getMemoryBuffer() const {
  return impl->buf.get();
}

StringRef
InputTextBuffer::getLine(int n) const {
  ASSERT(n >= 0 && n < this->getLineCount())
        << "can't get line " << n << " of " << this->getLineCount();
  return impl->lineCache[n];
}

int
InputTextBuffer::getLineCount() const {
  return impl->lineCache.size();
}

} // namespace foster
