// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Support/MemoryBuffer.h"

#ifndef FOSTER_INPUT_FILE_H
#define FOSTER_INPUT_FILE_H

namespace foster {

class InputFile {
  llvm::MemoryBuffer* buf;
  const std::string& filePath;
public:
  // precondition: file specified by filePath exists, and is readable
  InputFile(const std::string& filePath) : filePath(filePath) {
    buf = llvm::MemoryBuffer::getFile(filePath);
  }

  llvm::MemoryBuffer* getBuffer() const { return buf; }
  const std::string& getFilePath() const { return filePath; }
};

}

#endif
