// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Path.h"

#ifndef FOSTER_INPUT_FILE_H
#define FOSTER_INPUT_FILE_H

namespace foster {

class InputTextBuffer;

class InputFile {
  std::string path;
  InputTextBuffer* buf;

public:
  // precondition: file specified by filePath exists, and is readable
  InputFile(std::string path);

  InputTextBuffer* getBuffer() const { return buf; }
  const std::string& getPath() const { return path; }
};

std::string getShortName(const InputFile*);

} // namespace foster

#endif
