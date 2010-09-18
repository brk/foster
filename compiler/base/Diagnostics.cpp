// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/InputFile.h"

namespace foster {

//virtual
DiagBase::~DiagBase() {
  if (color != llvm::raw_ostream::SAVEDCOLOR) {
    out.changeColor(color, true);
  }

  if (sourceFile) {
    out << sourceFile->getShortSuffixPath();
  } else if (sourceBuffer) {
    out << "{-memory-}";
  } else {
    out << "<unknown source file>";
  }

  if (sourceLoc.isValid()) {
    out << ":" << sourceLoc.line << ":" << sourceLoc.column;
  }

  out << ": " << levelstr;

  if (color != llvm::raw_ostream::SAVEDCOLOR) {
    out.resetColor();
  }

  out << ": " << msg.str() << '\n';
}

} // namespace foster

