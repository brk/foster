// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"

namespace foster {

//virtual
DiagBase::~DiagBase() {
  const InputFile* source = (sourceFile ? sourceFile : gInputFile);
  if (source) {
    out << source->getShortSuffixPath();
  } else {
    out << "<unknown source file>";
  }

  if (sourceLoc.isValid()) {
    out << ":" << sourceLoc.line << ":" << sourceLoc.column;
  }
  out << ": " << levelstr
      << ": " << msg.str() << '\n';
}

EDiag::~EDiag() {}

} // namespace foster

