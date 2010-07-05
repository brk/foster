// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "SourceRange.h"

#include <ostream>

namespace foster {

const InputFile* gInputFile;


bool SourceRange::isValid() const {
  // We assume that invalid ranges will also be empty,
  // so we don't need to explicitly test for invalid line numbers.
  return begin < end;
}

bool SourceRange::isJustStartLocation() const {
  return !isValid() && begin.isValid();
}

bool SourceRange::isEmpty() const {
  return !isValid() && !begin.isValid();
}

bool SourceRange::isSingleLine() const {
  return begin.line == end.line && begin.line >= 0;
}

}

std::ostream& operator <<(std::ostream& out, const foster::SourceRange& r) {
  const foster::InputFile* f = r.source;
  if (r.isEmpty()) {
    out << "<" << r.source->getFilePath()
        << ":" << r.begin.line << "::" << r.begin.column
        << " - " << r.end.line << "::" << r.end.column << ">";
  } else if (r.isSingleLine()) {
    llvm::StringRef line = r.source->getLine(r.begin.line);
    out << line.str() << "\n";
    for (int i = 0; i < r.end.column; ++i) {
      if (i < r.begin.column) {
        out << ' ';
      } else if (i == r.begin.column) {
        out << '^';
      } else {
        out << '~';
      }
    }
  } else {
    out << "<" << r.source->getFilePath()
        << ":" << r.begin.line << "::" << r.begin.column
        << " - " << r.end.line << "::" << r.end.column << ">";
  }
  return out;
}
