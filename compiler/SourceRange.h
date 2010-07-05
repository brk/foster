// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_SOURCERANGE_H
#define FOSTER_SOURCERANGE_H

#include "InputFile.h"

#include <ostream>

namespace foster {

// Maintaining a global pointer to the current input file is a convenient
// alternative to threading the current input file through ExprAST_from()
// call graph in ANTLRtoFosterAST.cpp.
extern const InputFile* gInputFile;

struct SourceLocation {
  int line, column;
  SourceLocation(int line, int column) : line(line), column(column) {}

  bool isValid() const { return SourceLocation(0, 0) < *this; }
  bool operator<(const SourceLocation& o) const {
    return (line < o.line || (line == o.line && column < o.column));
  }

  static SourceLocation getInvalidLocation() {
    return SourceLocation(-1, -1);
  }
};


class SourceRange {
public:
  const foster::InputFile* source;
  const foster::SourceLocation begin;
  const foster::SourceLocation end;

  SourceRange(const foster::InputFile* source,
              foster::SourceLocation begin,
              foster::SourceLocation end)
    : source(source), begin(begin), end(end) {}

  bool isValid() const;
  bool isJustStartLocation() const;
  bool isEmpty() const;
  bool isSingleLine() const;

  void highlightWithCaret(std::ostream& out, SourceLocation caret) const;

  static SourceRange getEmptyRange() {
    return SourceRange(gInputFile,
              SourceLocation::getInvalidLocation(),
              SourceLocation::getInvalidLocation());
  }
};
} // namespace foster

inline std::ostream& operator <<(std::ostream& out, const foster::SourceRange& r) {
  r.highlightWithCaret(out, r.begin);
  return out;
}

#endif // header guard

