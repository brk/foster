// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_SOURCERANGE_H
#define FOSTER_SOURCERANGE_H

#include <iosfwd>

namespace llvm {
  class raw_ostream;
}

namespace foster {

class InputFile;
class InputTextBuffer;

// Maintaining a global pointer to the current input file is a convenient
// alternative to threading the current input file through ExprAST_from()
// call graph in ANTLRtoFosterAST.cpp.
extern const foster::InputFile* gInputFile;
extern const foster::InputTextBuffer* gInputTextBuffer;

struct SourceLocation {
  int line, column;
  SourceLocation(int line, int column) : line(line), column(column) {}

  bool isValid() const { return (SourceLocation(0, 0) < *this) && column >= 0; }
  bool operator<(const SourceLocation& o) const {
    return (line < o.line || (line == o.line && column < o.column));
  }
  bool operator==(const SourceLocation& o) const {
    return line == o.line && column == o.column;
  }
  bool operator!=(const SourceLocation& o) const {
    return !(o == *this);
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
  const foster::InputTextBuffer* buf;

  SourceRange(const foster::InputFile* source,
              foster::SourceLocation begin,
              foster::SourceLocation end,
              const foster::InputTextBuffer* buf = 0);

  bool isValid() const;
  bool isJustStartLocation() const;
  bool isEmpty() const;
  bool isSingleLine() const;

  void highlightWithCaret(llvm::raw_ostream& out, SourceLocation caret) const;

  static SourceRange getEmptyRange() {
    return SourceRange(gInputFile,
              SourceLocation::getInvalidLocation(),
              SourceLocation::getInvalidLocation(), gInputTextBuffer);
  }
  bool operator==(const SourceRange& o) const {
    return (source == o.source) && end == o.end && begin == o.begin;
  }
  bool operator!=(const SourceRange& o) const {
    return !(o == *this);
  }
};

} // namespace foster

llvm::raw_ostream& operator <<(llvm::raw_ostream& out,
                               const foster::SourceRange& r);

std::ostream& operator <<(std::ostream& out, const foster::SourceRange& r);

#endif // header guard

