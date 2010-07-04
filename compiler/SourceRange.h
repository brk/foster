// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_SOURCERANGE_H
#define FOSTER_SOURCERANGE_H

#include "InputFile.h"

namespace foster {

// Maintaining a global pointer to the current input file is a convenient
// alternative to threading the current input file through ExprAST_from()
// call graph in ANTLRtoFosterAST.cpp.
extern InputFile* gInputFile;

struct SourceLocation {
  int line, column;
  SourceLocation(int line, int column) : line(line), column(column) {}
  bool operator<(const SourceLocation& o) const {
    return (line < o.line || (line == o.line && column < o.column));
  }
};


class SourceRange {
public:
  const foster::InputFile* source;
  const foster::SourceLocation begin;
  const foster::SourceLocation end;
  SourceRange(foster::InputFile* source,
              foster::SourceLocation begin,
              foster::SourceLocation end)
    : source(source), begin(begin), end(end) {}
  bool empty() const { return !(begin < end); }
  bool isSingleLine() const { return begin.line == end.line; }
};
}

#endif // header guard

