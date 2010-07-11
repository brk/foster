// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/SourceRange.h"

namespace foster {

const InputFile* gInputFile;

static void fixupLocation(const InputFile* source, SourceLocation& loc) {
  if (loc.line > 0) { loc.line--; }
  loc.column = source->getLine(loc.line).size() - 1;
}

SourceRange::SourceRange(const InputFile* source,
                         SourceLocation abegin,
                         SourceLocation aend)
    : source(source), begin(abegin), end(aend) {
  // In error situations, ANTLR will sometimes give us invalid
  // line/column information, such as providing 2/-1
  // instead of 1/endofline1.
  // We do fixup here so that we know the length of the previous line.
  if (begin.line >= 0 && begin.column == -1) {
    fixupLocation(source, const_cast<SourceLocation&>(begin));
    const_cast<SourceLocation&>(end) = begin;
  }
  if (end.line >= 0 && end.column == -1) {
    fixupLocation(source, const_cast<SourceLocation&>(end));
  }
}

bool SourceRange::isValid() const {
  return begin < end && begin.isValid() && end.isValid();
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

void SourceRange::highlightWithCaret(llvm::raw_ostream& out,
                                     SourceLocation caret) const {
  if (isEmpty()) {
    out << "<" << source->getFilePath()
        << ":" << begin.line << "::" << begin.column
        << " - " << end.line << "::" << end.column << " (empty)>";
  } else if (isSingleLine()) {
    llvm::StringRef line = source->getLine(begin.line);
    out << line.str() << "\n";

    // The end of the range should, by definition, be after the start..
    int endcol = (end.column > begin.column) ? end.column : begin.column + 1;
    // We should try to include the caret...
    if (endcol <= caret.column) endcol = caret.column + 1;
    // ... but not such that we color outside the lines.
    endcol = (std::min)(endcol, (int) line.size());

    for (int i = 0; i < endcol; ++i) {
      if (i < begin.column) {
        out << ' ';
      } else if (i == caret.column) {
        out << '^';
      } else if (i < endcol) {
        out << '~';
      }
    }
    out << "\n";
  } else {
    out << "<" << source->getFilePath()
        << ":" << begin.line << "::" << begin.column
        << " - " << end.line << "::" << end.column << ">";
  }
}

} // namespace foster

