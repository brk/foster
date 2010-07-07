// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_DIAGNOSTICS_H
#define FOSTER_DIAGNOSTICS_H

// Foster's diagnostics subsystem is inspired by Clang's,
// though with less emphasis on configurability and more
// emphasis on making it easy to mark and display errors.

namespace foster {

struct SourceRangeHighlighter {
  SourceRangeHighlighter(SourceRange r, SourceLocation c) : r(r), caret(c) {}

  SourceRange r;
  SourceLocation caret;
};

SourceRangeHighlighter show(ExprAST* ast) {
  if (!ast) {
    SourceLocation empty = SourceLocation::getInvalidLocation();
    return SourceRangeHighlighter(SourceRange(NULL, empty, empty), empty);
  }
  SourceRangeHighlighter h(ast->sourceRange, ast->sourceRange.begin);
  return h;
}

class DiagBase {
  std::string msgstr;
  const char* levelstr;
protected:
  llvm::raw_string_ostream msg;
  llvm::raw_ostream& out;
  const InputFile* sourceFile;
  SourceLocation sourceLoc;

  DiagBase(llvm::raw_ostream& out, const char* levelstr)
    : levelstr(levelstr), msg(msgstr), out(out), sourceFile(NULL), sourceLoc(-1, -1) {}
  ~DiagBase() {
    const InputFile* source = (sourceFile ? sourceFile : gInputFile);
    out << source->getFilePath();
    if (sourceLoc.isValid()) {
      out << ":" << sourceLoc.line << ":" << sourceLoc.column;
    }
    out << ": " << levelstr
        << ": " << msg.str() << '\n';
  }

  virtual void add(int64_t i) { msg << i; }
  virtual void add(const char* str) { msg << str; }
  virtual void add(const std::string& str) { msg << str; }
  virtual void add(const SourceRangeHighlighter& h) {
    if (h.r.source) {
      sourceFile = h.r.source;
      sourceLoc  = h.caret;
      msg << '\n';
      h.r.highlightWithCaret(msg, h.caret);
    }
  }
public:
  DiagBase& operator<<(int64_t i) { add(i); return *this; }
  DiagBase& operator<<(const char* str) { add(str); return *this; }
  DiagBase& operator<<(const std::string& str) { add(str); return *this; }
  DiagBase& operator<<(const SourceRangeHighlighter& h) { add(h); return *this; }
};

// Error diagnostic builder
class EDiag : public DiagBase {
public:
  EDiag() : DiagBase(llvm::errs(), "error") {}
  ~EDiag() {}
};

} // namespace

#endif

