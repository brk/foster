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
    : levelstr(levelstr), msg(msgstr), out(out), sourceLoc(-1, -1) {}
  ~DiagBase() {
    if (sourceFile) {
       out << sourceFile->getFilePath()
           << ":" << sourceLoc.line << ":" << sourceLoc.column
           << ": " << levelstr
           << ": " << msg.str() << '\n';
    } else { out << msg.str() << '\n';  }
  }

  virtual void add(const char* str) { msg << str; }
  virtual void add(const SourceRangeHighlighter& h) {
    sourceFile = h.r.source;
    sourceLoc  = h.caret;
    msg << '\n';
    h.r.highlightWithCaret(msg, h.caret);
  }
public:
  DiagBase& operator<<(const char* str) { add(str); return *this; }
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

