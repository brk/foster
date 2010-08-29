// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_DIAGNOSTICS_H
#define FOSTER_DIAGNOSTICS_H

#include "base/SourceRange.h"

#include "llvm/Support/raw_ostream.h"

#include <string>

// Foster's diagnostics subsystem is inspired by Clang's,
// though with less emphasis on configurability and more
// emphasis on making it easy to mark and display errors.

namespace foster {

struct SourceRangeHighlighter {
  SourceRangeHighlighter(SourceRange r, SourceLocation c) : r(r), caret(c) {}

  SourceRange r;
  SourceLocation caret;
};

inline SourceRangeHighlighter show(const SourceRange& r) {
  return SourceRangeHighlighter(r, r.begin);
}

class DiagBase {
  std::string msgstr;
  const char* levelstr;
protected:
  llvm::raw_string_ostream msg;
  llvm::raw_ostream& out;
  const InputFile*       sourceFile;
  const InputTextBuffer* sourceBuffer;
  SourceLocation sourceLoc;

  explicit DiagBase(llvm::raw_ostream& out, const char* levelstr)
    : levelstr(levelstr), msg(msgstr), out(out),
      sourceFile(NULL), sourceBuffer(NULL), sourceLoc(-1, -1) {}
  virtual ~DiagBase();

  virtual void add(int64_t i) { msg << i; }
  virtual void add(const char* str) { msg << str; }
  virtual void add(const std::string& str) { msg << str; }
  virtual void add(const SourceRangeHighlighter& h) {
    sourceFile   = h.r.source;
    sourceBuffer = h.r.buf;
    if (sourceFile || sourceBuffer) {
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

private:
  DiagBase(const DiagBase&);
};

// TODO allow top-level code to re-route diagnostics info to other streams

// Error diagnostic builder
class EDiag : public DiagBase {
public:
  explicit EDiag() : DiagBase(llvm::errs(), "error") {}
  virtual ~EDiag();
private:
  EDiag(const EDiag&);
};

// Debug diagnostic builder
class DDiag : public DiagBase {
public:
  explicit DDiag() : DiagBase(llvm::outs(), "debug") {}
  virtual ~DDiag();
private:
  DDiag(const DDiag&);
};

} // namespace

#endif

