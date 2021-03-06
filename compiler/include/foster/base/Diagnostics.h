// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_DIAGNOSTICS_H
#define FOSTER_DIAGNOSTICS_H

#include "base/SourceRange.h"

#include "llvm/Support/raw_ostream.h"

#include <set>
#include <string>

// Foster's diagnostics subsystem is inspired by Clang's,
// though with less emphasis on configurability and more
// emphasis on making it easy to mark and display errors.

namespace foster {

  // For want of a better place to put them...
  extern bool gDebugLoggingEnabled;
  extern std::set<std::string> gEnabledDebuggingTags;

  llvm::raw_ostream& dbg(const std::string& tag);


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
  llvm::raw_ostream::Colors color;
  const InputFile*       sourceFile;
  const InputTextBuffer* sourceBuffer;
  SourceLocation sourceLoc;

  explicit DiagBase(llvm::raw_ostream& out, const char* levelstr)
  : levelstr(levelstr), msg(msgstr), out(out),
    color(llvm::raw_ostream::SAVEDCOLOR),
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
  DiagBase& operator<<(llvm::StringRef str) { add(str.str()); return *this; }
  DiagBase& operator<<(const std::string& str) { add(str); return *this; }
  DiagBase& operator<<(const SourceRangeHighlighter& h) { add(h); return *this; }
  // TODO support std::error_code

private:
  DiagBase(const DiagBase&);
};

////////////////////////////////////////////////////////////////////

// Error diagnostic builder that always outputs to stderr.
class SimpleEDiag : public DiagBase {
public:
  explicit SimpleEDiag() : DiagBase(llvm::errs(), "error") {}
  ~SimpleEDiag() {}
private:
  SimpleEDiag(const SimpleEDiag&);
};

////////////////////////////////////////////////////////////////////

// Error diagnostic builder; unlike foster::SimpleEDiag, can be re-routed.
class EDiag : public DiagBase {
public:
  explicit EDiag();
  virtual ~EDiag();
private:
  EDiag(const EDiag&);
};

// Debug diagnostic builder
class DDiag : public DiagBase {
public:
  explicit DDiag(llvm::raw_ostream::Colors _color)
        : DiagBase(llvm::errs(), "debug") {
    this->color = _color;
  }
  explicit DDiag() : DiagBase(llvm::errs(), "debug") {}
  virtual ~DDiag();
private:
  DDiag(const DDiag&);
};

} // namespace foster

#endif

