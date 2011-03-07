// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/InputFile.h"

#include "llvm/Support/raw_ostream.h"

#include <vector>

namespace {
  class OStreamStack {
    std::vector<llvm::raw_ostream*> outs;
    std::vector<llvm::raw_ostream*> errs;

    std::vector<llvm::raw_string_ostream*> sstreams;
    std::vector<std::string*> strings;

  public:
    void pushOuts(llvm::raw_ostream* out) { this->outs.push_back(out); }
    void pushErrs(llvm::raw_ostream* out) { this->errs.push_back(out); }
    void popOuts() { outs.pop_back(); }
    void popErrs() { errs.pop_back(); }

    llvm::raw_ostream& currentOuts() {
      if (this->outs.empty()) { return llvm::outs(); }
      return *(this->outs.back());
    }
    llvm::raw_ostream& currentErrs() {
      if (this->errs.empty()) { return llvm::errs(); }
      return *(this->errs.back());
    }

    void startAccumulatingOutputToString() {
      std::string* s = new std::string();
      strings.push_back(s);
      sstreams.push_back(new llvm::raw_string_ostream(*s));
    }

    std::string collectAccumulatedOutput() {
      llvm::raw_string_ostream* ss = sstreams.back(); sstreams.pop_back();
      std::string str = ss->str();
      delete ss;
      std::string* s = strings.back(); strings.pop_back();
      delete s;
      return str;
    }

  };
} // unnamed namespace

namespace foster {
  static OStreamStack sOstreams;
  llvm::raw_ostream& currentErrs() { return sOstreams.currentErrs(); }
  llvm::raw_ostream& currentOuts() { return sOstreams.currentOuts(); }

  void startAccumulatingOutputToString() {
    sOstreams.startAccumulatingOutputToString();
  }

  std::string collectAccumulatedOutput() {
    return sOstreams.collectAccumulatedOutput();
  }

  bool gDebugLoggingEnabled = true;
  std::set<std::string> gEnabledDebuggingTags;

  llvm::raw_ostream& dbg(const std::string& tag) {
    if (foster::gDebugLoggingEnabled
      && (gEnabledDebuggingTags.empty()
       || gEnabledDebuggingTags.count(tag) == 1)) {
    return currentOuts() << "\t" << tag << ":\t";
    }
    return llvm::nulls();
  }

  EDiag::EDiag() : DiagBase(foster::currentErrs(), "error") {
    color = llvm::raw_ostream::RED;
  }

  EDiag::~EDiag() {
    // Note: error diagnostics from __COMPILES__ will be discarded, not deleted!
  }

////////////////////////////////////////////////////////////////////

DDiag::~DDiag() {}

////////////////////////////////////////////////////////////////////

  //virtual
  DiagBase::~DiagBase() {
    if (color != llvm::raw_ostream::SAVEDCOLOR) {
      out.changeColor(color, true);
    }

    if (sourceFile) {
      out << sourceFile->getShortName();
    } else if (sourceBuffer) {
      out << "{-memory-}";
    } else {
      out << "<unknown source file>";
    }

    if (sourceLoc.isValid()) {
      out << ":" << sourceLoc.line << ":" << sourceLoc.column;
    }

    out << ": " << levelstr;

    if (color != llvm::raw_ostream::SAVEDCOLOR) {
      out.resetColor();
    }

    out << ": " << msg.str() << '\n';
  }

} // namespace foster
