// Copyright (c) 2020 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/ADT/Statistic.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"

#include "base/LLVMUtils.h"
#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "base/TimingsRepository.h"

#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"

#include <fstream>
#include <string>
#include <sstream>
#include <iostream>

// Usage:
//        fingerprint-antlr [--shallow] <rootfile.foster>
// Input: a path to a Foster source file.
//
// Prints a list of each Foster source file visited, along with its hash.
// If --shallow is passed, only fingerprints a single file; otherwise,
// recursively visits each file in the dependency graph.

using namespace llvm;
using std::string;

using foster::EDiag;
using foster::ScopedTimer;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::list<string>
optIncludePath("I", cl::desc("Path to search for includes"),
                    cl::value_desc("include path"));

static cl::opt<bool>
optShallow("shallow",
  cl::desc("[foster] Only fingerprint a single input file."));

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("[foster] Print timing measurements of compiler passes"));


void setTimingDescriptions() {
  using foster::gTimings;
  gTimings.describe("total", "Overall compiler runtime (ms)");

  gTimings.describe("read", "Time spent reading input file (ms)");
  gTimings.describe("hash", "Time spent hashing (ms)");
}

void process(llvm::StringRef buffer, std::string path) {
    uint64_t h = 0;
    { ScopedTimer timer("hash");
      h = CityHash64(buffer.data(), buffer.size());
    }
    char buf[64] = {0};
    sprintf(buf, "%016" PRIx64 , h);
    llvm::outs() << buf << " " << path << "\n";
}

std::string slurpInput() {
  std::ios_base::sync_with_stdio(false);
  std::stringstream ss;
  std::string line;
  while (std::cin) { getline(std::cin, line); ss << line << "\n"; }
  return ss.str();
}

int main(int argc, char** argv) {
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster fingerprinter\n");

  uint64_t numlines = 0;
  uint64_t numbytes = 0;

  if (optShallow) {
    llvm::StringRef b;
    const foster::InputFile* infile;
    {
        ScopedTimer timer("read");
        infile = new foster::InputFile(optInputPath);
        b = infile->getBuffer()->getMemoryBuffer()->getBuffer();
    }
    process(b, infile->getPath());
    numbytes += b.size();
    numlines += infile->getBuffer()->getLineCount();
    delete infile;

    llvm::outs() << numlines << " lines " << numbytes << " bytes" << "\n";
  } else {
    foster::validateInputFile(optInputPath);
    const foster::InputFile infile(optInputPath);

    unsigned numParseErrors = 0;

    foster::ParsingContext::pushNewContext();

    InputWholeProgram* pgmAST = foster::parseWholeProgram(infile, optIncludePath, &numParseErrors);

    if (numParseErrors > 0) {
        EDiag() << "Encountered " << numParseErrors << " parsing errors; exiting."
                << (pgmAST ? " (with AST)" : " (without AST");
        return 3;
    } else if (!pgmAST) {
        return 4;
    }

    for (int i = 0; i < pgmAST->getModuleCount(); ++i) {
      auto m = pgmAST->getInputModule(i)->source;
      llvm::StringRef b = m->getBuffer()->getMemoryBuffer()->getBuffer();
      process(b, m->getPath());
      numbytes += b.size();
      numlines += m->getBuffer()->getLineCount();
    }

    llvm::outs() << pgmAST->getModuleCount() << " files " << numlines << " lines " << numbytes << " bytes" << "\n";
  }

  if (optPrintTimings) {
    //setTimingDescriptions();
    foster::gTimings.print("fingerprint-antlr");
  }

  return 0;
}
