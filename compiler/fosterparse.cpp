// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/ADT/Statistic.h"
#include "llvm/Support/CommandLine.h"

#include "base/LLVMUtils.h"
#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "base/TimingsRepository.h"

#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"

#include "passes/DumpToProtobuf.h"

#include <fstream>
#include <string>

// Usage:
//        fosterparse <inputfile.foster> <outputfile.pb>
// Input: a path to a Foster source file.
// Output: an AST corresponding to the input source,
//         serialized in Protobuf format.

using namespace llvm;
using std::string;

using foster::EDiag;
using foster::ScopedTimer;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<string>
optOutputPath(cl::Positional, cl::desc("<output file>"));

static cl::opt<string>
optIncludePath("I", cl::desc("Path to search for includes"),
                    cl::value_desc("include path"));

static cl::opt<bool>
optDumpStats("dump-stats",
  cl::desc("[foster] Dump timing and other statistics from parsing"));

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("[foster] Print timing measurements of compiler passes"));

void setTimingDescriptions() {
  using foster::gTimings;
  gTimings.describe("total", "Overall compiler runtime (ms)");

  gTimings.describe("io.parse", "Time spent parsing input file (ms)");
  gTimings.describe("io.file",  "Time spent doing non-parsing I/O (ms)");
  gTimings.describe("io.proto", "Time spent reading/writing protobufs (ms)");
}

void dumpWholeProgramToProtobuf(WholeProgramAST* pgm, const string& filename) {
  ASSERT(pgm != NULL);

  foster::fepb::WholeProgram wp;
  for (int x = 0; x < pgm->getModuleCount(); ++x) {
    ModuleAST* mod = pgm->getModuleAST(x);
    ASSERT(mod != NULL);
    foster::fepb::SourceModule* sm = wp.add_modules();

    const foster::InputTextBuffer* buf = mod->buf;
    if (buf) {
      for (int i = 0; i < buf->getLineCount(); ++i) {
        sm->add_line(buf->getLine(i));
      }
    }

    { ScopedTimer timer("io.protobuf.convert");
    DumpToProtobufPass p; dumpModule(&p, *sm, mod);
    }

    if (!sm->IsInitialized()) {
      EDiag() << "Protobuf module message is not initialized!\n";
    }
  }

  if (filename == "-") {
    EDiag() << "warning: dumping module to file named '-', not stdout!";
  }

  if (!wp.IsInitialized()) {
    EDiag() << "Protobuf program message is not initialized!\n";
  }

  ScopedTimer timer("io.protobuf.out");
  std::ofstream out(filename.c_str(),
                  std::ios::trunc | std::ios::binary);
  if (wp.SerializeToOstream(&out)) {
    // ok!
  } else {
    EDiag() << "program serialization returned false\n";
  }
}

int main(int argc, char** argv) {
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster parser\n");

  foster::validateInputFile(optInputPath);
  foster::validateOutputFile(optOutputPath);
  const foster::InputFile infile(optInputPath);

  unsigned numParseErrors = 0;

  foster::ParsingContext::pushNewContext();

  WholeProgramAST* pgmAST = NULL;
  { ScopedTimer timer("io.parse");
    pgmAST = foster::parseWholeProgram(infile, optIncludePath, &numParseErrors);
  }

  if (numParseErrors > 0) {
    EDiag() << "Encountered " << numParseErrors << " parsing errors; exiting."
            << (pgmAST ? " (with AST)" : " (without AST");
    return 3;
  } else if (!pgmAST) {
    return 4;
  }

  dumpWholeProgramToProtobuf(pgmAST, optOutputPath);

  if (optPrintTimings) {
    setTimingDescriptions();
    foster::gTimings.print("fosterparse");
  }
  if (optDumpStats) {
    llvm::PrintStatistics(llvm::outs());
  }
  return 0;
}
