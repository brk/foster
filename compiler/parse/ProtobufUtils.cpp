// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/System/Path.h"

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/InputTextBuffer.h"

#include "parse/FosterAST.h"
#include "parse/ProtobufToAST.h"
#include "parse/ProtobufUtils.h"

#include "passes/DumpToProtobuf.h"

#include <fstream>

using foster::EDiag;
using foster::gInputTextBuffer;

foster::InputTextBuffer*
newInputBufferFromSourceModule(const foster::fepb::SourceModule& sm) {
  int expectedLineCount = sm.line_size();
  std::string lines;
  for (int i = 0; i < expectedLineCount; ++i) {
    lines += sm.line(i) + "\n";
  }

  foster::InputTextBuffer* buf =
      new foster::InputTextBuffer(lines.c_str(), lines.size());

  ASSERT(buf->getLineCount() == expectedLineCount)
      << "expected line count: " << expectedLineCount
      << "actual   line count: " << buf->getLineCount();

  return buf;
}

ModuleAST* readSourceModuleFromProtobuf(const string& pathstr,
                                        foster::fepb::SourceModule& out_sm) {
  std::fstream input(pathstr.c_str(), std::ios::in | std::ios::binary);
  if (!out_sm.ParseFromIstream(&input)) {
    return NULL;
  }

  const foster::InputTextBuffer* inputBuffer = gInputTextBuffer;
  gInputTextBuffer = newInputBufferFromSourceModule(out_sm);
  ExprAST* expr = foster::ExprAST_from_pb(out_sm.mutable_expr());
  gInputTextBuffer = inputBuffer;

  if (!expr) {
    EDiag() << "unable to parse expression from source module protobuf";
    return NULL;
  }

  return dynamic_cast<ModuleAST*>(expr);
}

void dumpModuleToProtobuf(ModuleAST* mod, const string& filename) {
  ASSERT(mod != NULL);

  foster::fepb::SourceModule sm;
  const foster::InputTextBuffer* buf = mod->sourceRange.buf;
  if (buf) {
    for (int i = 0; i < buf->getLineCount(); ++i) {
      sm.add_line(buf->getLine(i));
    }
  }

  foster::fepb::Expr* pbModuleExpr = sm.mutable_expr();
  DumpToProtobufPass p(pbModuleExpr); mod->accept(&p);

  if (!pbModuleExpr->IsInitialized()) {
    EDiag() << "Protobuf message is not initialized!\n";
  }

  if (filename == "-") {
    EDiag() << "warning: dumping module to file named '-', not stdout!";
  }

  std::string debug_filename = filename + ".dbg.txt";
  std::ofstream debug_out(debug_filename.c_str(),
                          std::ios::trunc | std::ios::binary);
  debug_out << pbModuleExpr->DebugString();

  std::ofstream out(filename.c_str(),
                  std::ios::trunc | std::ios::binary);
  if (sm.SerializeToOstream(&out)) {
    // ok!
  } else {
    EDiag() << "serialization returned false\n";
  }
}

