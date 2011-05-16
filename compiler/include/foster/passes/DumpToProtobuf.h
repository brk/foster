// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_DUMPTOPROTOBUF
#define FOSTER_PASSES_DUMPTOPROTOBUF

#include "_generated_/FosterAST.pb.h"

struct DumpToProtobufPass {
  foster::fepb::Expr* current;
  DumpToProtobufPass() : current(NULL) {}
};

void dumpModule(DumpToProtobufPass* p,
                foster::fepb::SourceModule& sm,
                ModuleAST* mod);

struct DumpTypeToProtobufPass {
  foster::fepb::Type* current;
  DumpTypeToProtobufPass(foster::fepb::Type* current) : current(current) {}
};

#endif // header guard

