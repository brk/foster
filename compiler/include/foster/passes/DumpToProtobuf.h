// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_DUMPTOPROTOBUF
#define FOSTER_PASSES_DUMPTOPROTOBUF

#include "_generated_/FosterAST.pb.h"

struct DumpToProtobufPass {
  foster::fepb::Expr* exp;
  foster::fepb::Type* typ;
  DumpToProtobufPass() : exp(NULL), typ(NULL) {}
  DumpToProtobufPass(foster::fepb::Expr* exp, foster::fepb::Type* typ) : exp(exp), typ(typ) {}
};

void dumpModule(DumpToProtobufPass* p,
                foster::fepb::SourceModule& sm,
                ModuleAST* mod);

#endif // header guard

