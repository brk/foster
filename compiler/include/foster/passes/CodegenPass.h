// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CODEGEN
#define FOSTER_PASSES_CODEGEN

#include "parse/FosterASTVisitor.h"
#include <stack>

struct CodegenPass : public FosterASTVisitor {
  #include "parse/FosterASTVisitor.decls.inc.h"
};

#endif // header guard

