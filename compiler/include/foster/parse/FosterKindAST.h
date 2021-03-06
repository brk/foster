// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_KIND_AST_H
#define FOSTER_KIND_AST_H

#include "base/SourceRange.h"

#include <string>

struct KindAST {
  virtual ~KindAST() {}
};

struct TypeFormal {
  std::string name; // pattern???
  KindAST* kind;
  foster::SourceRange sourceRange;
  explicit TypeFormal(const std::string& name, KindAST* kind, const foster::SourceRange& sourceRange)
  : name(name), kind(kind), sourceRange(sourceRange) {}
};

#endif
