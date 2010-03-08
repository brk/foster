// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_UTILS_H
#define FOSTER_UTILS_H

#include "llvm/DerivedTypes.h"

const llvm::FunctionType* tryExtractCallableType(const llvm::Type* ty);

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericClosureTypeFor(const llvm::FunctionType* fnty);

// converts t1 (envptrty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericVersionOfClosureType(const llvm::FunctionType* fnty);

#endif

