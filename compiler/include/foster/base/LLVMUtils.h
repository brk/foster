// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_LLVM_UTILS_H
#define FOSTER_LLVM_UTILS_H

#include "llvm/Support/DataTypes.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/TimeValue.h"

#include "llvm/Support/IRBuilder.h"
#include "llvm/ADT/StringSet.h"

#include <iosfwd>

namespace llvm {
  class Type;
  class Module;
  class FunctionType;
  class ConstantInt;
  class Value;
  class CallInst;
  class raw_ostream;
  class FunctionPassManager;
  namespace sys { class Path; }
}

#define FOSTER_VERSION_STR "0.0.6"

std::ostream& operator<<(std::ostream& out, const llvm::Type& ty);

std::string str(const llvm::Type* ty);
std::string str(const llvm::Value* value);

namespace foster {

void initializeLLVM();
void initializeKnownNonAllocatingFQNames(llvm::StringSet<>& names);

/// Ensures that the given path exists and is a file, not a directory.
/// Calls exit() if file is not a readable file.
void validateInputFile(const std::string& pathstr);
void validateOutputFile(const std::string& pathstr);

void runFunctionPassesOverModule(llvm::FunctionPassManager& fpasses,
                                 llvm::Module* mod);

void ensureDirectoryExists(const std::string& pathstr);


llvm::Module* readLLVMModuleFromPath(const std::string& path);
void dumpModuleToBitcode(llvm::Module* mod, const std::string& filename);
void dumpModuleToFile(llvm::Module* mod, const std::string& filename);

extern llvm::IRBuilder<> builder;

} // namespace foster

void makePathAbsolute(llvm::sys::Path& path);

const char* llvmValueTag(const llvm::Value* v);
void markAsNonAllocating(llvm::CallInst* callInst);

bool isPointerToFunction(const llvm::Type* p);

// returns true if p == t*
bool isPointerToType(const llvm::Type* p, const llvm::Type* t);

// returns true if p == t**
bool isPointerToPointerToType(const llvm::Type* p, const llvm::Type* t);

bool isVoidOrUnit(const llvm::Type* ty);
bool isUnit(const llvm::Type* ty);
bool typesEqual(const llvm::Type* t1, const llvm::Type* t2);

llvm::ConstantInt* getConstantInt64For(int64_t val);
llvm::ConstantInt* getConstantInt32For(int32_t val);
llvm::ConstantInt* getConstantInt8For(int8_t val);

void storeNullPointerToSlot(llvm::Value* slot);

class Nominalizer {
public:
  const llvm::StructType* nominalize(const llvm::Type*);
  const llvm::Type* denominalize(const llvm::StructType*);
  bool isNominalized(const llvm::StructType*);
private:
  struct Impl;
   Impl* impl;
};

#endif
