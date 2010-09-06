// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/FreshNameGenerator.h"

#include "parse/FosterTypeAST.h"
#include "parse/FosterSymbolTable.h"
#include "parse/CompilationContext.h"

#include "llvm/LLVMContext.h"
#include "llvm/Target/TargetSelect.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <stack>
#include <map>

using llvm::getGlobalContext;

using std::map;
using std::string;

namespace foster {

std::stack<CompilationContext*> gCompilationContexts;


struct CompilationContext::Impl {
  OperatorPrecedenceTable prec;
  FreshNameGenerator freshNames;

  std::map<pANTLR3_BASE_TREE, pANTLR3_COMMON_TOKEN> startTokens;
  std::map<pANTLR3_BASE_TREE, pANTLR3_COMMON_TOKEN>   endTokens;

  std::string accumulated_output;
  llvm::raw_string_ostream os;
  llvm::raw_ostream* outs;
  llvm::raw_ostream* errs;

  std::map<string, bool> keywords;
  std::map<string, bool> reserved_keywords;

  Impl() : os(accumulated_output), outs(NULL), errs(NULL) {
    initMaps();
  }

private:
  void initMaps();
};


#ifndef ARRAY_SIZE
#define ARRAY_SIZE(a) (sizeof(a)/sizeof(((a)[0])))
#endif

namespace {
  const char* c_keywords[] = {
    "as" , "at" , "def" , "id", "in", "is", "it", "to",
    "given" , "false" , "if" , "match" , "do" , "new" , "nil",
    "gives" , "and" , "or" , "true" , "var" , "while",
    "for", "ref", "?ref"
  };
  const char* c_reserved_keywords[] = {
    "def", "catch", "lazy", "object", "package", "private",
    "protected", "return", "throw", "trait", "try", "type",
    "val", "with", "yield", "except"
  };
} // unnamed namespace

void
CompilationContext::Impl::initMaps() {
  for (size_t i = 0; i < ARRAY_SIZE(c_keywords); ++i) {
    keywords[c_keywords[i]] = true;
  }

  for (size_t i = 0; i < ARRAY_SIZE(c_reserved_keywords); ++i) {
    reserved_keywords[c_reserved_keywords[i]] = true;
  }
}


CompilationContext* // static
CompilationContext::pushNewContext() {
  CompilationContext* cc = new CompilationContext();
  gCompilationContexts.push(cc);
  return cc;
}

void // static
CompilationContext::pushContext(CompilationContext* cc) {
  gCompilationContexts.push(cc);
}

CompilationContext* // static
CompilationContext::popCurrentContext() {
  ASSERT(!gCompilationContexts.empty());
  CompilationContext* cc = gCompilationContexts.top();
  gCompilationContexts.pop();
  return cc;
}

/////////////////////

std::string // static
CompilationContext::freshName(std::string like) {
  ASSERT(!foster::gCompilationContexts.empty());

  return foster::gCompilationContexts.top()->impl->freshNames.fresh(like);
}

/////////////////////

void // static
CompilationContext::setTokenRange(pANTLR3_BASE_TREE t,
              pANTLR3_COMMON_TOKEN s,
              pANTLR3_COMMON_TOKEN e) {
  ASSERT(!gCompilationContexts.empty());

  gCompilationContexts.top()->impl->startTokens[t] = s;
  gCompilationContexts.top()->impl->  endTokens[t] = e;
}

pANTLR3_COMMON_TOKEN // static
CompilationContext::getStartToken(pANTLR3_BASE_TREE t) {
  ASSERT(!gCompilationContexts.empty());

  return gCompilationContexts.top()->impl->startTokens[t];
}

pANTLR3_COMMON_TOKEN // static
CompilationContext::getEndToken(pANTLR3_BASE_TREE t) {
  ASSERT(!gCompilationContexts.empty());

  return gCompilationContexts.top()->impl->endTokens[t];
}


void // static
CompilationContext::clearTokenBoundaries() {
  ASSERT(!gCompilationContexts.empty());

  gCompilationContexts.top()->impl->startTokens.clear();
  gCompilationContexts.top()->impl->  endTokens.clear();
}

///////////////////

foster::OperatorPrecedenceTable::OperatorRelation // static
CompilationContext::getOperatorRelation(const std::string& op1,
                                        const std::string& op2) {
  ASSERT(!gCompilationContexts.empty());

  return gCompilationContexts.top()->impl->prec.get(op1, op2);
}

bool // static
CompilationContext::isKnownOperatorName(const string& op) {
  ASSERT(!gCompilationContexts.empty());

  return gCompilationContexts.top()->impl->prec.isKnownOperatorName(op);
}

bool // static
CompilationContext::isKeyword(const string& op) {
  ASSERT(!gCompilationContexts.empty());

  return gCompilationContexts.top()->impl->keywords[op];
}

bool // static
CompilationContext::isReservedKeyword(const string& op) {
  ASSERT(!gCompilationContexts.empty());

  return gCompilationContexts.top()->impl->reserved_keywords[op];
}

////////////////////////////////////////////////////////////////////

llvm::raw_ostream& CompilationContext::currentErrs() {
  if (impl->errs) { return *(impl->errs); }
  else { return llvm::errs(); }
}

llvm::raw_ostream& CompilationContext::currentOuts() {
  if (impl->outs) { return *(impl->outs); }
  else { return llvm::errs(); }
}

void CompilationContext::startAccumulatingOutputToString() {
  impl->outs = &impl->os;
  impl->errs = &impl->os;
}

std::string CompilationContext::collectAccumulatedOutput() {
  std::string rv = impl->os.str();
  impl->accumulated_output.clear();
  return rv;
}


CompilationContext::CompilationContext() {
  impl = new Impl();
}

////////////////////////////////////////////////////////////////////

llvm::raw_ostream& currentErrs() {
  if (gCompilationContexts.empty()) {
    return llvm::errs();
  } else {
    return gCompilationContexts.top()->currentErrs();
  }
}

llvm::raw_ostream& currentOuts() {
  if (gCompilationContexts.empty()) {
    return llvm::outs();
  } else {
    return gCompilationContexts.top()->currentOuts();
  }  
}

////////////////////////////////////////////////////////////////////

EDiag::~EDiag() {}

////////////////////////////////////////////////////////////////////

llvm::ExecutionEngine* ee = NULL;
llvm::IRBuilder<> builder(llvm::getGlobalContext());
llvm::Module* module = NULL;

map<string, const llvm::Type*> gCachedLLVMTypes;

TypeAST*    TypeASTFor(const string& name) {
  if (gCachedLLVMTypes.count(name) == 1) {
    return NamedTypeAST::get(name, gCachedLLVMTypes[name]);
  } else if (TypeAST* ty = gTypeScope.lookup(name, "")) {
    return ty;
  } else {
    if (const llvm::Type* ty = LLVMTypeFor(name)) {
      ASSERT(false) << "WARNING: have LLVMTypeFor("<<name<<")"
                    << " but no TypeASTFor(...)";
      ty = NULL; // avoid unused variable warning
    }
    return NULL;
  }
}

const llvm::Type* LLVMTypeFor(const string& name) {
  if (gCachedLLVMTypes.count(name) == 1) {
    return gCachedLLVMTypes[name];
  } else if (foster::module) {
    return foster::module->getTypeByName(name);
  } else {
    return NULL;
  }
}

void initCachedLLVMTypeNames() {
  gCachedLLVMTypes["i1"] = llvm::IntegerType::get(getGlobalContext(), 1);
  gCachedLLVMTypes["i8"] = llvm::IntegerType::get(getGlobalContext(), 8);
  gCachedLLVMTypes["i16"] = llvm::IntegerType::get(getGlobalContext(), 16);
  gCachedLLVMTypes["i32"] = llvm::IntegerType::get(getGlobalContext(), 32);
  gCachedLLVMTypes["i64"] = llvm::IntegerType::get(getGlobalContext(), 64);

  gCachedLLVMTypes["i8*"] = llvm::PointerType::getUnqual(gCachedLLVMTypes["i8"]);
  gCachedLLVMTypes["i8**"] = llvm::PointerType::getUnqual(gCachedLLVMTypes["i8*"]);
}


/// Macros in TargetSelect.h conflict with those from ANTLR, so this code
/// must be in a source file that does not include any ANTLR files.
void initializeLLVM() {
  llvm::InitializeNativeTarget();

  // Initializing the native target doesn't initialize the native
  // target's ASM printer, so we have to do it ourselves.
#if LLVM_NATIVE_ARCH == X86Target
  LLVMInitializeX86AsmPrinter();
#else
  std::cerr << "Warning: not initializing any asm printer!" << std::endl;
#endif

  initCachedLLVMTypeNames();
}

} // namespace foster

string freshName(string like) {
  return foster::CompilationContext::freshName(like);
}

