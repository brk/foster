// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/LLVMUtils.h"

#include <map>

#include "llvm/Target/TargetSelect.h"
#include "llvm/Instructions.h"
#include "llvm/Metadata.h"
#include "llvm/Module.h"
#include "llvm/LLVMContext.h"
#include "llvm/PassManager.h"
#include "llvm/Assembly/AssemblyAnnotationWriter.h"
#include "llvm/Support/IRReader.h"
#include "llvm/Support/FormattedStream.h"

#include "llvm/Support/FileSystem.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Signals.h"

#include "pystring/pystring.h"

using namespace llvm;

std::ostream& operator<<(std::ostream& out, const llvm::Type& ty) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << ty;
  return out << ss.str();
}

std::string str(const llvm::Type* ty) {
  if (!ty) return "<NULL ty>";
  std::string s;
  llvm::raw_string_ostream ss(s); ss << *ty;
  return ss.str();
}

std::string str(const llvm::Value* value) {
  if (!value) return "<nil>";
  std::string s;
  llvm::raw_string_ostream ss(s); ss << *value;
  return ss.str();
}

namespace foster {

std::map<std::string, std::string> sgProcLines;
llvm::IRBuilder<> builder(llvm::getGlobalContext());

/// Macros in TargetSelect.h conflict with those from ANTLR, so this code
/// must be in a source file that does not include any ANTLR files.
void
initializeLLVM() {
  llvm::InitializeNativeTarget();

  // Initializing the native target doesn't initialize the native
  // target's ASM printer, so we have to do it ourselves.
  #if LLVM_NATIVE_ARCH == X86Target
    LLVMInitializeX86AsmPrinter();
  #else
    llvm::errs() << "Warning: not initializing any asm printer!\n";
  #endif
}

void
validateFileOrDir(const std::string& pathstr,
                  const char* inp,
                  bool want_dir) {
  llvm::sys::PathWithStatus path(pathstr);

  if (path.empty()) {
    EDiag() << "Error: need an " << inp << " filename!";
    exit(1);
  }

  std::string err;
  const llvm::sys::FileStatus* status
         = path.getFileStatus(/*forceUpdate=*/ false, &err);
  if (!status) {
    if (err.empty()) {
      EDiag() << "Error occurred when reading " << inp << " path '"
              << pathstr << "'";
    } else {
      EDiag() << "Error validating " << inp << " path: " << err;
    }
    exit(1);
  }

  if (status->isDir != want_dir) {
    if (want_dir) {
      EDiag() << "Error: " << inp << " must be a directory, not a file!";
    } else {
      EDiag() << "Error: " << inp << " must be a file, not a directory!";
    }
    exit(1);
  }
}

void
validateInputFile(const std::string& pathstr) {
  validateFileOrDir(pathstr, "input", false);
}

void validateOutputFile(const std::string& pathstr) {
  llvm::sys::Path outputPath(pathstr);
  validateFileOrDir(outputPath.getDirname(), "output", true);
}

void runFunctionPassesOverModule(llvm::FunctionPassManager& fpasses,
                                 Module* mod) {
  fpasses.doInitialization();
  for (Module::iterator it = mod->begin(); it != mod->end(); ++it) {
    fpasses.run(*it);
  }
  fpasses.doFinalization();
}

void ensureDirectoryExists(const std::string& pathstr) {
  llvm::sys::Path p(pathstr);
  if (!p.isDirectory()) {
    p.createDirectoryOnDisk(true, NULL);
  }
}

Module* readLLVMModuleFromPath(const std::string& path) {
  llvm::SMDiagnostic diag;
  return llvm::ParseIRFile(path, diag, llvm::getGlobalContext());
}

struct CommentWriter : public llvm::AssemblyAnnotationWriter {
  void printInfoComment(const Value& v, formatted_raw_ostream& os) {
    if (v.getType()->isVoidTy()) return;
    os.PadToColumn(62);
    os << "; #uses = " << v.getNumUses() << "\t; " << *(v.getType());
  }

  void emitFunctionAnnot(const llvm::Function* f, formatted_raw_ostream& os) {
    if (!f->isDeclaration()) {

      std::string originalName = f->getName();
      if (originalName == "foster__main") {
        originalName = "main";
      }

      std::string& s = sgProcLines[originalName];
      if (!s.empty()) {
        os << "; Function " << f->getName() << " source text:\n";
        os << pystring::replace(s, "\n", "\n;   ") << "\n";
      }

    }
  }
};

void dumpModuleToFile(llvm::Module* mod, const std::string& filename) {
  std::string errInfo;
  llvm::raw_fd_ostream LLpreASM(filename.c_str(), errInfo);
  if (errInfo.empty()) {
    CommentWriter cw;
    mod->print(LLpreASM, &cw);
  } else {
    foster::EDiag() << "Error dumping module to " << filename << "\n"
                    << errInfo << "\n";
    exit(1);
  }
}

void dumpModuleToBitcode(llvm::Module* mod, const std::string& filename) {
  std::string errInfo;
  sys::RemoveFileOnSignal(sys::Path(filename), &errInfo);

  raw_fd_ostream out(filename.c_str(), errInfo, raw_fd_ostream::F_Binary);
  if (!errInfo.empty()) {
    foster::EDiag() << "Error when preparing to write bitcode to " << filename
        << "\n" << errInfo;
    exit(1);
  }

  WriteBitcodeToFile(mod, out);
}

void initializeKnownNonAllocatingFQNames(llvm::StringSet<>& names) {
  names.insert("print_i1");
  names.insert("expect_i1");
  names.insert("print_i32");
  names.insert("expect_i32");
  names.insert("print_i64");
  names.insert("expect_i64");
  names.insert("read_i32");
  names.insert("mp_int_zero");
  names.insert("mp_int_clear");
  names.insert("mp_int_init_value");

  // This one will allocate memory, but for now, it only allocates
  // memory via malloc, so it cannot trigger GC.
  names.insert("foster_coro_create");
}

} // namespace foster

void makePathAbsolute(llvm::sys::Path& path) {
  llvm::SmallString<128> pathstr(path.str());
  llvm::error_code err = llvm::sys::fs::make_absolute(pathstr);
  ASSERT(err == llvm::errc::success) << err.message();
  path.set(pathstr);
}

const char* llvmValueTag(const llvm::Value* v) {
  using llvm::isa;
  if (!v) return "<NULL Value>";

  if (isa<llvm::AllocaInst>(v))         return "AllocaInst";
  if (isa<llvm::LoadInst>(v))           return "LoadInst";
  if (isa<llvm::CallInst>(v))           return "CallInst";
  if (isa<llvm::StoreInst>(v))          return "StoreInst";
  if (isa<llvm::BinaryOperator>(v))     return "BinaryOperator";

  if (isa<llvm::Constant>(v))           return "Constant";
  if (isa<llvm::Argument>(v))           return "Argument";
  if (isa<llvm::GlobalValue>(v))        return "GlobalValue";
  if (isa<llvm::CastInst>(v))           return "CastInst";

  if (isa<llvm::GetElementPtrInst>(v))  return "GetElementPtrInst";
  if (isa<llvm::ICmpInst>(v))           return "ICmpInst";
  if (isa<llvm::FCmpInst>(v))           return "FCmpInst";
  if (isa<llvm::SelectInst>(v))         return "SelectInst";
  if (isa<llvm::ExtractElementInst>(v)) return "ExtractElementInst";
  if (isa<llvm::ExtractValueInst>(v))   return "ExtractValueInst";
  if (isa<llvm::SelectInst>(v))         return "SelectInst";
  if (isa<llvm::SwitchInst>(v))         return "SwitchInst";
  if (isa<llvm::InsertElementInst>(v))  return "InsertElementInst";
  if (isa<llvm::InsertValueInst>(v))    return "InsertValueInst";
  if (isa<llvm::PHINode>(v))            return "PHINode";
  if (isa<llvm::ReturnInst>(v))         return "ReturnInst";
  if (isa<llvm::BranchInst>(v))         return "BranchInst";
  if (isa<llvm::IndirectBrInst>(v))     return "IndirectBrInst";
  if (isa<llvm::InvokeInst>(v))         return "InvokeInst";
  if (isa<llvm::UnwindInst>(v))         return "UnwindInst";
  if (isa<llvm::TruncInst>(v))          return "TruncInst";
  if (isa<llvm::BitCastInst>(v))        return "BitCastInst";

  return "Unknown Value";
}

void markAsNonAllocating(llvm::CallInst* callInst) {
  llvm::Value* tru = llvm::ConstantInt::getTrue(llvm::getGlobalContext());
  llvm::MDNode* mdnode = llvm::MDNode::get(llvm::getGlobalContext(), &tru, 1);
  callInst->setMetadata("willnotgc", mdnode);
}

llvm::ConstantInt* getConstantInt64For(int64_t val) {
  return llvm::ConstantInt::get(Type::getInt64Ty(getGlobalContext()), val);
}

llvm::ConstantInt* getConstantInt32For(int32_t val) {
  return llvm::ConstantInt::get(Type::getInt32Ty(getGlobalContext()), val);
}

llvm::ConstantInt* getConstantInt8For(int8_t val) {
  return llvm::ConstantInt::get(Type::getInt8Ty(getGlobalContext()), val);
}

bool isVoidOrUnit(const llvm::Type* ty) {
  return ty->isVoidTy() || isUnit(ty);
}

// Check that ty == {} or {}*
bool isUnit(const llvm::Type* ty) {
  const llvm::Type* emptyTy = llvm::StructType::get(getGlobalContext(), false);
  return typesEqual(ty, emptyTy) || isPointerToType(ty, emptyTy);
}

// Syntactically conspicuous
bool typesEqual(const llvm::Type* t1, const llvm::Type* t2) {
  return t1 == t2;
}

bool isPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && typesEqual(t, p->getContainedType(0));
}

// returns true if p == t**
bool isPointerToPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && isPointerToType(p->getContainedType(0), t);
}

void storeNullPointerToSlot(llvm::Value* slot) {
  foster::builder.CreateStore(
    llvm::ConstantPointerNull::getNullValue(slot->getType()->getContainedType(0)),
    slot, /*isVolatile=*/ false);
}

struct Nominalizer::Impl {
  std::map<const llvm::Type*, int> nomCount;
  std::map<const llvm::Type*, bool> isNomTag;
  std::map<int,const llvm::StructType*> tagCache;

  const llvm::StructType* nominalize(const llvm::Type* ty) {
    int n = nomCount[ty];
    ++nomCount[ty];
    return makeNominal(ty, n);
  }

  const llvm::StructType* nomTag(int n) {
    if (n == -1) {
      return StructType::get(getGlobalContext(), false);
    }

    if (!tagCache[n]) {
      std::vector<const Type*> arg;
      arg.push_back(nomTag(n - 1));
      tagCache[n] = llvm::StructType::get(getGlobalContext(), arg, false);
      isNomTag[tagCache[n]] = true;
    }
    return tagCache[n];
  }

  const llvm::StructType* makeNominal(const llvm::Type* ty, int n) {
    std::vector<const Type*> arg;
    arg.push_back(ty);
    arg.push_back(nomTag(n));
    return StructType::get(getGlobalContext(), arg, false);
  }

  const llvm::Type* denominalize(const llvm::StructType* sty) {
    ASSERT(isNominalized(sty));
    return sty->getContainedType(0);
  }

  bool isNominalized(const llvm::StructType* sty) {
    ASSERT(sty->getNumContainedTypes() == 2);
    return isNomTag[sty->getContainedType(1)];
  }
};

const llvm::StructType* Nominalizer::nominalize(const llvm::Type* t )  { return impl->nominalize(t); }
const llvm::Type* Nominalizer::denominalize(const llvm::StructType* t) { return impl->denominalize(t); }
bool Nominalizer::isNominalized(const llvm::StructType* t)       { return impl->isNominalized(t); }

