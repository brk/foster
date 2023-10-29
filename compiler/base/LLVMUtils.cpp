// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/LLVMUtils.h"

#include <map>
#include <sstream>
#include <iostream>
#include <ostream>

#include "llvm/Support/TargetSelect.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/AssemblyAnnotationWriter.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/SourceMgr.h"

#include "llvm/Support/FileSystem.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/Signals.h"

#include "pystring/pystring.h"

using namespace llvm;

std::ostream& operator<<(std::ostream& out, llvm::Type& ty) {
  out << str(&ty);
  return out;
}

std::string str(llvm::Type* ty) {
  if (!ty) return "<NULL ty>";
  std::string s;
  llvm::raw_string_ostream ss(s); ss << *ty;
  return ss.str();
}

std::string str(llvm::Value* value) {
  if (!value) return "<nil>";
  std::string s;
  llvm::raw_string_ostream ss(s); ss << *value;
  return ss.str();
}

namespace foster {

std::map<std::string, std::string> sgProcLines;
llvm::LLVMContext fosterLLVMContext;
llvm::IRBuilder<> builder(fosterLLVMContext);

/// Macros in TargetSelect.h conflict with those from ANTLR, so this code
/// must be in a source file that does not include any ANTLR files.
void
initializeLLVM() {
  llvm::InitializeNativeTarget();

  // Initializing the native target doesn't initialize the native
  // target's ASM printer, so we have to do it ourselves.
  #if LLVM_NATIVE_ARCH == X86Target
    LLVMInitializeX86AsmPrinter();
    LLVMInitializeX86AsmParser();
  #else
    llvm::errs() << "Warning: not initializing any asm printer!\n";
  #endif
}

void
validateFileOrDir(const std::string& pathstr,
                  const char* inp,
                  bool want_dir) {
  if (pathstr.empty()) {
    EDiag() << "need an " << inp << " filename!";
    exit(1);
  }

  llvm::sys::fs::file_status st;
  if(llvm::sys::fs::status(pathstr, st)) {
    EDiag() << "Error occurred when reading " << inp << " path '"
            << pathstr << "'";
    exit(1);
  }

  if (llvm::sys::fs::is_directory(st) != want_dir) {
    if (want_dir) {
      EDiag() << inp << " must be a directory, not a file!";
    } else {
      EDiag() << inp << " must be a file, not a directory!";
    }
    exit(1);
  }
}

void
validateInputFile(const std::string& pathstr) {
  validateFileOrDir(pathstr, "input file", false);
}

void validateOutputFile(const std::string& pathstr) {
  llvm::SmallString<128> outputPath(pathstr);
  llvm::sys::path::remove_filename(outputPath);
  if (outputPath.empty()) { outputPath = "./"; }
  validateFileOrDir(outputPath.str().str(), "output dir", true);
}

void ensureDirectoryExists(const std::string& pathstr) {
  if (llvm::sys::fs::create_directory(pathstr, true)) {
    foster::EDiag() << "unable to create directory " << pathstr << "\n";
    exit(1);
  }
}

std::unique_ptr<Module> readLLVMModuleFromPath(const std::string& path) {
  llvm::SMDiagnostic diag;
  return llvm::parseIRFile(path, diag, fosterLLVMContext);
}

struct CommentWriter : public llvm::AssemblyAnnotationWriter {
  void printInfoComment(const Value& v, formatted_raw_ostream& os) {
    if (v.getType()->isVoidTy()) return;
    os.PadToColumn(62);
    os << "; #uses = " << v.getNumUses() << "\t; " << *(v.getType());
  }

  void emitFunctionAnnot(const llvm::Function* f, formatted_raw_ostream& os) {
    if (!f->isDeclaration()) {

      std::string originalName = f->getName().str();
      if (originalName == "foster__main") {
        originalName = "main";
      }

      std::string& s = sgProcLines[originalName];
      if (!s.empty()) {
        os << "; Function " << f->getName() << " source text:\n;";
        os << pystring::replace(s, "\n", "\n;   ") << "\n";
      }

    }
  }
};

void dumpModuleToFile(llvm::Module* mod, const std::string& filename) {
  std::error_code errInfo;
  llvm::raw_fd_ostream LLpreASM(filename.c_str(), errInfo,
                           llvm::sys::fs::FileAccess::FA_Write
                         | llvm::sys::fs::FileAccess::FA_Read);
  if (!errInfo) {
    CommentWriter cw;
    mod->print(LLpreASM, &cw);
  } else {
    std::string s; std::stringstream ss(s); ss << errInfo;
    foster::EDiag() << "when dumping module to " << filename << "\n"
                    << ss.str() << "\n";
    exit(1);
  }
}

void dumpModuleToBitcode(llvm::Module* mod, const std::string& filename) {
  std::error_code errInfo;
  std::string errInfoStr;
  sys::RemoveFileOnSignal(filename, &errInfoStr);

  raw_fd_ostream out(filename.c_str(), errInfo, llvm::sys::fs::FileAccess::FA_Write);
  if (errInfo) {
    std::string s; std::stringstream ss(s); ss << errInfo;
    foster::EDiag() << "when preparing to write bitcode to " << filename
        << "\n" << ss.str() << "\n" << errInfoStr;
    exit(1);
  }

  WriteBitcodeToFile(*mod, out);
}

} // namespace foster

std::string makePathAbsolute(std::string path) {
  llvm::SmallString<128> pathstr(path);
  std::error_code err = llvm::sys::fs::make_absolute(pathstr);
  ASSERT(!err) << err.message();
  return pathstr.str().str();
}

const char* llvmValueTag(llvm::Value* v) {
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
  if (isa<llvm::TruncInst>(v))          return "TruncInst";
  if (isa<llvm::BitCastInst>(v))        return "BitCastInst";

  return "Unknown Value";
}

// Converts a global variable of type [_ x T] to a local var of type T*.
Constant* arrayVariableToPointer(GlobalVariable* arr) {
  llvm::Constant* zero =
                 llvm::ConstantInt::get(Type::getInt64Ty(arr->getContext()), 0);
  std::vector<Constant*> idx;
  idx.push_back(zero);
  idx.push_back(zero);
  return ConstantExpr::getGetElementPtr(nullptr, arr, llvm::ArrayRef(idx));
}

bool isFunctionPointerTy(llvm::Type* p) {
  return p->isPointerTy()
      && p->getContainedType(0)->isFunctionTy();
}

// Syntactically conspicuous
bool typesEq(llvm::Type* t1, llvm::Type* t2) { return (t1 == t2); }

bool isPointerToType(llvm::Type* p, llvm::Type* t) {
  return p->isPointerTy() && typesEq(p->getContainedType(0), t);
}

bool isPointerToOpaque(llvm::Type* p) {
  if (!p->isPointerTy()) return false;
  if (auto sty = dyn_cast<StructType>(p->getContainedType(0))) {
    return sty->isOpaque();
  }
  return false;
}

void storeNullPointerToSlot(llvm::Value* slot, llvm::Type* ty) {
  foster::builder.CreateStore(
    llvm::ConstantPointerNull::getNullValue(ty),
    slot, /*isVolatile=*/ false);
}


// ASSUMPTION: not cross compiling; host and target sizes match.
bool is32Bit() {
  #if defined(__x86_64__) || defined(__x86_64)
    return false;
  #else
    return true;
  #endif
}

int getWordTySize() {
  if (is32Bit()) {
    return 32;
  } else {
    return 64;
  }
}

llvm::Type* getWordTy(IRBuilder<>& b) {
  return llvm::Type::getIntNTy(b.getContext(), 1 * getWordTySize());
}

llvm::Type* getWordX2Ty(IRBuilder<>& b) {
  return llvm::Type::getIntNTy(b.getContext(), 2 * getWordTySize());
}

llvm::Constant* getNullOrZero(llvm::Type* t) {
  if (llvm::PointerType* p = llvm::dyn_cast<llvm::PointerType>(t)) {
    return llvm::ConstantPointerNull::get(p);
  } else if (llvm::isa<llvm::IntegerType>(t)) {
    return llvm::ConstantInt::get(t, 0);
  } else if (t->isFloatingPointTy()) {
    return llvm::ConstantFP::get(t, 0.0);
  } else {
    //t->dump();
    assert(false && "getNullOrZero given improper type");
    return NULL;
  }
}

llvm::PointerType* ptrTo(llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
}

llvm::PointerType* rawPtrTo(llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
}

llvm::PointerType* getHeapPtrTo(llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
  //return llvm::PointerType::get(t, 1);
}

bool isFosterFunction(llvm::Function& F) {
  return F.hasFnAttribute("foster-fn");
}

