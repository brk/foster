#include "FosterUtils.h"
#include "FosterAST.h" // TODO this is just for LLVMTypeFor(), should break this dependency!

#include "llvm/Module.h"

#include <sstream>

using llvm::Type;
using llvm::FunctionType;

std::map<const Type*, bool> namedClosureTypes;

void addClosureTypeName(llvm::Module* mod, const llvm::StructType* sty) {
  if (!mod) return;
  if (namedClosureTypes[sty]) return;

  std::stringstream ss;
  ss << "ClosureTy";
  const FunctionType* fty = tryExtractCallableType(sty->getContainedType(0));
  if (fty != NULL) {
    // Skip generic closure argument
    for (int i = 1; i < fty->getNumParams(); ++i) {
      ss << "_" << *(fty->getParamType(i));
    }
    ss << "_to_" << *(fty->getReturnType());

    mod->addTypeName(ss.str(), sty);

    namedClosureTypes[sty] = true;
  }
}

const FunctionType* tryExtractCallableType(const Type* ty) {
  if (const llvm::PointerType* ptrTy = llvm::dyn_cast<llvm::PointerType>(ty)) {
    // Avoid doing full recursion on pointer types; fn* is callable,
    // but fn** is not.
    ty = ptrTy->getContainedType(0);
  }

  return llvm::dyn_cast_or_null<const llvm::FunctionType>(ty);
}

// converts      t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
// or    t1 (envty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
static const llvm::StructType* genericClosureTypeFor(const FunctionType* fnty, bool skipFirstArg) {
  const Type* envType = llvm::PointerType::get(LLVMTypeFor("i8"), 0);

  std::vector<const Type*> fnParams;
  fnParams.push_back(envType);

  int firstArg = skipFirstArg ? 1 : 0;
  for (int i = firstArg; i < fnty->getNumParams(); ++i) {
    fnParams.push_back(fnty->getParamType(i));
  }

  const Type* fnTy = llvm::FunctionType::get(fnty->getReturnType(), fnParams, /*isVarArg=*/ false);
  std::vector<const Type*> cloTypes;
  cloTypes.push_back(llvm::PointerType::get(fnTy, 0));
  cloTypes.push_back(envType);
  const llvm::StructType* cloTy = llvm::StructType::get(getGlobalContext(), cloTypes, /*isPacked=*/ false);
  //std::cout << "GENERIC CLOSURE TYPE for " << *fnty << " is " << *cloTy << std::endl;
  return cloTy;
}

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericClosureTypeFor(const FunctionType* fnty) {
  return genericClosureTypeFor(fnty, false);
}

// converts t1 (envty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericVersionOfClosureType(const FunctionType* fnty) {
  return genericClosureTypeFor(fnty, true);
}

