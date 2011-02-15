// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/TypeSymbolTable.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Intrinsics.h"

#include "base/LLVMUtils.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ParsingContext.h"

#include "pystring/pystring.h"

#include <vector>
#include <sstream>

using namespace llvm;

namespace foster {

bool gPrintLLVMImports = false;

static const char* sOps[] = {
  "negate", "bitnot",

  "+", "-", "/", "*",

  "<" ,
  "<=",
  ">" ,
  ">=",
  "==",
  "!=",

  "bitand" ,
  "bitor"  ,
  "bitxor" ,
  "bitshl" ,
  "bitlshr",
  "bitashr",
  NULL
};

static bool
isUnaryOp(const std::string& op) {
  return op == "negate" || op == "bitnot" || op == "sext_i64";
}

static bool
isCmpOp(const std::string& op) {
  return op == "!=" || op == "==" || op =="<" || op == ">"
      || op == "<=" || op == ">=";
}

static Value*
codegenPrimitiveOperation(const std::string& op,
                          IRBuilder<>& b,
                          const std::vector<Value*>& args) {
  Value* VL = args[0];
       if (op == "negate") { return b.CreateNeg(VL, "negtmp"); }
  else if (op == "bitnot") { return b.CreateNot(VL, "nottmp"); }
  else if (op == "sext_i64") { return b.CreateSExt(VL, b.getInt64Ty(), "sexti64tmp"); }

  Value* VR = args[1];
  // Other variants: F (float), NSW (no signed wrap), NUW,
  // UDiv, ExactSDiv, URem, SRem,
       if (op == "+") { return b.CreateAdd(VL, VR, "addtmp"); }
  else if (op == "-") { return b.CreateSub(VL, VR, "subtmp"); }
  else if (op == "/") { return b.CreateSDiv(VL, VR, "divtmp"); }
  else if (op == "*") { return b.CreateMul(VL, VR, "multmp"); }

  // Also have unsigned variants
  else if (op == "<")  { return b.CreateICmpSLT(VL, VR, "slttmp"); }
  else if (op == "<=") { return b.CreateICmpSLE(VL, VR, "sletmp"); }
  else if (op == ">")  { return b.CreateICmpSGT(VL, VR, "sgttmp"); }
  else if (op == ">=") { return b.CreateICmpSGE(VL, VR, "sgetmp"); }
  else if (op == "==") { return b.CreateICmpEQ(VL, VR, "eqtmp"); }
  else if (op == "!=") { return b.CreateICmpNE(VL, VR, "netmp"); }

  else if (op == "bitand") { return b.CreateAnd(VL, VR, "bitandtmp"); }
  else if (op == "bitor") {  return b.CreateOr( VL, VR, "bitortmp"); }
  else if (op == "bitxor") { return b.CreateXor(VL, VR, "bitxortmp"); }

  else if (op == "bitshl") { return b.CreateShl(VL, VR, "shltmp"); }
  else if (op == "bitlshr") { return b.CreateLShr(VL, VR, "lshrtmp"); }
  else if (op == "bitashr") { return b.CreateAShr(VL, VR, "ashrtmp"); }

  ASSERT(false) << "unhandled op '" << op << "'";
}

static Function*
getConcretePrimitiveFunction(Module* m, const char* op, const Type* ty) {
  std::vector<const Type*> argtypes;
  const Type* returnType = NULL;

  if (isUnaryOp(op)) { // ty -> ty
    argtypes.push_back(ty); returnType = ty;
    if (std::string(op) == "sext_i64") { returnType = Type::getInt64Ty(getGlobalContext()); }
  } else if (isCmpOp(op)) { // ty -> ty -> i1
    argtypes.push_back(ty);
    argtypes.push_back(ty); returnType = Type::getInt1Ty(getGlobalContext());
  } else { // ty -> ty -> ty
    argtypes.push_back(ty);
    argtypes.push_back(ty); returnType = ty;
  }

  ASSERT(returnType != NULL);

  std::string funcName = "primitive_" + std::string(op) + "_" + str(ty);

  FunctionType* ft = FunctionType::get(returnType, argtypes, false);
  Function* f = Function::Create(ft, Function::PrivateLinkage, funcName, m);
  f->setCallingConv(llvm::CallingConv::Fast);
  f->addFnAttr(Attribute::AlwaysInline);
  return f;
}

// Add a function       primitive_<op>_<type>
// with the appropriate signature
static Function*
addConcretePrimitiveFunctionTo(Module* m, const char* op, const Type* ty) {
  Function* f = getConcretePrimitiveFunction(m, op, ty);

  std::vector<Value*> args;
  for (Function::arg_iterator it = f->arg_begin();
                             it != f->arg_end(); ++it) {
    llvm::Value& v = *it;
    args.push_back(&v);
  }

  BasicBlock* bb = BasicBlock::Create(getGlobalContext(), "entry", f);
  IRBuilder<> fBuilder(getGlobalContext());
  fBuilder.SetInsertPoint(bb);
  llvm::Value* rv = codegenPrimitiveOperation(op, fBuilder, args);
  fBuilder.CreateRet(rv);

  const std::string& name = f->getNameStr();
  const llvm::Type* fty = f->getType();
  // We get a pointer-to-whatever-function type, because f is a global
  // value (therefore ptr), but we want just the function type.
  if (const PointerType* pty = dyn_cast<PointerType>(fty)) {
    fty = pty->getElementType();
  }

  if (gPrintLLVMImports) {
    llvm::outs() << "\t" << name << " :: " << str(fty) << "\n";
  }
  return f;
}

void
addLLVMIntrinsic(Module* m, llvm::Intrinsic::ID id) {
  std::string funcName =
        pystring::replace(llvm::Intrinsic::getName(id), ".", "_");

  const FunctionType* ft = llvm::Intrinsic::getType(m->getContext(), id);
  Function* f = Function::Create(ft, Function::PrivateLinkage, funcName, m);
  f->setCallingConv(llvm::CallingConv::Fast);
  f->addFnAttr(Attribute::AlwaysInline);

  BasicBlock* bb = BasicBlock::Create(m->getContext(), "entry", f);
  IRBuilder<> fBuilder(getGlobalContext());
  fBuilder.SetInsertPoint(bb);
  llvm::Value* rv = fBuilder.CreateCall(llvm::Intrinsic::getDeclaration(m, id));
  fBuilder.CreateRet(rv);
}

void
addConcretePrimitiveFunctionsTo(Module* m) {
  std::vector<const Type*> types;
  types.push_back(Type::getInt32Ty(getGlobalContext()));
  types.push_back(Type::getInt64Ty(getGlobalContext()));

  for (int i = 0; sOps[i] != NULL; ++i) {
    for (size_t j = 0; j < types.size(); ++j) {
      addConcretePrimitiveFunctionTo(m, sOps[i], types[j]);
    }
  }

  addConcretePrimitiveFunctionTo(m, "bitnot", Type::getInt1Ty(getGlobalContext()));
  addConcretePrimitiveFunctionTo(m, "sext_i64", Type::getInt32Ty(getGlobalContext()));
  addLLVMIntrinsic(m, llvm::Intrinsic::readcyclecounter);
}

// Add prototypes for module m's C-linkage functions to the linkee module.
void
putModuleMembersInInternalScope(const std::string& scopeName,
                                     Module* m, Module* linkee) {
  if (!m) return;

  // Collect type names from the module.
  const TypeSymbolTable & typeSymTab = m->getTypeSymbolTable();
  for (TypeSymbolTable::const_iterator it = typeSymTab.begin();
                                           it != typeSymTab.end(); ++it) {
    std::string name = (*it).first;
    const Type* ty   = (*it).second;

    if (gPrintLLVMImports) {
      outs() << "type " << name << " = " << str(ty) << "\n";
    }

    // TODO do we need to explicitly copy the type to the linkee?
    linkee->addTypeName(name, ty);
  }

  // Collect global variables from the module.
  for (Module::global_iterator it = m->global_begin();
                              it != m->global_end(); ++it) {
    const GlobalVariable& gv = *it;
    if (!gv.isConstant()) {
      outs() << "<internal>\tskipping non-const global\t" << gv.getName() << "\n";
      continue;
    }

    if (gPrintLLVMImports) {
      outs() << "<internal>\tglobal\t" << gv.getName() << "\n";
    }
    linkee->getOrInsertGlobal(gv.getName(), gv.getType());
  }

  // These functions will not be linked in, to keep the postlinked
  // Module as clean as possible.
  std::set<string> functionsToRemove;

  // Collect C-linkage function declarations from the module.
  // Functions with C++ linkage are not included.
  // Functions with definitions are only included if they are explicitly
  // marked (via a foster_ prefix) as being intended for inclusion.
  //
  // This allows a library wrapper to define functions that should be
  // included (such as those that concreteize macro definitions), and
  // also those which should not be included (such as
  // force_these_symbols_to_be_included()).
  for (Module::iterator it = m->begin(); it != m->end(); ++it) {
    const Function& f = *it;

    const string& name = f.getNameStr();
    bool isCxxLinkage = pystring::startswith(name, "_Z", 0)
                     || pystring::startswith(name, "__cxx_", 0);
    if (isCxxLinkage) continue;

    bool hasDef = !f.isDeclaration();
    if (hasDef) {
      if (!pystring::startswith(name, "foster_")) {
        // drop from original module
        functionsToRemove.insert(name);
        continue;
      }
    }

    const Type* ty = f.getType();
    // We get a pointer-to-whatever-function type, because f is a global
    // value (therefore ptr), but we want just the function type.
    if (const PointerType* pty = dyn_cast<PointerType>(ty)) {
      ty = pty->getElementType();
    }

    if (const FunctionType* fnty =
                                      dyn_cast<FunctionType>(ty)) {
      Value* decl = linkee->getOrInsertFunction(
          StringRef(name),
          fnty,
          f.getAttributes());

      if (gPrintLLVMImports) {
        outs() << "<internal>\t" << hasDef << "\t" << name << " \n";
      }
    } else {
      ASSERT(false) << "how could a function not have function type?!?";
    }
  }

  // Don't link in functions that were just included to force
  // LLVM to include declarations in the module in the first place.
  for (std::set<std::string>::iterator it = functionsToRemove.begin();
                         it != functionsToRemove.end(); ++it) {
    if (gPrintLLVMImports) {
      outs() << "not including function " << *it << "\n";
    }
    m->getFunctionList().erase(m->getFunction(*it));
  }
}

// Add module m's C-linkage functions in the global scopes,
// and also add prototypes to the linkee module.
void putModuleMembersInScope(Module* m, Module* linkee) {
  if (!m) return;

  for (Module::iterator it = m->begin(); it != m->end(); ++it) {
    const Function& f = *it;

    const string& name = f.getNameStr();
    bool isCxxLinkage = pystring::startswith(name, "_Z", 0);

    bool hasDef = !f.isDeclaration();
    if (hasDef && !isCxxLinkage
               && !pystring::startswith(name, "__cxx_", 0)) {
      // Ensure that, when parsing, function calls to this name will find it
      const Type* ty = f.getType();
      // We get a pointer-to-whatever-function type, because f is a global
      // value (therefore ptr), but we want just the function type.
      if (const PointerType* pty = dyn_cast<PointerType>(ty)) {
        ty = pty->getElementType();
      }

      if (const FunctionType* fnty =
                                      dyn_cast<FunctionType>(ty)) {
        // Ensure that codegen for the given function finds the 'declare'
        // TODO make lazy prototype?
        Value* decl = linkee->getOrInsertFunction(
            StringRef(name),
            fnty,
            f.getAttributes());

        if (gPrintLLVMImports) {
          outs() << "inserting variable in global scope: " << name << " : "
                 << str(fnty) << "\n";
        }
      } else {
        ASSERT(false) << "how could a function not have function type?!?";
      }
    }
  }
}

} // namespace foster

