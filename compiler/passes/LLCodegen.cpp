// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#define DEBUG_TYPE "foster-codegen"

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterTypeAST.h"

#include "passes/FosterLL.h"
#include "passes/CodegenPass-impl.h"

#include "llvm/IR/Attributes.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/InlineAsm.h"

#include "llvm/IR/Metadata.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
//#include "llvm/Analysis/DIBuilder.h"
//#include "llvm/Support/Dwarf.h"

#include <map>
#include <sstream>
#include <fstream>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::ConstantInt;
using llvm::Value;
using llvm::dyn_cast;

using foster::builder;
using foster::EDiag;
using foster::DDiag;

using std::vector;

STATISTIC(MEMCPY_FROM_GLOBAL_TO_HEAP, "[foster] statically emitted memcpy operations");

namespace foster {

void codegenLL(LLModule* prog, llvm::Module* mod, CodegenPassConfig config) {
  CodegenPass cp(mod, config);
  prog->codegenModule(&cp);
  cp.emitTypeMapListGlobal();
}

void deleteCodegenPass(CodegenPass* cp) { delete cp; }

} // namespace foster


char kFosterMain[] = "foster__main";
int  kUnknownBitsize = 999; // keep in sync with IntSizeBits in Base.hs

// {{{ Internal helper functions
bool tryBindArray(CodegenPass* pass, Value* base, Value*& arr, Value*& len);

namespace {

llvm::Type* getLLVMType(TypeAST* type) {
  ASSERT(type) << "getLLVMType must be given a non-null type!";
  return type->getLLVMType();
}

llvm::Type* slotType(llvm::Type* t) { return t->getContainedType(0); }
llvm::Type* slotType(llvm::Value* v) { return slotType(v->getType()); }

bool isLargishStructPointerTy(llvm::Type* ty) {
  if (llvm::PointerType* pt = llvm::dyn_cast<llvm::PointerType>(ty)) {
    if (llvm::StructType* st = llvm::dyn_cast<llvm::StructType>(pt->getElementType())) {
      return st->getNumElements() >= 2;
    }
  }
  return false;
}

bool isPointerToUnknown(Type* ty) {
  return ty->isPointerTy() &&
         slotType(ty)->isIntegerTy(kUnknownBitsize);
}

bool matchesExceptForUnknownPointers(Type* aty, Type* ety) {
  //DDiag() << "matchesExceptForUnknownPointers ? " << str(aty) << " =?= " << str(ety);
  if (aty == ety) return true;
  if (aty == foster_generic_coro_t || ety == foster_generic_coro_t) return true;
  
  if (aty->isPointerTy() && ety->isPointerTy()) {
    if (isPointerToUnknown(aty) || isPointerToUnknown(ety)) { return true; }
    return matchesExceptForUnknownPointers(slotType(aty), slotType(ety));
  }
  if (aty->getTypeID() != ety->getTypeID()) return false;

  if (aty->isIntegerTy() && ety->isIntegerTy()) {
    return llvm::cast<llvm::IntegerType>(aty)->getBitWidth()
        == llvm::cast<llvm::IntegerType>(ety)->getBitWidth();
  }
  // TODO vector types? metadata? floating point?
  if (aty->getNumContainedTypes() != ety->getNumContainedTypes()) return false;
  for (size_t i = 0; i < aty->getNumContainedTypes(); ++i) {
    if (! matchesExceptForUnknownPointers(aty->getContainedType(i),
                                          ety->getContainedType(i))) return false;
  }
  return true;
}

llvm::Value* emitBitcast(llvm::Value* v, llvm::Type* dstTy, llvm::StringRef msg = "") {
  llvm::Type* srcTy = v->getType();
  if (srcTy->isVoidTy()) {
    return getNullOrZero(dstTy);
  }
  if (isFunctionPointerTy(srcTy) && isLargishStructPointerTy(dstTy)) {
    ASSERT(false) << "cannot cast " << str(srcTy) << " to " << str(dstTy) << "\n" << str(v);
  }
  if (dstTy->isPointerTy() != srcTy->isPointerTy()) {
    builder.GetInsertBlock()->getParent()->dump();
    ASSERT(false) << "cannot cast " << str(srcTy) << " to " << str(dstTy) << "\ndue to pointer-type mismatch\n" << str(v);
  }

  return builder.CreateBitCast(v, dstTy, msg);
}

llvm::Value* emitGCWrite(CodegenPass* pass, Value* val, Value* base, Value* slot) {
  if (!base) base = getNullOrZero(builder.getInt8PtrTy());
  llvm::Constant* llvm_gcwrite = llvm::Intrinsic::getDeclaration(pass->mod,
                                                      llvm::Intrinsic::gcwrite);

/*
  llvm::outs() << "emitting GC write" << "\n";
  if (base) { 
    llvm::outs() << "  base is " << *base << "\n";
    llvm::outs() << "  base :: " << str(base->getType()) << "\n";
  }
  llvm::outs() << "   val is " << *val << "\n";
  llvm::outs() << "   val :: " << str(val->getType()) << "\n";
  llvm::outs() << "  slot is " << *slot << "\n";
  llvm::outs() << "  slot :: " << str(slot->getType()) << "\n";
*/

  Value* base_generic = builder.CreateBitCast(base, builder.getInt8PtrTy());
  Value* slot_generic = builder.CreateBitCast(slot, builder.getInt8PtrTy()->getPointerTo(0));
  Value*  val_generic = builder.CreateBitCast(val,  builder.getInt8PtrTy());
  return builder.CreateCall(llvm_gcwrite, { val_generic, base_generic, slot_generic });
}

// TODO (eventually) try emitting masks of loaded/stored heap pointers
// to measure performance overhead of high/low tags.

inline llvm::Value* emitNonVolatileLoad(llvm::Value* v, llvm::Twine name) {
  return builder.CreateLoad(v, false, name);
}

enum WriteSelector {
  WriteUnspecified,
  WriteKnownNonGC
};

llvm::Value* emitGCWriteOrStore(CodegenPass* pass,
                       llvm::Value* val,
                       llvm::Value* base,
                       llvm::Value* ptr,
                       WriteSelector w = WriteUnspecified) {
  //llvm::outs() << "logging write of " << *val <<
  //              "\n              to " << *ptr <<
  //              "\n     isNonGC = " << (w == WriteKnownNonGC) << "; val is ptr ty? " << val->getType()->isPointerTy() << "\n";
  bool useBarrier = val->getType()->isPointerTy()
        && !llvm::isa<llvm::AllocaInst>(ptr)
        && w != WriteKnownNonGC
        && pass->config.useGC;
  //maybeEmitCallToLogPtrWrite(pass, ptr, val, useBarrier);

  if (isPointerToType(ptr->getType(), val->getType())) {
    if (useBarrier) {
      return emitGCWrite(pass, val, base, ptr);
    } else {
      return builder.CreateStore(val, ptr, /*isVolatile=*/ false);
    }
  }

  builder.GetInsertBlock()->getParent()->dump();
  ASSERT(false) << "in basic block " << builder.GetInsertBlock()->getName() << ":\n"
          << "ELIDING STORE DUE TO MISMATCHED TYPES:\n"
          << "    ptr type: " << str(ptr->getType()) << "\n"
          << "    val type: " << str(val->getType()) << "\n"
          << "    val is  : " << str(val) << "\n"
          << "    ptr is  : " << str(ptr);
  return NULL;
}

llvm::Type* // nullable
needsBitcastToMediateUnknownPointerMismatch(llvm::Value* val, llvm::Value* ptr) {
  if (ptr->getType()->isPointerTy()
      && !isPointerToType(ptr->getType(), val->getType())) {
    auto eltTy = llvm::dyn_cast<llvm::PointerType>(ptr->getType())->getElementType();
    if (matchesExceptForUnknownPointers(val->getType(), eltTy)) {
      return eltTy;
    }
  }
  return nullptr;
}

llvm::Value* emitStore(CodegenPass* pass,
                       llvm::Value* val,
                       llvm::Value* ptr,
                       llvm::Value* base,
                       WriteSelector w = WriteUnspecified) {
  if (val->getType()->isVoidTy()) {
    val = getUnitValue();
  }

  if (auto eltTy = needsBitcastToMediateUnknownPointerMismatch(val, ptr)) {
    val = emitBitcast(val, eltTy, "specSgen");
  }

  return emitGCWriteOrStore(pass, val, base, ptr, w);
}

Value* emitCallToInspectPtr(CodegenPass* pass, Value* ptr) {
   llvm::Value* rmc = pass->mod->getFunction("inspect_ptr_for_debugging_purposes");
   ASSERT(rmc) << "couldnt find inspect_ptr_for_debugging_purposes";
   return markAsNonAllocating(builder.CreateCall(rmc, builder.CreateBitCast(ptr, builder.getInt8PtrTy())));
}

std::vector<llvm::Value*>
codegenAll(CodegenPass* pass, const std::vector<LLVar*>& args) {
  std::vector<llvm::Value*> vals;
  for (size_t i = 0; i < args.size(); ++i) {
    vals.push_back(args[i]->codegen(pass));
  }
  return vals;
}

bool isPointerToStruct(llvm::Type* ty) {
  return ty->isPointerTy() && llvm::isa<llvm::StructType>(slotType(ty));
}

llvm::Value* emitFakeComment(std::string s) {
  return new llvm::BitCastInst(builder.getInt32(0), builder.getInt32Ty(), s,
                               builder.GetInsertBlock());
}

bool isEnvPtr(llvm::Value* v) {
  return v->getName().startswith(".env");
}


////////////////////////////////////////////////////////////////////
//////////////////// Out-Of-Line Assertions ////////////////////////
/////////////////////////////////////////////////////////////////{{{

void assertRightNumberOfArgnamesForFunction(llvm::Function* F,
                                   const std::vector<std::string>& argnames) {
  ASSERT(argnames.size() == F->arg_size())
            << "error when codegenning proto " << F->getName()
            << "\n of type " << str(F->getType())
            << "; inArgs.size: " << argnames.size()
            << "; F.arg_size: " << F->arg_size() << "\n" << str(F);
}

void assertRightNumberOfArgsForFunction(llvm::Value* FV,
           llvm::FunctionType* FT, const std::vector<llvm::Value*>& valArgs) {
  ASSERT(FT->getNumParams() == valArgs.size())
            << "function arity mismatch for " << FV->getName()
            << "; got " << valArgs.size()
            << " args but expected " << FT->getNumParams();
}

void assertValueHasExpectedType(llvm::Value* argV, llvm::Type* expectedType,
                                llvm::Value* FV) {
    ASSERT(typesEq(argV->getType(), expectedType))
              << "\ntype mismatch: "
              << "\n had type         " << str(argV->getType())
              << "\n vs expected type " << str(expectedType)
              << "\nargV = " << str(argV)
              << "\nand base type " << str(FV->getType())
              << "\nfor base " << str(FV) << "\n";
}

void assertHaveCallableType(LLExpr* base, llvm::Type* FT, llvm::Value* FV) {
  ASSERT(FT) << "call to uncallable something "
             << base->tag << "\t" << base->type->tag
             << " of type " << str(base->type)
             << "\nFV: " << str(FV);
}

void assertHaveFunctionNamed(llvm::Function* f,
                             const std::string& fullyQualifiedSymbol,
                             CodegenPass* pass) {
  if (!f) {
   llvm::errs() << "Unable to find function in module named: "
                << fullyQualifiedSymbol << "\n";
   pass->valueSymTab.dump(llvm::errs());
   ASSERT(false) << "unable to find function " << fullyQualifiedSymbol;
  }
}

void assertCurrentFunctionReturnsUnitType() {
  ASSERT(getUnitValue()->getType() == builder.getCurrentFunctionReturnType())
     << "\n\tunit: " << str(getUnitValue()->getType())
     << "\n\tret: " << str(builder.getCurrentFunctionReturnType());
}

void assertHaveSameNumberOfArgsAndPhiNodes(const vector<llvm::Value*>& args,
                                           LLBlock* block) {
  ASSERT(args.size() == block->phiNodes.size())
        << "from " << builder.GetInsertBlock()->getName().str() << " : "
        << "to " << block->bb->getName().str() << " : "
        << "have " << args.size() << " args; "
        << "need " << block->phiNodes.size();
}

void assertValueHasSameTypeAsPhiNode(llvm::Value* v, LLBlock* block, int i) {
  ASSERT(v->getType() == block->phiNodes[i]->getType())
      << "Can't pass a value of type " << str(v->getType())
      << " to a phi node of type " << str(block->phiNodes[i]->getType())
      << "\n from value " << str(v) << " to block " << (block->block_id);
}

/// }}}

} // }}} namespace

// Implementation of CodegenPass helpers {{{

Value* getElementFromComposite(CodegenPass* pass, Value* compositeValue,
                               int indexValue, const std::string& msg, bool assumeImmutable=false) {
  ASSERT(indexValue >= 0);
  Value* idxValue = builder.getInt32(indexValue);
  Type* compositeType = compositeValue->getType();
  // To get an element from an in-memory object, compute the address of
  // the appropriate struct field and emit a load.
  
  if (llvm::isa<llvm::PointerType>(compositeType)) {
    Value* gep = getPointerToIndex(compositeValue, idxValue, (msg + ".subgep").c_str());

    if (assumeImmutable) {
      if (auto C = dyn_cast<llvm::ConstantExpr>(gep)) {
        if (auto GEP = llvm::cast<llvm::GetElementPtrInst>(C->getAsInstruction())) {
          if (auto GV = llvm::dyn_cast<llvm::GlobalVariable>(GEP->getPointerOperand())) {
            auto V = llvm::ConstantFoldLoadThroughGEPConstantExpr(GV->getInitializer(), C);
            if (V) {
              GEP->deleteValue();
              return V;
            }
          }
          GEP->deleteValue();
        }
      }
    }

    //maybeEmitCallToLogPtrRead(pass, gep);
    return emitNonVolatileLoad(gep, gep->getName() + "_ld");
  } else if (llvm::isa<llvm::StructType>(compositeType)) {
    return builder.CreateExtractValue(compositeValue, indexValue, (msg + "subexv").c_str());
  } else if (llvm::isa<llvm::VectorType>(compositeType)) {
    return builder.CreateExtractElement(compositeValue, idxValue, (msg + "simdexv").c_str());
  } else {
    EDiag() << "Cannot index into value type " << str(compositeType)
            << " with non-constant index " << str(idxValue);
  }
  return NULL;
}


CodegenPass::CodegenPass(llvm::Module* m, CodegenPassConfig config)
    : config(config), mod(m), currentProcName("<no proc yet>") {
  //dib = new DIBuilder(*mod);

  // N.B. we assume here that the input module m has already been linked
  // with the runtime library. We want to copy the function attributes that
  // Clang decorated the stdlib functions with, because we need some of the
  // attributes (such as "target-features=+sse2") to match, otherwise we'll
  // get incorrect results.
  llvm::Function* f = mod->getFunction("memalloc_cell");
  llvm::AttributeList attrs = f->getAttributes();
  auto FI = llvm::AttributeList::FunctionIndex;
  if (!attrs.hasAttribute(FI, "no-frame-pointer-elim")) {
    attrs = attrs.addAttribute(f->getContext(), FI,
      llvm::Attribute::get(f->getContext(), "no-frame-pointer-elim", "true"));
  }

  llvm::AttrBuilder toremove;
  toremove.addAttribute(
      llvm::Attribute::get(f->getContext(), "stack-protector-buffer-size", "8"));
  attrs = attrs.removeAttributes(f->getContext(), FI, toremove);
  this->fosterFunctionAttributes = attrs;
}

std::map<std::string, llvm::Type*> gDeclaredSymbolTypes;

llvm::Value* CodegenPass::lookupFunctionOrDie(const std::string&
                                                       fullyQualifiedSymbol) {
  //DDiag() << "looking up function " << fullyQualifiedSymbol;
  llvm::Function* f = mod->getFunction(fullyQualifiedSymbol);
  assertHaveFunctionNamed(f, fullyQualifiedSymbol, this);
  if (llvm::Type* expTy = gDeclaredSymbolTypes[fullyQualifiedSymbol]) {
    return builder.CreateBitCast(f, expTy);
  } else {
    return f;
  }
}

llvm::CallingConv::ID parseCallingConv(std::string cc) {
  if (cc == "fastcc") { return llvm::CallingConv::Fast; }
  ASSERT(cc == "ccc") << "unknown calling convention " << cc;
  return llvm::CallingConv::C;
}

llvm::Value* CodegenPass::emitFosterStringOfCString(Value* cstr, Value* sz) {
  bool init = false; // because we'll immediately memcpy.
  Value* hstr = this->emitArrayMalloc(TypeAST::i(8), sz, init);
  // This variable is dead after being passed to the TextFragment function,
  // so it does not need a GC root.

  Value* hstr_bytes; Value* len;
  if (tryBindArray(this, hstr, /*out*/ hstr_bytes, /*out*/ len)) {
    markAsNonAllocating(builder.CreateMemCpy(hstr_bytes,
                              cstr, sz, /*alignment*/ 4));
  } else { ASSERT(false); }

  // TODO null terminate?

  llvm::Value* textfragment = lookupFunctionOrDie("TextFragment");
  llvm::CallInst* call = builder.CreateCall(textfragment, { hstr, sz });
  call->setCallingConv(parseCallingConv("fastcc"));
  return call;
}

///}}}//////////////////////////////////////////////////////////////

///{{{//////////////////////////////////////////////////////////////
void codegenCoroPrimitives(CodegenPass* pass) {
  for (CodegenPass::LazyCoroPrimInfoMap::iterator
       it  = pass->lazyCoroPrimInfo.begin();
       it != pass->lazyCoroPrimInfo.end();
       ++it) {
    pass->emitLazyCoroPrimInfo( (*it).first.first.first,
                                (*it).second,
                                (*it).first.first.second,
                                (*it).first.second
                              );
  }
}

void registerKnownDataTypes(const std::vector<LLDecl*> datatype_decls,
                            CodegenPass* pass) {
  for (size_t i = 0; i < datatype_decls.size(); ++i) {
     LLDecl* d = datatype_decls[i];
     const std::string& typeName = d->getName();
     pass->dataTypeTagReprs[typeName] = CTR_OutOfLine;
  }
}

void createGCMapsSymbolIfNeeded(CodegenPass* pass) {
  if (!pass->config.useGC && !pass->config.standalone) {
    // The runtime needs a "foster__gcmaps" symbol for linking to succeed.
    // If we're not letting the GC plugin run, we'll need to emit it ourselves.
    new llvm::GlobalVariable(
    /*Module=*/      *(pass->mod),
    /*Type=*/        builder.getInt32Ty(),
    /*isConstant=*/  true,
    /*Linkage=*/     llvm::GlobalValue::ExternalLinkage,
    /*Initializer=*/ llvm::ConstantInt::get(builder.getInt32Ty(), 0),
    /*Name=*/        "foster__gcmaps",
    /*InsertBefore=*/NULL,
    /*ThreadLocal=*/ llvm::GlobalVariable::NotThreadLocal);
  }
}

void addExternDecls(const std::vector<LLDecl*> decls,
                    CodegenPass* pass) {
  for (auto d : decls) {
    if (pass->config.standalone || d->isForeign) {
      const std::string& declName = d->getName();
      TypeAST* fosterType = d->getType();

      llvm::outs() << "addExternDecls() saw " << declName << " :: " << str(fosterType) << "\n";

      if (const FnTypeAST* fnty = fosterType->castFnTypeAST()) {
        
        std::string autowrappedName = declName + std::string("__autowrap");
        if (auto existing = pass->mod->getFunction(autowrappedName)) {
          // If we import ``foo`` and we have a symbol ``foo__autowrap``, use it.
          codegenAutoWrapper(existing, fnty->getLLVMFnType(), declName, pass);
        } else if (llvm::Function* target = pass->mod->getFunction(declName)) {
          // We have ``foo`` but no ``foo__autowrap``.

          if ((!target->isDeclaration()) &&
                str(target->getType()->getContainedType(0))
                        != str(fnty->getLLVMFnType())) {
            // If the function we import has a different type than we expected,
            // automatically generate a wrapper to resolve the differences in types.
            // The original function gets renamed; the new function wraps the original
            // to provide the expected types to Foster code.
            // We only generate a wrapper when we can rename the definition;
            // renaming a declaration only causes problems when we link against the
            // real definition.
            target->setName(declName + std::string("__autowrap"));
            codegenAutoWrapper(target, fnty->getLLVMFnType(), declName, pass);
          } else {
            // Nothing to do; either the imported symbol already has the right type,
            // or it's a declaration instead a definition, so we can't rename it.
          }
        } else {
          // Unable to find either ``foo`` or ``foo__autowrap``; insert a declaration.
          pass->mod->getOrInsertFunction(declName, fnty->getLLVMFnType());
        }

      } else { // Not a function type, must be a regular global.

        auto g = pass->mod->getOrInsertGlobal(declName, fosterType->getLLVMType());
        if (d->autoDeref) {
          pass->autoDerefs[declName] = g;
        }
      }

    }
  }
}

///}}}//////////////////////////////////////////////////////////////
llvm::GlobalVariable* emitPrivateGlobal(CodegenPass* pass,
                                 llvm::Constant* val,
                                 const std::string& name);
llvm::GlobalVariable* emitGlobalNonArrayCell(CodegenPass* pass,
                                     llvm::GlobalVariable* typemap,
                                     llvm::Constant* body,
                                     const std::string& name);

void LLModule::codegenModule(CodegenPass* pass) {
  registerKnownDataTypes(datatype_decls, pass);

  addExternDecls(extern_val_decls, pass);

  if (!pass->config.standalone) {
    extendWithImplementationSpecificProcs(pass, procs);
  }

  for (auto& item : items) {
    //llvm::errs() << "Adding " << item->name << " to pass->globalValues\n";

    if (item->arrlit) {
      pass->globalValues[item->name] = item->arrlit->codegen(pass);
    } else {
      pass->globalValues[item->name] = item->lit->codegen(pass);
      pass->insertScopedValue(item->name, pass->globalValues[item->name]);
    }
  }

  // Ensure that the llvm::Function*s are created for all the function
  // prototypes, so that mutually recursive function references resolve.
  for (size_t i = 0; i < procs.size(); ++i) {
    // Ensure that the value is in the SymbolInfo entry in the symbol table.
    procs[i]->codegenProto(pass);
    // Associate the LLProc with its name so we can get its type later on.
    pass->procs[procs[i]->getCName()] = procs[i];
  }

  for (size_t i = 0; i < procs.size(); ++i) {
    // Codegen a global cell containing a closure pair for top-level functions.
    // The middle-end detects top-level functions which are used as closures
    // in a higher order way, and uses the name F.func instead of F, which
    // (at the end of this loop) gets mapped to the contents of the global cell.
    if (procs[i]->getCName() == "main") continue;

    std::vector<llvm::Constant*> cell_vals;
    auto Ffunc = pass->mod->getFunction(procs[i]->getCName() + ".proc");
    ASSERT(Ffunc) << "Couldn't find a closure wrapper for " << procs[i]->getCName();
    cell_vals.push_back(Ffunc);
    cell_vals.push_back(getNullOrZero(builder.getInt8PtrTy()));
    auto const_cell = llvm::ConstantStruct::getAnon(cell_vals);

    std::string cloname = procs[i]->getCName();

    CtorRepr ctorRepr; ctorRepr.smallId = -1;
    auto globalCell = emitGlobalNonArrayCell(pass,
                          pass->getTypeMapForType(TypeAST::i(64), ctorRepr, pass->mod, NotArray),
                          const_cell,
                          cloname + ".closure.cell");

    pass->globalValues[cloname] = builder.CreateConstGEP2_32(NULL, globalCell, 0, 2);
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegenProc(pass);
  }

  codegenCoroPrimitives(pass);

  createGCMapsSymbolIfNeeded(pass);
}

////////////////////////////////////////////////////////////////////
//////////////// LLProc, LLProto ///////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

bool isReturnTypeOK(llvm::Type* ty) {
  return true; // TODO verify not opaque
}

llvm::FunctionType*
getLLVMFunctionType(FnTypeAST* t, const std::string& procSymbol) {
  if (llvm::PointerType* pt =
   dyn_cast<llvm::PointerType>(getLLVMType(t))) {
    ASSERT(isReturnTypeOK(getLLVMType(t->getReturnType())))
        << "Cannot use opaque return type for proc " << procSymbol;
    return dyn_cast<llvm::FunctionType>(slotType(pt));
  } else {
    return NULL;
  }
}

void setFunctionArgumentNames(llvm::Function* F,
              const std::vector<std::string>& argnames) {
  assertRightNumberOfArgnamesForFunction(F, argnames);
  Function::arg_iterator AI = F->arg_begin();
  for (size_t i = 0; i != argnames.size(); ++i, ++AI) {
    AI->setName(argnames[i]);
  }
}

std::string getGlobalSymbolName(const std::string& sourceName) {
  if (sourceName == "main") {
    // libfoster contains a main() symbol that handles
    // initialization and shutdown/cleanup of the runtime,
    // calling this symbol in between.
    return kFosterMain;
  }
  return sourceName;
}

template<typename T>
void vectorAppend(std::vector<T>& target, const std::vector<T>& other) {
  target.insert(target.end(), other.begin(), other.end());
}

// We'll generate a wrapper for every toplevel procedure, even if it's not
// needed, and rely on LLVM's dead value elimination to remove the cruft.
void codegenClosureWrapper(llvm::Function* F, llvm::CallingConv::ID cc,
                           llvm::GlobalValue::LinkageTypes linkage,
                           std::string symbolName, CodegenPass* pass) {
    auto FT = F->getFunctionType();
    std::vector<llvm::Type*> argTys;
    argTys.push_back(builder.getInt8PtrTy());
    for (size_t i = 0; i < FT->getNumParams(); ++i) { argTys.push_back(FT->getParamType(i)); }
    auto FfuncT = llvm::FunctionType::get(FT->getReturnType(), argTys, false);
    std::string funcSymbolName = symbolName + ".proc";
    auto Ffunc = Function::Create(FfuncT, linkage, funcSymbolName, pass->mod);

    Ffunc->setCallingConv(parseCallingConv("fastcc"));

    Ffunc->arg_begin()->setName("env");
    pass->addEntryBB(Ffunc);
    std::vector<llvm::Value*> args;
    auto skipEnv = Ffunc->arg_begin(); skipEnv++;
    while (skipEnv != Ffunc->arg_end()) { args.push_back(&*skipEnv); ++skipEnv; }

    auto callInst = builder.CreateCall(F, args);
    callInst->setTailCall(true);
    callInst->setCallingConv(cc);

    if (callInst->getType()->isVoidTy()) {
      builder.CreateRetVoid();
    } else {
      builder.CreateRet(callInst);
    }
    pass->markFosterFunction(Ffunc);
}

void LLProc::codegenProto(CodegenPass* pass) {
  std::string symbolName = getGlobalSymbolName(this->getCName());

  llvm::FunctionType* FT = getLLVMFunctionType(this->getFnType(), symbolName);

  llvm::GlobalValue::LinkageTypes linkage = this->getFunctionLinkage();
  llvm::CallingConv::ID cc = this->type->getCallingConventionID();
  if (symbolName == kFosterMain) {
    // No args, returning void...
    FT = llvm::FunctionType::get(builder.getVoidTy(), false);
    linkage = llvm::GlobalValue::ExternalLinkage;
    cc      = llvm::CallingConv::C;
  }

  if (pass->config.standalone) {
    linkage = llvm::GlobalValue::ExternalLinkage;
    cc      = llvm::CallingConv::C;
  }

  ASSERT(FT) << "expecting top-level proc to have FunctionType!";
  this->F = Function::Create(FT, linkage, symbolName, pass->mod);
  ASSERT(F) << "function creation failed for proto " << this->getName();
  ASSERT(F->getName() == symbolName) << "redefinition of function " << symbolName;

  setFunctionArgumentNames(F, this->getFunctionArgNames());

  F->setCallingConv(cc);

  codegenClosureWrapper(F, cc, linkage, symbolName, pass);
}

////////////////////////////////////////////////////////////////////

void LLProc::codegenProc(CodegenPass* pass) {
  ASSERT(this->F != NULL) << "LLModule should codegen proto for " << getName();
  pass->currentProcName = getName();

  assertRightNumberOfArgnamesForFunction(F, this->getFunctionArgNames());

  pass->addEntryBB(F);
  CodegenPass::ValueScope* scope = pass->newScope(this->getName());

  //DDiag() << "codegennign blocks for fn " << F->getName();
  this->codegenToFunction(pass, F);
  pass->popExistingScope(scope);
}

///}}}//////////////////////////////////////////////////////////////

void CodegenPass::scheduleBlockCodegen(LLBlock* b) {
  if (worklistBlocks.tryAdd(b->block_id, b)) {
    // added new block
  } // else block was already scheduled
}

// We shouldn't get any such things from the middle-end.
void checkForUnusedEmptyBasicBlocks(llvm::Function* F) {
  for(auto& BB : *F) {
    ASSERT(! (BB.empty() && BB.use_empty()) );
  }
}

void initializeBlockPhis(LLBlock* block) {
  builder.SetInsertPoint(block->bb);
  for (size_t i = 0; i < block->phiVars.size(); ++i) {
    block->phiNodes.push_back(
           builder.CreatePHI(getLLVMType(block->phiVars[i]->type),
                        block->numPreds, block->phiVars[i]->getName()));
  }
}

Value* createUnboxedTuple(const std::vector<Value*>& vals);

llvm::Value* allocateSlot(CodegenPass* pass, LLVar* rootvar) {
  llvm::Type* ty = getLLVMType(rootvar->type);
  if (ty->isPointerTy()) {
    llvm::AllocaInst* slot = CreateEntryAlloca(ty, rootvar->getName());
    if (pass->config.useGC) { markGCRoot(slot, pass); }
    return slot;
  } else {
    // We need to wrap the non-pointer type with its metadata so the GC will
    // know how to trace the stack slot.
    CtorRepr ctorRepr; ctorRepr.smallId = -1;
    if (const StructTypeAST* sty = rootvar->type->castStructTypeAST()) {
      registerStructType(sty, "unboxed_tuple", ctorRepr, pass->mod);
    }
    llvm::GlobalVariable* typemap = pass->getTypeMapForType(rootvar->type, ctorRepr, pass->mod, NotArray);
    auto padded_ty = llvm::StructType::get(foster::fosterLLVMContext,
                                            { builder.getInt64Ty(), builder.getInt64Ty(), ty });
    llvm::AllocaInst* slot = CreateEntryAlloca(padded_ty, rootvar->getName());
    slot->setAlignment(16);
    if (pass->config.useGC) { markGCRoot(slot, pass); }
    builder.CreateStore(builder.CreatePtrToInt(typemap, builder.getInt64Ty()),
                        getPointerToIndex(slot, builder.getInt32(1), ""));
    return getPointerToIndex(slot, builder.getInt32(2), "past_tymap");
  }

}

void LLProcCFG::codegenToFunction(CodegenPass* pass, llvm::Function* F) {
  pass->fosterBlocks.clear();

  // Pre-allocate all our GC roots.
  for (size_t i = 0; i < gcroots.size(); ++i) {
    Value* slot = allocateSlot(pass, gcroots[i]);
    pass->insertScopedValue(gcroots[i]->getName(), slot);
  }

  // Create all the basic blocks before codegenning any of them.
  for (size_t i = 0; i < blocks.size(); ++i) {
    LLBlock* bi = blocks[i];
    pass->fosterBlocks[bi->block_id] = bi;
    bi->bb = BasicBlock::Create(builder.getContext(), bi->block_id, F);
    ASSERT(bi->block_id == bi->bb->getName())
                     << "function can't have two blocks named " << bi->block_id;
  }

  ASSERT(blocks.size() > 0) << F->getName() << " had no blocks!";

  // Create phi nodes in all the blocks,
  // and make them available via block->phiNodes.
  llvm::BasicBlock* savedBB = builder.GetInsertBlock();
  for (size_t i = 0; i < blocks.size(); ++i) {
    initializeBlockPhis(blocks[i]);
  }

  // Make sure we branch from the entry block to the first 'computation' block
  // which will either be a case analysis on the env parameter, or postalloca.
  builder.SetInsertPoint(savedBB);
  LLBr br(blocks[0]->block_id);
  if (!F->arg_empty()) {
    llvm::Argument* firstArg = &*F->arg_begin();
    if (isEnvPtr(firstArg)) {
      br.args.push_back(new LLValueVar(firstArg));
    }
  }
  br.codegenTerminator(pass);

  pass->worklistBlocks.clear();
  pass->scheduleBlockCodegen(blocks[0]);
  while (!pass->worklistBlocks.empty()) {
    LLBlock* b = pass->worklistBlocks.get();
    b->codegenBlock(pass);
  }

  checkForUnusedEmptyBasicBlocks(F);

  pass->markFosterFunction(F);
}

////////////////////////////////////////////////////////////////////

void LLBlock::codegenBlock(CodegenPass* pass) {
  builder.SetInsertPoint(bb);
  for (size_t i = 0; i < this->phiVars.size(); ++i) {
     pass->insertScopedValue(this->phiVars[i]->getName(), this->phiNodes[i]);
  }
  for (size_t i = 0; i < this->mids.size(); ++i) {
    this->mids[i]->codegenMiddle(pass);
  }
  this->terminator->codegenTerminator(pass);
}

////////////////////////////////////////////////////////////////////
////////////////////////// Terminators /////////////////////////////
/////////////////////////////////////////////////////////////////{{{

void LLRetVoid::codegenTerminator(CodegenPass* pass) {
  builder.CreateRetVoid();
}

Value* emitFnArgCoercions(Value*, Type*);

void LLRetVal::codegenTerminator(CodegenPass* pass) {
  llvm::Value* rv = this->val->codegen(pass);
  bool fnReturnsVoid = builder.getCurrentFunctionReturnType()->isVoidTy();
  if (!fnReturnsVoid && rv->getType()->isVoidTy()) {
     // Assumption is that our return type might be {}* (i.e. unit)
     // but the last thing we called returned void.
     assertCurrentFunctionReturnsUnitType();
     rv = getUnitValue();
  }

  if (fnReturnsVoid) {
    builder.CreateRetVoid();
  } else {
    builder.CreateRet(emitFnArgCoercions(rv, builder.getCurrentFunctionReturnType()));
  }
}

void passPhisAndBr(LLBlock* block, const vector<llvm::Value*>& args) {
  assertHaveSameNumberOfArgsAndPhiNodes(args, block);
  std::stringstream ss; ss << "br args:";
  for (size_t i = 0; i < args.size(); ++i) {
    llvm::Value* v = args[i];
    if (v->getType()->isVoidTy()) {
      v = getUnitValue(); // Can't pass a void value!
    }
    if ((v->getType() != block->phiNodes[i]->getType())
        && matchesExceptForUnknownPointers(v->getType(), block->phiNodes[i]->getType())
        //&& (isPointerToUnknown(v->getType()) || isPointerToUnknown(block->phiNodes[i]->getType()))
        ) {
      v = emitBitcast(v, block->phiNodes[i]->getType(), "genXspec");
    }
    assertValueHasSameTypeAsPhiNode(v, block, i);
    block->phiNodes[i]->addIncoming(v, builder.GetInsertBlock());
    ss << " " << v->getName().str() << ";";
  }
  if (!args.empty()) { emitFakeComment(ss.str()); }
  builder.CreateBr(block->bb);
}

void LLBr::codegenTerminator(CodegenPass* pass) {
  LLBlock* block = pass->lookupBlock(this->block_id);

  if (false && this->args.empty()) {
    llvm::outs() << "{{{ Empty args!";
    llvm::outs() << "    block_id: " << block_id << "\n";
    llvm::outs() << "    parent: " <<  builder.GetInsertBlock()->getParent()->getName().str() << "\n";
    llvm::outs() << "}}}\n";
  }
  if (this->args.empty() && (llvm::StringRef(block_id).startswith(
                        builder.GetInsertBlock()->getParent()->getName().str())
                          || llvm::StringRef(block_id).startswith("loophdr.")
                          || llvm::StringRef(block_id).startswith("effect_handler.go")))
  { // The "first" branch into the postalloca won't pass any actual args, so we
    // want to use the "real" function args (leaving out the invariant env ptr).
    // Other branches to postalloca will pass the new values for the arg slots.
    std::vector<llvm::Value*> args;
    Function* F = builder.GetInsertBlock()->getParent();
    for (Function::arg_iterator AI = F->arg_begin(); AI != F->arg_end(); ++AI) {
      if (!isEnvPtr(&*AI)) { args.push_back(&*AI); }
    }
    passPhisAndBr(block, args);
  } else {
    passPhisAndBr(block, codegenAll(pass, this->args));
  }
}

////////////////////////////////////////////////////////////////////

void addAndEmitTo(Function* f, BasicBlock* bb) {
  f->getBasicBlockList().push_back(bb);
  builder.SetInsertPoint(bb);
}

ConstantInt* getTagForCtorId(const CtorId& c) {
         if (c.typeName == "Bool")  { return builder.getInt1( c.ctorRepr.smallId);
  } else if (c.typeName == "Int16") { return builder.getInt16(c.ctorRepr.smallId);
  } else if (c.typeName == "Int32") { return builder.getInt32(c.ctorRepr.smallId);
  } else if (c.typeName == "Int64") { return builder.getInt64(c.ctorRepr.smallId);
  } else if (c.typeName == "Word")  { return is32Bit()
                                           ? builder.getInt32(c.ctorRepr.smallId)
                                           : builder.getInt64(c.ctorRepr.smallId);
  } else                            { return builder.getInt8( c.ctorRepr.smallId); }
}

llvm::Value* emitCallGetCtorIdOf(CodegenPass* pass, llvm::Value* v) {
  llvm::Value* foster_ctor_id_of = pass->mod->getFunction("foster_ctor_id_of");
  ASSERT(foster_ctor_id_of != NULL);
  return markAsNonAllocating(builder.CreateCall(foster_ctor_id_of,
                             emitBitcast(v, builder.getInt8PtrTy())));
}

void codegenSwitch(CodegenPass* pass, LLSwitch* sw, llvm::Value* insp_tag) {
  BasicBlock* defaultBB = (sw->defaultCase.empty())
                ? NULL
                : pass->lookupBlock(sw->defaultCase)->bb;

  BasicBlock* bbNoDefault = defaultBB ? NULL      :
                     BasicBlock::Create(builder.getContext(), "case_nodefault");
  BasicBlock* defOrContBB = defaultBB ? defaultBB : bbNoDefault;

  // Switch on the inspected value and add cases for each ctor considered.
  llvm::SwitchInst* si = builder.CreateSwitch(insp_tag, defOrContBB, sw->ctors.size());

  for (size_t i = 0; i < sw->ctors.size(); ++i) {
    BasicBlock* destBB = pass->lookupBlock(sw->blockids[i])->bb;
    ASSERT(destBB != NULL);

    // Compute the tag for the ctor associated with this branch.
    const CtorId& c = sw->ctors[i];
    ConstantInt* onVal = getTagForCtorId(c);

    ASSERT(si->getCondition()->getType() == onVal->getType())
        << "switch case and inspected value had different types!\n"
        << "SwitchCase ctor " << (i+1) << " of " << sw->ctors.size()
           << ": " << c.typeName << "." << c.ctorName << "#" << c.ctorRepr.smallId
        << "\ncond type: " << str(si->getCondition()->getType())
                      << "; val type: " << str(onVal->getType());

    si->addCase(onVal, destBB);
  }

  if (bbNoDefault) {
    Function *F = builder.GetInsertBlock()->getParent();
    addAndEmitTo(F, bbNoDefault);
    emitFosterAssert(pass->mod, llvm::ConstantInt::getTrue(builder.getContext()),
                   "control passed to llvm-generated default block -- bad!");
    builder.CreateUnreachable();
  }
}

llvm::Value* emitTagOfValue(CodegenPass* pass, llvm::Value* inspected,
                            CtorTagRepresentation ctr) {
  switch (ctr) {
  case CTR_BareValue: return inspected;
  case CTR_OutOfLine: return emitCallGetCtorIdOf(pass, inspected);
  case CTR_MaskWith3: {
    llvm::Value* truncated = builder.CreatePtrToInt(inspected, builder.getInt8Ty());
                      return builder.CreateAnd(truncated, 0x7); }
  }
  ASSERT(false) << "unknown tag representation in LLSwitch::codegen!"; return NULL;
}

void LLSwitch::codegenTerminator(CodegenPass* pass) {
  ASSERT(ctors.size() == blockids.size());
  ASSERT(ctors.size() >= 1);

  llvm::Value* inspected = this->var->codegen(pass);
  codegenSwitch(pass, this, emitTagOfValue(pass, inspected, this->ctr));
}

///}}}//////////////////////////////////////////////////////////////

llvm::Value* LLBitcast::codegen(CodegenPass* pass) {
  llvm::Value* v = var->codegen(pass);
  llvm::Type* tgt = getLLVMType(this->type);
  if (v->getType()->isVoidTy() && tgt == getUnitType()->getLLVMType()) {
    // Can't cast a void value to a unit value,
    // but we can manufacture a unit ptr...
    return llvm::ConstantPointerNull::getNullValue(tgt);
  } else return (v->getType() == tgt) ? v : emitBitcast(v, tgt);
}

void LLGCRootInit::codegenMiddle(CodegenPass* pass) {
  llvm::Value* v    = src->codegen(pass);
  llvm::Value* slot = root->codegen(pass);
  if (pass->config.emitLifetimeInfo) {
    markAsNonAllocating(builder.CreateLifetimeStart(slot));
  }

  emitStore(pass, v, slot, nullptr, WriteKnownNonGC);
}

void LLGCRootKill::codegenMiddle(CodegenPass* pass) {
  llvm::Value* slot = root->codegen(pass);
  if (this->doNullOutSlot &&
      pass->config.killDeadSlots) { storeNullPointerToSlot(slot); }
  if (pass->config.emitLifetimeInfo) {
     markAsNonAllocating(builder.CreateLifetimeEnd(slot));
  }
}

void LLRebindId::codegenMiddle(CodegenPass* pass) {
  pass->insertScopedValue(from, to->codegen(pass));
}

////////////////////////////////////////////////////////////////////
/////////////// LLDeref, LLStore, LLLetVals ////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* emitGCRead(CodegenPass* pass, Value* base, Value* slot) {
  if (!base) base = getNullOrZero(builder.getInt8PtrTy());
  llvm::Constant* llvm_gcread = llvm::Intrinsic::getDeclaration(pass->mod,
                                                      llvm::Intrinsic::gcread);
  llvm::outs() << "emitting GC read" << "\n";
  llvm::outs() << "  base is " << *base << "\n";
  llvm::outs() << "  slot is " << *slot << "\n";

  Value* base_generic = builder.CreateBitCast(base, builder.getInt8PtrTy());
  Value* slot_generic = builder.CreateBitCast(slot, builder.getInt8PtrTy()->getPointerTo(0));
  Value* val_generic = builder.CreateCall(llvm_gcread, { base_generic, slot_generic });
  return builder.CreateBitCast(val_generic, slot->getType()->getPointerElementType());
}

llvm::Value* LLDeref::codegen(CodegenPass* pass) {
  llvm::Value* ptr = base->codegen(pass);
  if (isTraced && !llvm::isa<llvm::AllocaInst>(ptr) && pass->config.useGC) {
    return emitGCRead(pass, nullptr, ptr);
  } else {
    return emitNonVolatileLoad(ptr, "deref");
  }
}

llvm::Value* LLStore::codegen(CodegenPass* pass) {
  llvm::Value* val  = v->codegen(pass);
  llvm::Value* slot = r->codegen(pass);
  if (isTraced && pass->config.useGC) {
    return emitGCWrite(pass, val, slot, slot);
  } else {
    return emitGCWriteOrStore(pass, val, slot, slot, WriteKnownNonGC);
  }
}

////////////////////////////////////////////////////////////////////

void trySetName(llvm::Value* v, const string& name) {
  if (v->getType()->isVoidTy()) {
    // Can't assign a name to void values in LLVM.
  } else if (isFunctionPointerTy(v->getType())) {
    // Don't want to rename functions!
  } else {
    v->setName(name);
  }
}

void LLLetVals::codegenMiddle(CodegenPass* pass) {
  for (size_t i = 0; i < exprs.size(); ++i) {
    Value* b = exprs[i]->codegen(pass);
    trySetName(b, names[i]);
    pass->insertScopedValue(names[i], b);
  }
}

///}}}///////////////////////////////////////////////////////////////

llvm::Value* LLCoroPrim::codegen(CodegenPass* pass) {
  llvm::Type* r = retType->getLLVMType();
  llvm::Type* a = typeArg->getLLVMType();
  if (this->primName == "coro_yield") { return pass->emitCoroYieldFn(r, a); }
  if (this->primName == "coro_invoke") { return pass->emitCoroInvokeFn(r, a); }
  if (this->primName == "coro_create") { return pass->emitCoroCreateFn(retType, typeArg); }
  if (this->primName == "coro_isdead") { 
    auto orig = pass->mod->getFunction("foster_coro_isdead");
    auto newty = rawPtrTo(llvm::FunctionType::get(builder.getInt1Ty(), 
                                  { getHeapPtrTo(foster_generic_split_coro_ty) }, false));
    llvm::outs() << "trying to cast " << str(orig->getType()) << "\nto\n" << str(newty) << "\n";
    return builder.CreateBitCast(orig, newty);
  }
  if (this->primName == "coro_parent") {
    auto fn = Function::Create(
      /*Type=*/    llvm::FunctionType::get(
                    /*Result=*/   getHeapPtrTo(foster_generic_coro_t),
                    /*Params=*/   { },
                    /*isVarArg=*/ false),
      /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
      /*Name=*/    ".coro_parent", pass->mod);

    fn->setCallingConv(llvm::CallingConv::Fast);
    pass->markFosterFunction(fn);

      
    BasicBlock* prevBB = builder.GetInsertBlock();
    pass->addEntryBB(fn);
    builder.CreateRet(
      builder.CreateBitCast(pass->getCurrentCoroParent(),
        getHeapPtrTo(foster_generic_coro_t)));
    if (prevBB) {
      builder.SetInsertPoint(prevBB);
    }

    return fn;
  }
  ASSERT(false) << "unknown coro prim: " << this->primName;
  return NULL;
}

////////////////////////////////////////////////////////////////////
//////////////////// Literals and variables ////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLBool::codegen(CodegenPass* pass) {
  return builder.getInt1(this->boolValue);
}

llvm::Value* LLFloat::codegen(CodegenPass* pass) {
  ASSERT(this->type) << "LLFloat was missing its type...";
  return llvm::ConstantFP::get(getLLVMType(this->type), this->doubleValue);
}

llvm::Constant* emitConstantArrayTidy(uint64_t size,
                                      llvm::Constant* arrValues) {
    std::vector<llvm::Constant*> tidy_vals;
    tidy_vals.push_back(llvm::ConstantInt::get(builder.getInt64Ty(), size));
    tidy_vals.push_back(arrValues);
    return llvm::ConstantStruct::getAnon(tidy_vals);
}

llvm::GlobalVariable* emitPrivateGlobal(CodegenPass* pass,
                                 llvm::Constant* val,
                                 const std::string& name) {
  llvm::GlobalVariable* globalVar = new llvm::GlobalVariable(
      /*Module=*/      *(pass->mod),
      /*Type=*/        val->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     llvm::GlobalValue::PrivateLinkage,
      /*Initializer=*/ val,
      /*Name=*/        name);
  globalVar->setAlignment(16);
  return globalVar;
}

llvm::GlobalVariable* emitGlobalArrayCell(CodegenPass* pass,
                                     llvm::GlobalVariable* typemap,
                                     llvm::Constant* body,
                                     const std::string& name) {
  std::vector<llvm::Constant*> cell_vals;
  std::vector<llvm::Constant*> pad_vals;
  if (is32Bit()) {
    pad_vals.push_back(builder.getInt64(0)); // alignment padding
    pad_vals.push_back(typemap);
    pad_vals.push_back(builder.getInt32(0)); // padding for typemap
  } else {
    pad_vals.push_back(builder.getInt64(0)); // alignment padding
    pad_vals.push_back(typemap);
  }
  cell_vals.push_back(llvm::ConstantStruct::getAnon(pad_vals));
  cell_vals.push_back(body);
  auto const_cell = llvm::ConstantStruct::getAnon(cell_vals);

  return emitPrivateGlobal(pass, const_cell, name);
}

llvm::GlobalVariable* emitGlobalNonArrayCell(CodegenPass* pass,
                                     llvm::GlobalVariable* typemap,
                                     llvm::Constant* body,
                                     const std::string& name) {
  std::vector<llvm::Constant*> cell_vals;
  cell_vals.push_back(builder.getInt64(0));
  cell_vals.push_back(typemap);
  cell_vals.push_back(body);
  auto const_cell = llvm::ConstantStruct::getAnon(cell_vals);

  auto rv = emitPrivateGlobal(pass, const_cell, name);
  //llvm::errs() << "emitGlobalNonArrayCell for " << name << " is " << str(rv) << "\n";
  return rv;
}

// Returns a tidy pointer.
llvm::Value* emitByteArray(CodegenPass* pass, llvm::StringRef bytes, llvm::StringRef cellname) {
  auto const_arr_tidy = emitConstantArrayTidy(bytes.size(), getConstantArrayOfString(bytes));

  CtorRepr ctorRepr; ctorRepr.smallId = -1;
  auto arrayGlobal = emitGlobalArrayCell(pass,
                        pass->getTypeMapForType(TypeAST::i(8), ctorRepr, pass->mod, YesArray),
                        const_arr_tidy,
                        cellname);

  auto rv = builder.CreateBitCast(getPointerToIndex(arrayGlobal, builder.getInt32(1), "cellptr"),
                                ArrayTypeAST::getZeroLengthTypeRef(TypeAST::i(8)), "arr_ptr");

  //llvm::errs() << "emitByteArray for " << bytes << ":\n    " << str(rv) << "\n";
  return rv;
}

llvm::Value* LLText::codegen(CodegenPass* pass) {
  Value* hstr = emitByteArray(pass, this->stringValue, ".txt_cell");
  Value* textfragment = pass->lookupFunctionOrDie("TextFragment");
  auto call = builder.CreateCall(textfragment, { hstr, builder.getInt32(this->stringValue.size()) });
  call->setCallingConv(parseCallingConv("fastcc"));
  return call;
}

llvm::Value* LLValueVar::codegen(CodegenPass* pass) {
  return this->val;
}

llvm::Value* LLGlobalSymbol::codegen(CodegenPass* pass) {
  // Closure conversion emits variables with procedure type; we'd be quite
  // remiss to use the nullary global closure wrapper instead of the proc!
  bool isProc = NULL != this->type->castFnTypeAST();

  if (auto v = pass->autoDerefs[this->name]) {
    return builder.CreateLoad(v, this->name);
  }

  auto v = pass->globalValues[this->name];
  if (!v || isProc) {
    if (!v) llvm::errs() << "falling back to global proc instead of closure for " << this->name << "\n";
    v = pass->lookupFunctionOrDie(this->name);
  }
  return v;
}


llvm::Value* LLGlobalSymbol::codegenCallee(CodegenPass* pass) {
  // But if we know we're codegenning for a call site, we can use the global
  // procedure directly, instead of its closure wrapper.
  return pass->lookupFunctionOrDie(this->name);
}

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  llvm::Value* v = pass->valueSymTab.lookup(getName());
  if (!v) {
    builder.GetInsertBlock()->getParent()->dump();
    pass->valueSymTab.dump(llvm::errs());
    ASSERT(false) << "\n\n\t\tUnknown variable name " << this->name << " in CodegenPass"
                  << " in block " << builder.GetInsertBlock()->getName()
                  << " of function " << pass->currentProcName;
  }
  return v;
}

llvm::Value* LLInt::codegen(CodegenPass* pass) {
  ASSERT(this->type && this->type->getLLVMType());
  llvm::Type* ty = this->type->getLLVMType();

  llvm::Value* small = ConstantInt::get(ty, this->getAPInt());

  // Our type could be an LLVM type, or an arbitrary precision int type.
  if (ty->isIntegerTy()) {
    return small;
  }

  // MP integer constants that do not fit in 64 bits
  // must be initialized from string data.
  ASSERT(false) << "codegen for int values that don't fit"
                << " in 64 bits not yet implemented";
  return NULL;
}

llvm::Value* LLKillProcess::codegen(CodegenPass* pass) {
  emitFosterAssert(pass->mod, builder.getFalse(), this->stringValue.c_str());
  return llvm::UndefValue::get(this->type->getLLVMType());
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLAllocate ////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

Value* allocateCell(CodegenPass* pass, TypeAST* type,
                    LLAllocate::MemRegion region,
                    CtorRepr ctorRepr, std::string srclines, bool init) {
  llvm::Type* ty = type->getLLVMType();

  switch (region) {
  case LLAllocate::MEM_REGION_STACK: {
    // TODO We could optimize the treatment of stack-allocated pointer-free data
    // by *not* using a gcroot, and allocating a slot instead of a cell (i.e. no
    // type map).

    //ASSERT(!containsGCablePointers(type, ty));

    // We enforce the invariant that the GC will scan but not attempt to copy
    // stack-allocated cells to the heap, by marking stack memory regions
    // as "stable" in foster_gc.cpp.
    llvm::GlobalVariable* ti = pass->getTypeMapForType(type, ctorRepr, pass->mod, NotArray);
    llvm::Type* typemap_type = ti->getType();
    // We include padding in order for the padding plus the typemap pointer to
    // be 16 bytes wide. This, in turn, ensures that we will align the payload
    // field to the necessary 16 bytes as well.
    // Also, because the heap_cell type in foster_gc_utils effectively treats
    // the header as a union of a pointer with uint64_t, we must include padding
    // after the typemap if the pointer is 32 bits.
    int ptrsize = builder.GetInsertBlock()->getModule()->getDataLayout().getPointerSize();
    llvm::Type* pad8 = llvm::ArrayType::get(builder.getInt8Ty(), 8);
    llvm::Type* pad  = llvm::ArrayType::get(builder.getInt8Ty(), 8 - ptrsize);
    llvm::StructType* sty = llvm::StructType::get(builder.getContext(), { pad8, typemap_type, pad, ty });
    llvm::AllocaInst* cell = CreateEntryAlloca(sty, "stackref");
    cell->setAlignment(16);
    llvm::Value* slot = getPointerToIndex(cell, builder.getInt32(3), "stackref_slot");
    builder.CreateStore(ti, getPointerToIndex(cell, builder.getInt32(1), "stackref_meta"));
    return slot;
  }
  case LLAllocate::MEM_REGION_GLOBAL_HEAP:
    return pass->emitMalloc(type, ctorRepr, srclines, init);

  default:
    ASSERT(false); return NULL;
  }
}

llvm::Value* emitNullaryCtor(CtorRepr ctorRepr, llvm::Type* ptrty) {
  llvm::Value* val = builder.getInt8(ctorRepr.smallId);
  return builder.CreateIntToPtr(val, ptrty);
}

// If we represent a constant array as a globally-allocated/static value,
// we simply won't call this function.
llvm::Value* LLAllocate::codegen(CodegenPass* pass) {
  if (this->arraySize != NULL) {
    Value* array_size = this->arraySize->codegen(pass);
    return pass->emitArrayMalloc(this->type, array_size, this->zero_init);
  } else {
    if (const StructTypeAST* sty = this->type->castStructTypeAST()) {
      registerStructType(const_cast<StructTypeAST*>(sty),
                         this->type_name, this->ctorRepr, pass->mod);
    }
    if (this->ctorRepr.isNullary) {
      emitFakeComment("nullary ctor!");
      return emitNullaryCtor(this->ctorRepr, getHeapPtrTo(this->type->getLLVMType()));
      // return null pointer, or'ed with ctor smallId, bitcast to appropriate result.
    } else {
      return allocateCell(pass, this->type, this->region, this->ctorRepr,
                                this->srclines, this->zero_init);
    }
  }
}

///}}}//////////////////////////////////////////////////////////////
//////////////// Arrays ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

bool tryBindArray(CodegenPass* pass, llvm::Value* base, Value*& arr, Value*& len) {
  // {i64, [0 x T]}*
  if (isPointerToStruct(base->getType())) {
    llvm::Type* sty = slotType(base);
    if (sty->getNumContainedTypes() == 2
      && sty->getContainedType(0) == builder.getInt64Ty()) {
      if (llvm::ArrayType* aty =
        llvm::dyn_cast<llvm::ArrayType>(sty->getContainedType(1))) {
        if (aty->getNumElements() == 0) {
          arr = getPointerToIndex(base, builder.getInt32(1), "arr");
          len = getElementFromComposite(pass, base, 0, "len");
          return true;
        }
      }
    }
  }
  return false;
}

Value* getArraySlot(Value* base, Value* idx, CodegenPass* pass, Type* ty,
                    bool dynCheck, const std::string& srclines) {
  Value* arr = NULL; Value* len;

  if (isPointerToUnknown(base->getType())) {
    auto arrayType = ArrayTypeAST::getSizedArrayTypeRef(ty, 0);
    base = emitBitcast(base, arrayType, "genAspec");
  }

  if (tryBindArray(pass, base, arr, len)) {
    if (dynCheck && !pass->config.disableAllArrayBoundsChecks) {
      emitFosterArrayBoundsCheck(pass->mod, idx, len, srclines);
    }
    ASSERT(idx->getType() != llvm::Type::getInt1Ty(builder.getContext()))
      << "Indexing using a boolean subscript is probably not what you want!";
    return getPointerToIndex(arr, idx, "arr_slot");
  } else {
    ASSERT(false) << "expected array, got " << str(base);
    return NULL;
  }
}


llvm::Value* LLArrayIndex::codegenARI(CodegenPass* pass, Value** outbase, Type* ty) {
  *outbase    = this->base ->codegen(pass);
  Value* idx  = this->index->codegen(pass);
  idx = builder.CreateZExt(idx, llvm::Type::getInt64Ty(builder.getContext()));
  ASSERT(static_or_dynamic == "static" || static_or_dynamic == "dynamic");
  return getArraySlot(*outbase, idx, pass, ty,
                      this->static_or_dynamic == "dynamic", this->srclines);
}

llvm::Value* LLArrayRead::codegen(CodegenPass* pass) {
  ASSERT(this->type) << "LLArrayRead with no type?";

  Value* base = NULL;
  Value* slot = ari->codegenARI(pass, &base, this->type->getLLVMType());
  //Value* val  = emitGCRead(pass, base, slot);
  Value* val  = emitNonVolatileLoad(slot, "arrayslot");
  return val;
}

  // base could be an array a[i] or a slot for a reference variable r.
  // a[i] should codegen to &a[i], the address of the slot in the array.
  // r    should codegen to the contents of the slot (the ref pointer value),
  //        not the slot address.

llvm::Value* LLArrayPoke::codegen(CodegenPass* pass) {
  Value* val  = this->value->codegen(pass);
  Value* base = NULL;
  Value* slot = ari->codegenARI(pass, &base, val->getType());

  if (auto eltTy = needsBitcastToMediateUnknownPointerMismatch(val, slot)) {
    val = emitBitcast(val, eltTy, "specSgen");
  }

  //builder.CreateStore(val, slot, /*isVolatile=*/ false);
  emitGCWriteOrStore(pass, val, base, slot);
  return getNullOrZero(getUnitType()->getLLVMType());
}


llvm::Value* LLArrayLength::codegen(CodegenPass* pass) {
  Value* val  = this->value->codegen(pass);
  Value* _bytes; Value* len;
  if (tryBindArray(pass, val, /*out*/ _bytes, /*out*/ len)) {
    // len already assigned.
  } else { ASSERT(false); }
  return len;
}

llvm::Value* LLByteArray::codegen(CodegenPass* pass) {
  return emitByteArray(pass, this->bytes, ".bytes_cell");
}

llvm::Value* LLArrayLiteral::codegen(CodegenPass* pass) {
  // Allocate a global array, with zeros/nulls for non-literal elements.
  //
  std::vector<llvm::Constant*> vals;
  std::vector<std::pair<llvm::Value*, unsigned> > ncvals;
  llvm::Type* elt_ty = this->elem_type->getLLVMType();
  for (unsigned i = 0; i < this->args.size(); ++i) {
    llvm::Value* v = this->args[i]->codegen(pass);
    if (llvm::Constant* c = llvm::dyn_cast<llvm::Constant>(v)) {
      vals.push_back(c);
    } else {
      vals.push_back(getNullOrZero(elt_ty));
      ncvals.push_back(std::make_pair(v, i));
    }
  }
  llvm::ArrayType* ty = llvm::ArrayType::get(elt_ty, vals.size());
  llvm::Constant* const_arr = llvm::ConstantArray::get(ty, vals);

  bool isImmutable = false;

  // If there are no non-constant values, then the array can be
  // allocated globally instead of on the heap, and we won't need
  // to copy any values.
  if (!arr || (ncvals.empty() && isImmutable)) {
    auto const_arr_tidy = emitConstantArrayTidy(vals.size(), const_arr);

    CtorRepr ctorRepr; ctorRepr.smallId = -1;
    auto arrayGlobal = emitGlobalArrayCell(pass,
                          pass->getTypeMapForType(this->elem_type, ctorRepr, pass->mod, YesArray),
                          const_arr_tidy,
                          ".arr_cell");

    return builder.CreateBitCast(getPointerToIndex(arrayGlobal, builder.getInt32(1), "cellptr"),
                                 ArrayTypeAST::getZeroLengthTypeRef(this->elem_type), "arr_ptr");
  } else {
    llvm::GlobalVariable* arrayGlobal = emitPrivateGlobal(pass, const_arr, ".arr");

    // Load the heap array which our forebears allocated unto us.
    llvm::Value* heap_arr = this->arr->codegen(pass);

    Value* heapmem; Value* _len;
    if (tryBindArray(pass, heap_arr, /*out*/ heapmem, /*out*/ _len)) {
      MEMCPY_FROM_GLOBAL_TO_HEAP++;
      // Memcpy from global to heap.

      int64_t size_in_bytes = pass->mod->getDataLayout().getTypeAllocSize(elt_ty)
                                  * this->args.size();
      
      builder.CreateMemCpy(heapmem, arrayVariableToPointer(arrayGlobal),
                                    size_in_bytes, 1);

      // Copy any non-constant values to the heap array
      //
      llvm::Type* i32 = builder.getInt32Ty();
      for (unsigned i = 0; i < ncvals.size(); ++i) {
        unsigned k  = ncvals[i].second;
        Value* val  = ncvals[i].first;
        Value* slot = getPointerToIndex(heapmem, llvm::ConstantInt::get(i32, k), "arr_slot");
        bool useBarrier = val->getType()->isPointerTy() && pass->config.useGC;
        //maybeEmitCallToLogPtrWrite(pass, slot, val, useBarrier);
        if (useBarrier) {
          emitGCWrite(pass, val, heapmem, slot);
        } else {
          builder.CreateStore(val, slot, /*isVolatile=*/ false);
        }
      }
    } else { ASSERT(false); }

    return heap_arr;
  }
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLTupleStore //////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLUnitValue::codegen(CodegenPass* pass) {
  return getUnitValue();
}

void copyValuesToStruct(CodegenPass* pass,
                        const std::vector<llvm::Value*>& vals,
                        llvm::Value* tup_ptr) {
  ASSERT(tup_ptr != NULL);
  ASSERT(isPointerToStruct(tup_ptr->getType()))
        << "copyValuesToStruct can't copy values to non-ptr-to-struct type "
        << str(tup_ptr->getType())
        << "\n" << str(tup_ptr);

  for (size_t i = 0; i < vals.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(nullptr, tup_ptr, 0, i, "gep");
    auto w = (pass->config.emitAllGCBarriers) ? WriteUnspecified : WriteKnownNonGC;
    emitStore(pass, vals[i], dst, tup_ptr, w);
  }
}

void LLTupleStore::codegenMiddle(CodegenPass* pass) {
  if (vars.empty()) return;
  llvm::Value* tup_ptr = this->storage->codegen(pass);
  copyValuesToStruct(pass, codegenAll(pass, this->vars), tup_ptr);
}

Value* createUnboxedTuple(const std::vector<Value*>& vals) {
  std::vector<llvm::Constant*> undefs;
  for (auto val : vals) { undefs.push_back(llvm::UndefValue::get(val->getType())); }
  // Rather than copying values to memory with GEP + store,
  // we "copy" values to a struct value which starts out with undef members.
  Value* rv = llvm::ConstantStruct::getAnon(undefs);
  for (size_t i = 0; i < vals.size(); ++i) { rv = builder.CreateInsertValue(rv, vals[i], i); }
  return rv;
}

Value* LLUnboxedTuple::codegen(CodegenPass* pass) {
  if (this->isStatic) {
    if (this->vars.empty()) {
        return getUnitValue();
    } else {
        std::vector<llvm::Constant*> consts;
        for (auto v : this->vars) {
          auto gv = pass->globalValues[v->getName()];
          if (auto cgv = dyn_cast<llvm::Constant>(gv)) {
            consts.push_back(cgv);
          } else {
            llvm::errs() << "var  " << v->getName() << " was not constant! ... " << *gv << "\n";
            exit(2);
          }
        }

        auto ct = llvm::ConstantStruct::getAnon(consts);
        CtorRepr ctorRepr; ctorRepr.smallId = 126;
        // TODO merge type maps for similar types?
        
        std::vector<int> noSkippedIndices;
        registerStructType(this->type->castStructTypeAST(), "cstupty", ctorRepr, pass->mod);
        auto typemap = pass->getTypeMapForType(this->type, ctorRepr, pass->mod, NotArray);
        auto globalCell = emitGlobalNonArrayCell(pass, typemap, ct, "cstup");
        llvm::Type* ty = getHeapPtrTo(getLLVMType(this->type)); // well, heap-formatted but not on-heap...
        llvm::outs() << "************ " << "type map for unboxed (?) type " << str(this->type) << "\n";
        return emitBitcast(builder.CreateConstGEP2_32(NULL, globalCell, 0, 2), ty);
        //return emitPrivateGlobal(pass, ct, "cstup");
        /*
    llvm::GlobalVariable* emitGlobalNonArrayCell(CodegenPass* pass,
                                        llvm::GlobalVariable* typemap,
                                        llvm::Constant* body,
                                        const std::string& name) {
                                        */

    }
  } else {
    return createUnboxedTuple(codegenAll(pass, this->vars));
  }
}


Value* LLGlobalAppCtor::codegen(CodegenPass* pass) {
  llvm::Type* ty = getLLVMType(this->type);
  if (this->args.empty()) {
    return emitNullaryCtor(this->ctor.ctorId.ctorRepr, ty);
  }

  std::vector<llvm::Constant*> consts;
  for (auto v : this->args) {
    auto gv = pass->globalValues[v->getName()];
    if (auto cgv = dyn_cast<llvm::Constant>(gv)) {
      consts.push_back(cgv);
    } else {
      llvm::errs() << "var  " << v->getName() << " was not constant! ... " << *gv << "\n";
      exit(2);
    }
  }

  llvm::GlobalVariable* ti = pass->getTypeMapForType(type, this->ctor.ctorId.ctorRepr, pass->mod, NotArray);
  auto ct = llvm::ConstantStruct::getAnon(consts);
  auto globalCell = emitGlobalNonArrayCell(pass, ti, ct, "csctor");
  return emitBitcast(builder.CreateConstGEP2_32(NULL, globalCell, 0, 2), ty);
}

///}}}//////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//////////////// Decision Trees ////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLOccurrence::codegen(CodegenPass* pass) {
  ASSERT(ctors.size() == offsets.size());

    std::stringstream ss; ss << "occ["<<this->var->getName()<<"](";
    for (size_t i = 0; i < offsets.size(); ++i) {
      ss << offsets[i] << ":";
      ss << ctors[i].ctorId.ctorName << "::";
    }
    ss << ")--";

    emitFakeComment(ss.str());


  llvm::Value* v = this->var->codegen(pass);

  for (size_t i = 0; i < offsets.size(); ++i) {
    // If we know that the subterm at this position was created with
    // a particular data constructor, emit a cast to that ctor's type.
    if (ctors[i].ctorStructType) {
      if (v->getType()->isPointerTy()) {
        v = emitBitcast(v, getHeapPtrTo(ctors[i].ctorStructType->getLLVMType()));
      } else {
        const CtorRepr& r = ctors[i].ctorId.ctorRepr;
        if (r.isTransparent && !r.isBoxed) {
        } else {
          EDiag() << "not bitcasting for occ with repr " << str(ctors[i].ctorId.ctorRepr) << " because of type mismatch between"
                  << str(v) << " :: " << str(v->getType()) << " and ptr to " << str(ctors[i].ctorStructType);
        }
      }
    }

    if (ctors[i].ctorId.ctorRepr.isTransparent && ctors[i].ctorId.ctorRepr.isBoxed) {
      emitFakeComment("eliding dereference due to transparent ctor representation of " + ctors[i].ctorId.ctorName);
      continue;
    }

    v = getElementFromComposite(pass, v, offsets[i], "switch_insp");
  }

  // Consider code like         case v of Some x -> ... x ...
  // when there's a type definition Maybe a = None | Some a.
  // v's source type is Maybe X, which (since we erase type parameters)
  // corresponds to the LLVM type Maybe.DT*. This will be refined to
  // { i999* }* when computing the occurrence for x. But x's physical type then
  // remains i999*, while it ought to be the translation of its source type, X.
  // This bitcast fixes the mismatch.
  return emitBitcast(v, getLLVMType(this->type), "occty");
}

///}}}//////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//////////////// Term Application //////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLCallPrimOp::codegen(CodegenPass* pass) {
  if (this->op == "lookup_handler_for_effect") {
    // Special cased because it's the only operation that needs tag.
    llvm::Value* fn = pass->mod->getFunction("foster__lookup_handler_for_effect");
    ASSERT(fn != NULL) << "NO foster__lookup_handler_for_effect IN MODULE! :(";

    llvm::CallInst* handler = builder.CreateCall(fn, { builder.getInt64(this->tag) }, "handler");
    return handler;
  }
  return pass->emitPrimitiveOperation(this->op, builder,
                                      codegenAll(pass, this->args));
}

llvm::Value* LLCallInlineAsm::codegen(CodegenPass* pass) {
  auto vs = codegenAll(pass, this->args);
  auto iasm = llvm::InlineAsm::get(this->ty->getLLVMFnType(),
                                   this->asmString,
                                   this->constraints,
                                   this->hasSideEffects);
  return builder.CreateCall(iasm, llvm::makeArrayRef(vs), "asmres");
}

llvm::Value* emitFnArgCoercions(Value* argV, llvm::Type* expectedType) {
  // This is a an artifact produced by the mutual recursion
  // of the environments of mutually recursive closures.
  if (  argV->getType() != expectedType
    &&  argV->getType() == getGenericClosureEnvType()->getLLVMType()) {
    DDiag() << "emitting bitcast gen2spec (exp: " << str(expectedType)
            << "); (actual: " << str(argV->getType()) << ")";
    argV = emitBitcast(argV, expectedType, "gen2spec");
  }

  // This occurs in polymorphic code.
  if ((argV->getType() != expectedType)
      && matchesExceptForUnknownPointers(argV->getType(), expectedType)) {
    // Example: matched { i64, [0 x i8] }* to %struct.foster_bytes* in call to prim_print_bytes_stdout
    //DDiag() << "matched " << str(argV->getType()) << " to " << str(expectedType) << " in call to " << FV->getName();
    argV = emitBitcast(argV, expectedType, "spec2gen");
  }

  // In code like  v = case _ of _ -> expect_i32 ...    _ -> ()
  // we'll be forced to bind the result of expect_i32 (which is actually
  // void, not unit) to a unit-typed variable. If so, just use a null pointer.
  if (argV->getType()->isVoidTy() && str(expectedType) == "{}*") {
    argV = getNullOrZero(llvm::dyn_cast<llvm::PointerType>(expectedType));
  }

  return argV;
}

llvm::Type* getClosureType(llvm::Type* retTy, const std::vector<Value*>& nonEnvArgs) {
  std::vector<llvm::Type*> argTys;
  argTys.push_back(builder.getInt8PtrTy());
  for (auto arg : nonEnvArgs) { argTys.push_back(arg->getType()); }
  return getHeapPtrTo(
            llvm::StructType::get(foster::fosterLLVMContext,
              { rawPtrTo(llvm::FunctionType::get(retTy, argTys, false)),
                builder.getInt8PtrTy() })
            );
}

llvm::Value* LLCall::codegen(CodegenPass* pass) {
  ASSERT(base != NULL) << "unable to codegen call due to null base";
  Value* FV = base->codegenCallee(pass);
  ASSERT(FV) << "unable to codegen call due to missing value for base";

  llvm::FunctionType* FT = NULL;
  std::vector<Value*> valArgs;
  bool fromClosure = false;

  llvm::CallingConv::ID callingConv = parseCallingConv(this->callconv);

  std::vector<Value*> nonEnvArgs;
  // Collect the args, performing coercions if necessary.
  for (auto arg : this->args) {
    nonEnvArgs.push_back(arg->codegen(pass));
  }

  if (Function* F = llvm::dyn_cast<Function>(FV)) {
    // Call to top level function
    callingConv = F->getCallingConv();
    FT = F->getFunctionType();
  } else if (isFunctionPointerTy(FV->getType())) {
    FT = dyn_cast<llvm::FunctionType>(slotType(FV));
  } else {
    if (!isPointerToStruct(FV->getType())) {
      // We can end up in this situation (trying to call a value that
      // has an unknown/generic type) because inlining does not "push through"
      // type coercions.
      FV = emitBitcast(FV, getClosureType(this->type->getLLVMType(), nonEnvArgs), "fnspec");
    }

    ASSERT(isPointerToStruct(FV->getType()));
    // Load code and env pointers from closure...
    llvm::Value* envPtr =
        getElementFromComposite(pass, FV, 1, "getCloEnv");
    FV = getElementFromComposite(pass, FV, 0, "getCloCode", true);

    FT = dyn_cast<llvm::FunctionType>(slotType(FV));
    // Pass env pointer as first parameter to function.
    valArgs.push_back(envPtr);
    fromClosure = true;
  }

  if (pass->config.countClosureCalls && fromClosure) {
    auto f  = pass->mod->getFunction("foster__record_closure_call");
    auto ci = builder.CreateCall(f);
    markAsNonAllocating(ci);
  }

  assertHaveCallableType(base, FT, FV);

  // Collect all args, performing coercions if needed.
  for (auto arg : nonEnvArgs) {
    llvm::Type* expectedType = FT->getParamType(valArgs.size());
    llvm::Value* argV = emitFnArgCoercions(arg, expectedType);
    assertValueHasExpectedType(argV, expectedType, FV);
    valArgs.push_back(argV);
  }

  assertRightNumberOfArgsForFunction(FV, FT, valArgs);

  // Give the instruction a name, if we can...

  auto callInst = builder.CreateCall(FV, llvm::makeArrayRef(valArgs));
  callInst->setCallingConv(callingConv);
  trySetName(callInst, "calltmp");

  // See CapnpIL.hs for a note on tail call marker safety.
  if (this->okToMarkAsTailCall && callingConv == llvm::CallingConv::Fast) {
    callInst->setTailCall(true);
  }

  if (!this->callMightTriggerGC) {
    markAsNonAllocating(callInst);
  } else {
    emitFakeComment("ABOVE CALL MAY TRIGGER GC...");
  }

  return callInst;
}

/// }}}

