// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterLL.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"

#include "passes/CodegenPass-impl.h"

#include "llvm/Attributes.h"
#include "llvm/CallingConv.h"
#include "llvm/LLVMContext.h"
#include "llvm/Intrinsics.h"

#include "llvm/Metadata.h"
//#include "llvm/Analysis/DIBuilder.h"
#include "llvm/Support/Dwarf.h"

#include "pystring/pystring.h"

#include <map>
#include <sstream>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::ConstantInt;
using llvm::getGlobalContext;
using llvm::Value;
using llvm::dyn_cast;

using foster::builder;
using foster::EDiag;

char kFosterMain[] = "foster__main";
int  kUnknownBitsize = 999; // keep in sync with IntSizeBits in Base.hs

namespace foster {

int8_t bogusCtorId(int8_t c) { return c; }

void codegenLL(LLModule* package, llvm::Module* mod) {
  CodegenPass cp(mod);
  package->codegenModule(&cp);
}

} // namespace foster

const llvm::Type* getLLVMType(TypeAST* type) {
  ASSERT(type) << "getLLVMType must be given a non-null type!";
  return type->getLLVMType();
}

const llvm::Type* slotType(llvm::Value* v) {
  return v->getType()->getContainedType(0);
}

inline
llvm::Value* emitNonVolatileLoad(llvm::Value* v, const llvm::Twine& name) {
  return builder.CreateLoad(v, false, name);
}

llvm::Value* emitStore(llvm::Value* val,
                       llvm::Value* ptr) {
  if (val->getType()->isVoidTy()) {
    return getUnitValue(); // Can't store a void!
  }

  if (isPointerToType(ptr->getType(), val->getType())) {
    return builder.CreateStore(val, ptr, /*isVolatile=*/ false);
  }

  ASSERT(false) << "ELIDING STORE DUE TO MISMATCHED TYPES:\n"
          << "ptr type: " << str(ptr->getType()) << "\n"
          << "val type: " << str(val->getType()) << "\n"
          << "val is  : " << str(val) << "\n"
          << "ptr is  : " << str(ptr);
  EDiag() << "unit is: " << str(getUnitValue());
  return builder.CreateBitCast(builder.getInt32(0),
                               builder.getInt32Ty(),
                               "elided store");
}

llvm::Value* emitStoreWithCast(llvm::Value* val,
                               llvm::Value* ptr) {
  if (!isPointerToType(ptr->getType(), val->getType())) {
    return emitStore(builder.CreateBitCast(val, slotType(ptr)), ptr);
  } else {
    return emitStore(val, ptr);
  }
}

llvm::Value* CodegenPass::autoload(llvm::Value* v) {
  if (this->needsImplicitLoad.count(v) == 1) {
    return emitNonVolatileLoad(v, v->getName() + ".autoload");
  } else return v;
}

// emit() serves as a wrapper around codegen()
// which inserts implicit loads as needed, and also
// verifies that the expected type matches the generated type.
// In most cases, emit() should be used instead of codegen().
llvm::Value* CodegenPass::emit(LLExpr* e, TypeAST* expectedType) {
  ASSERT(e != NULL) << "null expr passed to emit()!";
  llvm::Value* v = e->codegen(this);
  v = autoload(v);

  if (expectedType) {
    const llvm::Type* ty = getLLVMType(expectedType);
    if (!typesEq(v->getType(), ty)) {
      ASSERT(false) << "********* expected type " << str(ty)
                           << "; had type " << str(v->getType())
                           << "\n for value " << str(v);
    }
  }
  ASSERT(v != NULL);
  return v;
}

std::vector<llvm::Value*>
codegenAll(CodegenPass* pass, const std::vector<LLVar*>& args) {
  std::vector<llvm::Value*> vals;
  for (size_t i = 0; i < args.size(); ++i) {
    vals.push_back(pass->emit(args[i], NULL));
  }
  return vals;
}

void copyValuesToStruct(const std::vector<llvm::Value*>& vals,
                        llvm::Value* tup_ptr) {
  ASSERT(tup_ptr != NULL);
  for (size_t i = 0; i < vals.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(tup_ptr, 0, i, "gep");
    emitStore(vals[i], dst);
  }
}

////////////////////////////////////////////////////////////////////

void registerKnownDataTypes(const std::vector<LLDecl*> datatype_decls,
                            CodegenPass* pass) {
  for (size_t i = 0; i < datatype_decls.size(); ++i) {
     LLDecl* d = datatype_decls[i];
     const std::string& typeName = d->getName();
     DataTypeAST* dt = dynamic_cast<DataTypeAST*>(d->getType());
     pass->isKnownDataType[typeName] = dt;
  }
}

TupleTypeAST* getDataCtorType(DataCtor* dc) {
  return TupleTypeAST::get(dc->types);
}

llvm::Value* LLAppCtor::codegen(CodegenPass* pass) {
  DataTypeAST* dt = pass->isKnownDataType[this->ctorId.typeName];
  ASSERT(dt) << "unable to find data type for " << this->ctorId.typeName;
  DataCtor* dc = dt->getCtor(this->ctorId.smallId);
  TupleTypeAST* ty = getDataCtorType(dc);

  // This basically duplicates LLTuple::codegen and should eventually
  // be properly implemented in terms of it.
  registerTupleType(ty, this->ctorId.typeName + "." + this->ctorId.ctorName,
                    this->ctorId.smallId, pass->mod);
  bool yesUnboxed = true;
  LLAllocate a(ty, this->ctorId.smallId, yesUnboxed, NULL,
               LLAllocate::MEM_REGION_GLOBAL_HEAP);
  llvm::Value* obj_slot = a.codegen(pass);
  llvm::Value* obj = emitNonVolatileLoad(obj_slot, "obj");

  EDiag() << "LLAppCtor " << dt->getName() << " :: " << str(dt->getLLVMType());
  copyValuesToStruct(codegenAll(pass, this->args), obj);

  const llvm::Type* dtype = dt->getLLVMType();
  // TODO fix to use a stack slot properly
  return builder.CreateBitCast(obj, dtype);
}

void LLModule::codegenModule(CodegenPass* pass) {
  registerKnownDataTypes(datatype_decls, pass);

  // Ensure that the llvm::Function*s are created for all the function
  // prototypes, so that mutually recursive function references resolve.
  for (size_t i = 0; i < procs.size(); ++i) {
    // Ensure that the value is in the SymbolInfo entry in the symbol table.
    procs[i]->codegenProto(pass);
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegenProc(pass);
  }
}

////////////////////////////////////////////////////////////////////

void CodegenPass::scheduleBlockCodegen(LLBlock* b) {
  if (worklistBlocks.tryAdd(b->block_id, b)) {
    //EDiag() << "added new block " << b->block_id;
  }
}

void codegenBlocks(std::vector<LLBlock*> blocks, CodegenPass* pass,
                   llvm::Function* F) {
  pass->llvmBlocks.clear();
  pass->fosterBlocks.clear();
  pass->blockBindings.clear();

  // Create all the basic block before codegenning any of them.
  for (size_t i = 0; i < blocks.size(); ++i) {
    llvm::BasicBlock* bb = BasicBlock::Create(getGlobalContext(),
                                              blocks[i]->block_id, F);
    ASSERT(blocks[i]->block_id == bb->getName())
        << "function can't have two blocks named "
        << blocks[i]->block_id;
    pass->llvmBlocks[blocks[i]->block_id] = bb;
    pass->fosterBlocks[blocks[i]->block_id] = blocks[i];

    // Make sure we branch from the entry block to the first
    // 'computation' block.
    if (i == 0) {
      builder.CreateBr(bb);
    }
  }

  ASSERT(blocks.size() > 0) << F->getName() << " had no blocks!";

  pass->worklistBlocks.clear();
  pass->scheduleBlockCodegen(blocks[0]);
  while (!pass->worklistBlocks.empty()) {
    LLBlock* b = pass->worklistBlocks.get();
    b->codegenBlock(pass);
  }

  // Redundant pattern matches will produce empty basic blocks;
  // here, we clean up any basic blocks we created but never used.
  llvm::Function::iterator BB_it = F->begin();
  while (BB_it != F->end()) {
    llvm::BasicBlock* bb = BB_it; ++BB_it;
    if (bb->empty()) {
      if (bb->use_empty()) {
        bb->eraseFromParent();
      }
    }
  }
}

typedef std::map<std::vector<int>, TupleTypeAST*> CtorTypes;
struct BlockBindings {
  CaseContext* ctx;
  CtorTypes ctab;
  std::vector<DTBinding> binds;
  llvm::Value* scrutinee;
};

llvm::Value* lookupOccs(Occurrence* occ, llvm::Value* v, CtorTypes& ctab);
llvm::AllocaInst*
getStackSlotForOcc(Occurrence* occ, llvm::Value* v,
                   CaseContext* ctx, CodegenPass* pass);

void trySetName(llvm::Value* v, const string& name);

////////////////////////////////////////////////////////////////////

llvm::Value* emitFakeComment(std::string s) {
  EDiag() << "emitFakeComment: " << s;
  return new llvm::BitCastInst(builder.getInt32(0), builder.getInt32Ty(), s,
                               builder.GetInsertBlock());
}

void LLBlock::codegenBlock(CodegenPass* pass) {
  llvm::BasicBlock* bb = pass->lookupBlock(this->block_id);
  builder.SetInsertPoint(bb);

  BlockBindings* bindings = pass->blockBindings[this->block_id];
  //EDiag() << "codegenning block " << bb->getName() << "; binds? " << (bindings != NULL);
  if (bindings) {
    for (size_t i = 0; i < bindings->binds.size(); ++i) {
      DTBinding& bind = bindings->binds[i];
      CaseContext* ctx = bindings->ctx;

      //EDiag() << "looking up occs for " << bind.first; bb->getParent()->dump();
      Value* v = lookupOccs(bind.second, bindings->scrutinee, bindings->ctab);
      Value* v_slot = getStackSlotForOcc(bind.second, v, ctx, pass);
      trySetName(v_slot, "pat_" + bind.first + "_slot");
      EDiag() << "implicitly inserting " << bind.first << " = " << str(v_slot);
      pass->valueSymTab.insert(bind.first, v_slot);
    }
  }

  for (size_t i = 0; i < this->mids.size(); ++i) {
    this->mids[i]->codegenMiddle(pass);
  }
  //EDiag() << "codegening terminator for block " << bb->getName();
  this->terminator->codegenTerminator(pass);
}

void LLRebindId::codegenMiddle(CodegenPass* pass) {
  pass->valueSymTab.insert(from, to->codegen(pass));
}

////////////////////////////////////////////////////////////////////

void LLRetVoid::codegenTerminator(CodegenPass* pass) {
  //EDiag() << "ret void";
  builder.CreateRetVoid();
}

void LLRetVal::codegenTerminator(CodegenPass* pass) {
  llvm::Value* rv = pass->emit(this->val, NULL);
  //EDiag() << "ret " << str(rv) << " :: " << str(rv->getType());
  if (rv->getType()->isVoidTy()) {
    builder.CreateRetVoid();
  } else if (builder.getCurrentFunctionReturnType()->isVoidTy()) {
    builder.CreateRetVoid();
  } else {
    builder.CreateRet(rv);
  }
}

void LLBr::codegenTerminator(CodegenPass* pass) {
  //EDiag() << "br " << this->block_id;
  builder.CreateBr(pass->lookupBlock(this->block_id));
}

void LLCondBr::codegenTerminator(CodegenPass* pass) {
  //EDiag() << "condbar " << this->then_id;
  builder.CreateCondBr(pass->emit(this->var, NULL),
                       pass->lookupBlock(this->then_id),
                       pass->lookupBlock(this->else_id));
}

struct CaseContext {
  std::map<std::vector<int>, TupleTypeAST*>     ctab;
  std::map<std::vector<int>, llvm::AllocaInst*> ctorSlotMap;
};

void LLSwitch::codegenTerminator(CodegenPass* pass) {
  EDiag() << "switch " << this->scrutinee->tag;
  llvm::Value* v = pass->emit(this->scrutinee, NULL);
  CaseContext* ctx = new CaseContext;
  this->dt->codegenDecisionTree(pass, v, ctx);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

CodegenPass::CodegenPass(llvm::Module* m) : mod(m) {
  //dib = new DIBuilder(*mod);
}

llvm::Function* CodegenPass::lookupFunctionOrDie(const std::string&
                                                         fullyQualifiedSymbol) {
  // Otherwise, it should be a function name.
  llvm::Function* f = mod->getFunction(fullyQualifiedSymbol);

  if (!f) {
   llvm::errs() << "Unable to find function in module named: "
              << fullyQualifiedSymbol << "\n";
   valueSymTab.dump(llvm::errs());
   ASSERT(false) << "unable to find function " << fullyQualifiedSymbol;
  }
  return f;
}

////////////////////////////////////////////////////////////////////
//////////////// LLInt, LLBool, LLVar///////////////////////////////
////////////////////////////////////////////////////////////////////

llvm::Value* LLInt::codegen(CodegenPass* pass) {
  ASSERT(this->type && this->type->getLLVMType());
  const llvm::Type* ty = this->type->getLLVMType();

  llvm::Value* small = ConstantInt::get(ty, this->getAPInt());

  // Our type could be an LLVM type, or an arbitrary precision int type.
  if (ty->isIntegerTy()) {
    return small;
  } else if (false) {
    // MP integer constants that do not fit in 64 bits
    // must be initialized from string data.
    ASSERT(false) << "codegen for int values that don't fit"
                  << " in 64 bits not yet implemented";
    return NULL;
  } else {
    // Small integers may be initialized immediately.
    llvm::Value* mpint = pass->allocateMPInt();

    // Call mp_int_init_value() (ignore rv for now)
    llvm::Value* mp_init_value = pass->lookupFunctionOrDie("mp_int_init_value");
    builder.CreateCall2(mp_init_value, mpint, small);
    return mpint;
  }
}

llvm::Value* LLBool::codegen(CodegenPass* pass) {
  return builder.getInt1(this->boolValue);
}

llvm::Value* LLGlobalSymbol::codegen(CodegenPass* pass) {
  return pass->lookupFunctionOrDie(this->name);
}

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  // The variable for an environment can be looked up multiple times...
  llvm::Value* v = pass->valueSymTab.lookup(getName());
  if (v) return v;
  //return emitFakeComment("fake " + getName());

  pass->valueSymTab.dump(llvm::errs());
  ASSERT(false) << "Unknown variable name " << this->name << " in CodegenPass";
  return NULL;
}

/**
// Note: the logical signature of addition on multi-precision ints (Int)
// is (+Int) :: Int -> Int -> Int
// but the C-level signature for mp_int_add is
// mp_result mp_int_add(mp_int, mp_int, mp_int);

llvm::Value* emitRuntimeMPInt_Op(llvm::Value* VL, llvm::Value* VR,
                                 const char* mp_int_op_name) {
  // TODO If we have ASTs, we would be able to use the _value
  // variants for small constants.

  llvm::Value* result = allocateMPInt();
  builder.CreateCall(foster::module->getFunction("mp_int_init"), result);
  builder.CreateCall3(foster::module->getFunction(mp_int_op_name),
                      VL, VR, result);
  return result;
}

llvm::Value* emitRuntimeArbitraryPrecisionOperation(const std::string& op,
                                        llvm::Value* VL, llvm::Value* VR) {
       if (op == "+") { return emitRuntimeMPInt_Op(VL, VR, "mp_int_add"); }
  else if (op == "*") { return emitRuntimeMPInt_Op(VL, VR, "mp_int_mul"); }

  EDiag() << "\t emitRuntimeArbitraryPrecisionOperation() not yet implemented"
          << " for operation " << op << "!";
  exit(1);
  return NULL;
}
*/

////////////////////////////////////////////////////////////////////
//////////////// LLAlloc, LLDeref, LLStore /////////////////////////
////////////////////////////////////////////////////////////////////

Value* allocateCell(CodegenPass* pass, TypeAST* type, bool unboxed,
                    LLAllocate::MemRegion region, int8_t ctorId) {
  const llvm::Type* ty = type->getLLVMType();
  if (unboxed) {
    if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
      ty = pty->getContainedType(0);
    }
  }

  switch (region) {
  case LLAllocate::MEM_REGION_STACK:
    return CreateEntryAlloca(ty, "alloc");

  case LLAllocate::MEM_REGION_GLOBAL_HEAP:
    return pass->emitMalloc(ty, ctorId);

  default:
    ASSERT(false); return NULL;
  }
}

Value* allocateArray(CodegenPass* pass, TypeAST* ty,
                     LLAllocate::MemRegion region,
                     Value* arraySize) {
  const llvm::Type* elt_ty = getLLVMType(ty);
  ASSERT(region == LLAllocate::MEM_REGION_GLOBAL_HEAP);
  return pass->emitArrayMalloc(elt_ty, arraySize);
}

llvm::Value* LLAllocate::codegen(CodegenPass* pass) {
  if (this->arraySize != NULL) {
    EDiag() << "allocating array, type = " << str(this->type);
    return allocateArray(pass, this->type, this->region,
                         pass->emit(this->arraySize, NULL));
  } else {
    return allocateCell(pass, this->type, this->unboxed,
                        this->region, this->ctorId);
  }
}

llvm::Value* LLAlloc::codegen(CodegenPass* pass) {
  // (alloc base) is equivalent to
  //    let rs  = mallocType t;
  //        sv = base;
  //        r   = rs^;
  //     in sv >^ r;
  //        r
  //    end
  ASSERT(this && this->baseVar && this->baseVar->type);
  llvm::Value* ptrSlot   = pass->emitMalloc(this->baseVar->type->getLLVMType(),
                                            foster::bogusCtorId(-4));
  llvm::Value* storedVal = pass->emit(baseVar, NULL);
  llvm::Value* ptr       = emitNonVolatileLoad(ptrSlot, "alloc_slot_ptr");
  emitStore(storedVal, ptr);
  return ptrSlot;
}

llvm::Value* LLDeref::codegen(CodegenPass* pass) {
  // base could be an array a[i] or a slot for a reference variable r.
  // a[i] should codegen to &a[i], the address of the slot in the array.
  // r    should codegen to the contents of the slot (the ref pointer value),
  //        not the slot address.
  return builder.CreateLoad(pass->emit(base, NULL));
}

llvm::Value* LLStore::codegen(CodegenPass* pass) {
  llvm::Value* vv = pass->emit(v, NULL);
  llvm::Value* vr = pass->emit(r, NULL);
  return emitStore(vv, vr);
}

////////////////////////////////////////////////////////////////////
//////////////// LLLetVals /////////////////////////////////////////
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
    // We use codegen() instead of pass>emit()
    // because emit inserts implict loads, which we
    // want done as late as possible.
    Value* b = exprs[i]->codegen(pass);
    trySetName(b, (b->hasName()
                   && pystring::startswith(b->getName(), "stackref"))
                ? names[i] + "_slot"
                : names[i]);
    //EDiag() << "inserting " << names[i] << " = " << (exprs[i]->tag) << " -> " << str(b);
    pass->valueSymTab.insert(names[i], b);
  }
}

////////////////////////////////////////////////////////////////////
//////////////// LLClosures ////////////////////////////////////////
////////////////////////////////////////////////////////////////////

void LLClosures::codegenMiddle(CodegenPass* pass) {
  // This AST node binds a mutually-recursive set of functions,
  // represented as closure values.

  std::vector<llvm::Value*> envSlots;
  for (size_t i = 0; i < closures.size(); ++i) {
    envSlots.push_back(closures[i]->env->codegenStorage(pass));
  }

  // Allocate storage for the closures and populate 'em with code/env values.
  for (size_t i = 0; i < closures.size(); ++i) {
    llvm::Value* clo = closures[i]->codegenClosure(pass, envSlots[i]);
    pass->valueSymTab.insert(closures[i]->varname, clo);
  }

  // Stick each closure environment in the symbol table.
  std::vector<llvm::Value*> envPtrs;
  for (size_t i = 0; i < closures.size(); ++i) {
    // Make sure we close over generic versions of our pointers...
    llvm::Value* envPtr = pass->autoload(envSlots[i]);
    llvm::Value* genPtr = builder.CreateBitCast(envPtr,
                                builder.getInt8PtrTy(),
                                closures[i]->envname + ".generic");
    pass->valueSymTab.insert(closures[i]->envname, genPtr);

    envPtrs.push_back(envPtr);
  }

  // Now that all the env pointers are in scope,
  // store the appropriate values through each pointer.
  for (size_t i = 0; i < closures.size(); ++i) {
    closures[i]->env->codegenTo(pass, envPtrs[i]);
  }

  // And clean up env names.
  for (size_t i = 0; i < closures.size(); ++i) {
    pass->valueSymTab.remove(closures[i]->envname);
  }
}

bool tryBindClosureFunctionTypes(const llvm::Type*          origType,
                                 const llvm::FunctionType*& fnType,
                                 const llvm::StructType*  & cloStructTy) {
  fnType = NULL; cloStructTy = NULL;

  const llvm::PointerType* pfnty = llvm::dyn_cast<llvm::PointerType>(origType);
  if (!pfnty) {
    EDiag() << "expected " << str(origType) << " to be a ptr type.";
    return false;
  }
  fnType = llvm::dyn_cast<llvm::FunctionType>(pfnty->getContainedType(0));
  if (!fnType) {
    EDiag() << "expected " << str(origType) << " to be a ptr to fn type.";
    return false;
  }
  if (fnType->getNumParams() == 0) {
    EDiag() << "expected " << str(fnType) << " to have an env parameter.";
    return false;
  }
  const llvm::PointerType* maybeEnvType =
                llvm::dyn_cast<llvm::PointerType>(fnType->getParamType(0));
  if (!maybeEnvType) return false;

  cloStructTy = llvm::StructType::get(origType->getContext(),
                    pfnty, maybeEnvType, NULL);
  return true;
}

// Converts { r({...}*, ----), {....}* }
// to       { r( i8*,   ----),   i8*   }.
// Used when choosing a type to allocate for a closure pair.
const llvm::StructType*
genericClosureStructTy(const llvm::FunctionType* fnty) {
  const Type* retty = fnty->getReturnType();
  std::vector<const llvm::Type*> argTypes;
  for (size_t i = 0; i < fnty->getNumParams(); ++i) {
     argTypes.push_back(fnty->getParamType(i));
  }
  argTypes[0] = builder.getInt8PtrTy();

  return llvm::StructType::get(fnty->getContext(),
           ptrTo(llvm::FunctionType::get(retty, argTypes, false)),
           builder.getInt8PtrTy(), NULL);
}

bool isPointerToPointer(const llvm::Type* p) {
  return p->isPointerTy() && p->getContainedType(0)->isPointerTy();
}

llvm::Value* LLClosure::codegenClosure(
                        CodegenPass* pass,
                        llvm::Value* envPtrOrSlot) {
  llvm::Value* proc = pass->lookupFunctionOrDie(procname);

  const llvm::FunctionType* fnty;
  const llvm::StructType* cloStructTy;

  if (!tryBindClosureFunctionTypes(proc->getType(), fnty, cloStructTy)) {
    ASSERT(false) << "proc " << procname
                  << " with type " << str(proc->getType())
                  << " not closed??";
  }

  llvm::Value* clo = NULL; llvm::Value* rv = NULL;
  bool closureEscapes = true;
  if (closureEscapes) {
    // // { code*, env* }**
    llvm::AllocaInst* clo_slot = pass->emitMalloc(genericClosureStructTy(fnty),
                                                  foster::bogusCtorId(-5));
    clo = emitNonVolatileLoad(clo_slot, varname + ".closure"); rv = clo_slot;
  } else { // { code*, env* }*
    clo = CreateEntryAlloca(cloStructTy, varname + ".closure"); rv = clo;
  }

  // TODO register closure type

  emitStoreWithCast(proc,
                  builder.CreateConstGEP2_32(clo, 0, 0, varname + ".clo_code"));
  Value* env_slot = builder.CreateConstGEP2_32(clo, 0, 1, varname + ".clo_env");
  if (env->vars.empty()) {
    storeNullPointerToSlot(env_slot);
  } else {
    // Only store the env in the closure if the env contains entries.
    llvm::Value* envPtr = pass->autoload(envPtrOrSlot);
    emitStoreWithCast(envPtr, env_slot);
  }

  return rv;
}

////////////////////////////////////////////////////////////////////
//////////////// LLProc ////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

const llvm::FunctionType*
getLLVMFunctionType(FnTypeAST* t, const std::string& procSymbol) {
  if (const llvm::PointerType* pt =
   dyn_cast<llvm::PointerType>(getLLVMType(t))) {
    ASSERT(! getLLVMType(t->getReturnType())->isOpaqueTy())
        << "Cannot use opaque return type for proc " << procSymbol;
    return dyn_cast<llvm::FunctionType>(pt->getContainedType(0));
  } else {
    return NULL;
  }
}

void setFunctionArgumentNames(llvm::Function* F,
              const std::vector<std::string>& argnames) {
  ASSERT(argnames.size() == F->arg_size())
            << "error when codegenning proto " << F->getName()
            << "\n of type " << str(F->getType())
            << "; inArgs.size: " << argnames.size() <<
               "; F.arg_size: " << F->arg_size() << "\n" << str(F);

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

llvm::Value* LLProc::codegenProto(CodegenPass* pass) {
  std::string symbolName = getGlobalSymbolName(this->name);

  this->type->markAsProc();
  const llvm::FunctionType* FT = getLLVMFunctionType(this->type, symbolName);

  if (symbolName == kFosterMain) {
    // No args, returning void...
    FT = llvm::FunctionType::get(builder.getVoidTy(), false);
    this->functionLinkage = llvm::GlobalValue::ExternalLinkage;
  }

  ASSERT(FT) << "expecting top-level proc to have FunctionType!";

  this->F = Function::Create(FT, this->functionLinkage, symbolName, pass->mod);

  ASSERT(F) << "function creation failed for proto " << this->name;
  ASSERT(F->getName() == symbolName) << "redefinition of function " << symbolName;

  setFunctionArgumentNames(F, this->argnames);

  if (FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(this->type)) {
    F->setCallingConv(fnty->getCallingConventionID());
  }

  return F;
}

bool functionMightAllocateMemory(LLProc* proc) {
  return true; // conservative approximation to MightAlloc
}

llvm::AllocaInst* ensureImplicitStackSlot(llvm::Value* v, CodegenPass* pass) {
  if (llvm::LoadInst* load = dyn_cast<llvm::LoadInst>(v)) {
    llvm::AllocaInst* slot = dyn_cast<llvm::AllocaInst>(load->getOperand(0));
    if (slot && pass->needsImplicitLoad.count(slot) == 1) {
      return slot;
    }
  }

  if (mightContainHeapPointers(v->getType())) {
    return pass->storeAndMarkPointerAsGCRoot(v);
  } else {
    llvm::AllocaInst* slot = stackSlotWithValue(v, v->getNameStr() + "_addr");
    pass->markAsNeedingImplicitLoads(slot);
    return slot;
  }
}

llvm::Value* LLProc::codegenProc(CodegenPass* pass) {
  ASSERT(this->F != NULL) << "LLModule should codegen proto for " << getName();
  ASSERT(F->arg_size() == this->argnames.size());

  F->setGC("fostergc");

  BasicBlock* prevBB = builder.GetInsertBlock();
  pass->addEntryBB(F);

  CodegenPass::ValueScope* scope = pass->valueSymTab.newScope(this->getName());

  // If the body of the function might allocate memory, the first thing
  // the function should do is create stack slots/GC roots to hold
  // dynamically-allocated pointer parameters.
  if (functionMightAllocateMemory(this)) {
    Function::arg_iterator AI = F->arg_begin();
    for ( ; AI != F->arg_end(); ++AI) {
      llvm::Value* slot = ensureImplicitStackSlot(AI, pass);
      scope->insert(AI->getNameStr(), slot);
    }
  }

  EDiag() << "codegennign blocks for fn " << F->getName();

  codegenBlocks(this->blocks, pass, F);

  pass->valueSymTab.popExistingScope(scope);

  // Restore the insertion point, if there was one.
  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return F;
}

////////////////////////////////////////////////////////////////////

llvm::Value* LLCoroPrim::codegen(CodegenPass* pass) {
  const llvm::Type* r = retType->getLLVMType();
  const llvm::Type* a = typeArg->getLLVMType();
  if (this->primName == "coro_yield") { return pass->emitCoroYieldFn(r, a); }
  if (this->primName == "coro_invoke") { return pass->emitCoroInvokeFn(r, a); }
  if (this->primName == "coro_create") { return pass->emitCoroCreateFn(r, a); }
  ASSERT(false) << "unknown coro prim: " << this->primName;
  return NULL;
}

////////////////////////////////////////////////////////////////////

// Create at most one stack slot per subterm.
llvm::AllocaInst*
getStackSlotForOcc(Occurrence* occ, llvm::Value* v,
                   CaseContext* ctx, CodegenPass* pass) {
  llvm::AllocaInst* slot = ctx->ctorSlotMap[occ->offsets];
  if (slot) {
    emitStore(v, slot);
  } else {
    slot = ensureImplicitStackSlot(v, pass);
    ctx->ctorSlotMap[occ->offsets] = slot;
  }
  return slot;
}

llvm::Value* lookupOccs(Occurrence* occ, llvm::Value* v, CtorTypes& ctab) {
  ASSERT(occ != NULL);
  const std::vector<int>& occs = occ->offsets;
  llvm::Value* rv = v;

  std::vector<int> currentOccs;

  // If we know that the subterm at this position was created with
  // a particular data constructor, emit a cast to that ctor's type.
  if (TupleTypeAST* tupty = ctab[currentOccs]) {
    rv = builder.CreateBitCast(rv, tupty->getLLVMType());
  }

  for (size_t i = 0; i < occs.size(); ++i) {
    llvm::Constant* idx = getConstantInt32For(occs[i]);
    rv = getElementFromComposite(rv, idx, "switch_insp");

    currentOccs.push_back(occs[i]);
    if (TupleTypeAST* tupty = ctab[currentOccs]) {
      rv = builder.CreateBitCast(rv, tupty->getLLVMType());
    }
  }

  return rv;
}

void DecisionTree::codegenDecisionTree(CodegenPass* pass,
                                       llvm::Value* scrutinee,
                                       CaseContext* ctx) {
  llvm::BasicBlock* bb = NULL;
  switch (tag) {
  case DecisionTree::DT_FAIL:
    EDiag() << "DecisionTree codegen, tag = DT_FAIL; v = " << str(scrutinee);
    emitFosterAssert(pass->mod, builder.getInt1(false), "pattern match failure!");
    break;

  case DecisionTree::DT_LEAF:
    //EDiag() << "codegenning dt leaf for block " << this->action_block_id
    //    << "; bindings already set? " << (pass->blockBindings[this->action_block_id] != NULL);
    if (!pass->blockBindings[this->action_block_id]) {
      BlockBindings* bindings = new BlockBindings;
      bindings->ctx       = ctx;
      bindings->ctab      = ctx->ctab;
      bindings->binds     = binds;
      bindings->scrutinee = scrutinee;
      pass->blockBindings[this->action_block_id] = bindings;
    }

    // Make sure that we eventually codegen in the leaf block.
    bb = pass->lookupBlock(action_block_id);
    builder.CreateBr(bb);
    break;

  case DecisionTree::DT_SWAP:
    ASSERT(false) << "Should not have DT_SWAP nodes at codegen!";
  // end DT_SWAP

  case DecisionTree::DT_SWITCH:
    sc->codegenSwitch(pass, scrutinee, ctx);
    break;
  }
}

llvm::Value* emitCallGetCtorIdOf(CodegenPass* pass, llvm::Value* v) {
  llvm::Value* foster_ctor_id_of = pass->mod->getFunction("foster_ctor_id_of");
  ASSERT(foster_ctor_id_of != NULL);
  llvm::CallInst* call = builder.CreateCall(foster_ctor_id_of,
                         builder.CreateBitCast(v, builder.getInt8PtrTy()));
  markAsNonAllocating(call);
  return call;
}

void addAndEmitTo(Function* f, BasicBlock* bb) {
  f->getBasicBlockList().push_back(bb);
  builder.SetInsertPoint(bb);
}

void SwitchCase::codegenSwitch(CodegenPass* pass,
                               llvm::Value* scrutinee,
                               CaseContext* ctx) {
  ASSERT(ctors.size() == trees.size());
  ASSERT(ctors.size() >= 1);

  BasicBlock* defaultBB = NULL;
  if (defaultCase != NULL) {
    defaultBB = BasicBlock::Create(getGlobalContext(), "case_default");
  }

  // All the ctors should have the same data type, now that we have at least
  // one ctor, check if it's associated with a data type we know of.
  DataTypeAST* dt = pass->isKnownDataType[ctors[0].typeName];

  // Special-case codegen for when there's only one
  // possible case, to avoid superfluous branches.
  if (trees.size() == 1 && !defaultCase) {
    if (dt) {
      TupleTypeAST* tupty = getDataCtorType(
                            dt->getCtor(ctors[0].smallId));
      ctx->ctab[this->occ->offsets] = tupty;
    }
    trees[0]->codegenDecisionTree(pass, scrutinee, ctx);
    return;
  }

  // TODO: switching on a.p. integers: possible at all?
  // If so, it will require manual if-else chaining,
  // not a simple int32 switch...
  BasicBlock* bbNoDefault = defaultBB ? NULL      :
                       BasicBlock::Create(getGlobalContext(), "case_nodefault");
  BasicBlock* defOrContBB = defaultBB ? defaultBB : bbNoDefault;

  // Fetch the subterm of the scrutinee being inspected.
  llvm::Value* inspected = lookupOccs(this->occ, scrutinee, ctx->ctab);

  // If we're looking at a data type, emit code to get the ctor tag,
  // instead of switching on the pointer value directly.
  if (dt) {    inspected = emitCallGetCtorIdOf(pass, inspected);  }

  // Switch on the inspected value; we'll fill in the ctor branches as we go.
  llvm::SwitchInst* si = builder.CreateSwitch(inspected, defOrContBB, ctors.size());
  Function *F = builder.GetInsertBlock()->getParent();

  for (size_t i = 0; i < ctors.size(); ++i) {
    CtorId c = ctors[i];
    ConstantInt* onVal = NULL;
    TupleTypeAST* tupty = NULL;

    // Compute the "tag" associated with this branch.
    // Also, if needed, we shall bitcast the scrutinee (for data types)
    // from an unknown to a specific ctor-associated type in order to perform
    // further case discrimination.
    if (dt) {
      tupty = getDataCtorType(dt->getCtor(c.smallId));
      ctx->ctab[this->occ->offsets] = tupty;
      onVal = getConstantInt8For(c.smallId);
    } else if (c.typeName == "Bool") {
      onVal = builder.getInt1(c.smallId);
    } else if (c.typeName == "Int32") {
      onVal = getConstantInt32For(c.smallId);
    } else {
      ASSERT(false) << "SwitchCase ctor " << (i+1) << "/" << ctors.size()
             << ": " << c.typeName << "." << c.ctorName << "#" << c.smallId
             << "\n" << str(scrutinee)  << "::" << str(scrutinee->getType());
    }

    // Emit the code for the branch expression,
    // ending with a branch to the end of the case-expr.
    std::stringstream ss; ss << "casetest_" << i;
    BasicBlock* destBB = BasicBlock::Create(getGlobalContext(), ss.str());
    addAndEmitTo(F, destBB);
    trees[i]->codegenDecisionTree(pass, scrutinee, ctx);

    ASSERT(inspected->getType() == onVal->getType())
        << "switch case and inspected value had different types!";
    si->addCase(onVal, destBB);
    //if (tupty) { ctx->ctab.erase(this->occ->offsets); }
  }

  if (defaultCase) {
    addAndEmitTo(F, defaultBB);
    defaultCase->codegenDecisionTree(pass, scrutinee, ctx);
  }

  if (bbNoDefault) {
    addAndEmitTo(F, bbNoDefault);
    emitFosterAssert(pass->mod, llvm::ConstantInt::getTrue(builder.getContext()),
                   "control passed to llvm-generated default block -- bad!");
    builder.CreateUnreachable();
  }
}

////////////////////////////////////////////////////////////////////

bool isPointerToStruct(const llvm::Type* ty) {
  if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    if (llvm::dyn_cast<llvm::StructType>(pty->getContainedType(0))) {
      return true;
    }
  }
  return false;
}

bool tryBindArray(llvm::Value* base, Value*& arr, Value*& len) {
  // {i64, [0 x T]}*
  if (isPointerToStruct(base->getType())) {
    const llvm::Type* sty = slotType(base);
    if (sty->getNumContainedTypes() == 2
      && sty->getContainedType(0) == builder.getInt64Ty()) {
      if (const llvm::ArrayType* aty =
        llvm::dyn_cast<llvm::ArrayType>(sty->getContainedType(1))) {
        if (aty->getNumElements() == 0) {
          arr = getPointerToIndex(base, getConstantInt32For(1), "arr");
          len = getElementFromComposite(base, getConstantInt32For(0), "len");
          return true;
        }
      }
    }
  }
  return false;
}

Value* getArraySlot(Value* base, Value* idx, CodegenPass* pass) {
  Value* arr = NULL; Value* len;
  if (tryBindArray(base, arr, len)) {
    // TODO emit code to validate idx value is in range.
    emitFosterAssert(pass->mod,
      builder.CreateICmpSLT(
                builder.CreateSExt(idx, len->getType()),
                len, "boundscheck"),
      "array index out of bounds!");
    return getPointerToIndex(arr, idx, "arr_slot");
  } else {
    ASSERT(false) << "expected array, got " << str(base);
    return NULL;
  }
}

llvm::Value* LLArrayRead::codegen(CodegenPass* pass) {
  Value* base = pass->emit(this->base , NULL);
  Value* idx  = pass->emit(this->index, NULL);
  Value* slot = getArraySlot(base, idx, pass);
  Value* val  = builder.CreateLoad(slot);
  return ensureImplicitStackSlot(val, pass);
}

llvm::Value* LLArrayPoke::codegen(CodegenPass* pass) {
  Value* val  = pass->emit(this->value, NULL);
  Value* base = pass->emit(this->base , NULL);
  Value* idx  = pass->emit(this->index, NULL);
  Value* slot = getArraySlot(base, idx, pass);
  return builder.CreateStore(val, slot, /*isVolatile=*/ false);
}

////////////////////////////////////////////////////////////////////

llvm::Value* LLCallPrimOp::codegen(CodegenPass* pass) {
  return codegenPrimitiveOperation(this->op, builder, codegenAll(pass, this->args));
}

bool isGenericClosureEnvType(const Type* ty) {
  return ty == builder.getInt8PtrTy();
}

// Returns null if no bitcast is needed, else returns the type to bitcast to.
bool isPointerToUnknown(const Type* ty) {
  if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    return pty->getContainedType(0)->isIntegerTy(kUnknownBitsize);
  }
  return false;
}

bool matchesExceptForUnknownPointers(const Type* aty, const Type* ety) {
  if (aty == ety) return true;
  if (aty->isPointerTy()) {
    if (isPointerToUnknown(ety)) { return true; }
    return matchesExceptForUnknownPointers(aty->getContainedType(0),
                                           ety->getContainedType(0));
  }
  if (aty->getTypeID() != ety->getTypeID()) return false;
  if (aty->getNumContainedTypes() != ety->getNumContainedTypes()) return false;
  for (size_t i = 0; i < aty->getNumContainedTypes(); ++i) {
    if (! matchesExceptForUnknownPointers(aty->getContainedType(i),
                                          ety->getContainedType(i))) return false;
  }
  return true;
}

llvm::Value* LLCall::codegen(CodegenPass* pass) {
  ASSERT(base != NULL) << "unable to codegen call due to null base";

  Value* FV = pass->emit(base, NULL);
  ASSERT(FV) << "unable to codegen call due to missing value for base";

  const llvm::FunctionType* FT = NULL;
  std::vector<Value*> valArgs;

  // TODO extract directly from FnTypeAST
  llvm::CallingConv::ID callingConv = llvm::CallingConv::GHC; // conspicuous
  bool haveSetCallingConv = false;

  if (Function* F = llvm::dyn_cast<Function>(FV)) {
    // Call to top level function
    FT = F->getFunctionType();
    callingConv = F->getCallingConv(); haveSetCallingConv = true;
  } else if (FnTypeAST* fnType = dynamic_cast<FnTypeAST*>(base->type)) {
    callingConv = fnType->getCallingConventionID(); haveSetCallingConv = true;
    if (fnType->isMarkedAsClosure()) {
      // Load code and env pointers from closure...
      llvm::Value* envPtr =
           getElementFromComposite(FV, getConstantInt32For(1), "getCloEnv");
      FV = getElementFromComposite(FV, getConstantInt32For(0), "getCloCode");

      FT = dyn_cast<const llvm::FunctionType>(FV->getType()->getContainedType(0));
      // Pass env pointer as first parameter to function.
      ASSERT(valArgs.empty());
      valArgs.push_back(envPtr);
    } else {
      FT = fnType->getLLVMFnType();
    }
  } else {
    ASSERT(false) << "expected either direct llvm::Function value or else "
                  << "something of FnType; had " << (base->tag)
                  << " of type " << str(base->type);
  }

  ASSERT(haveSetCallingConv);
  ASSERT(FT) << "call to uncallable something "
             << base->tag << "\t" << base->type->tag
             << "\nFV: " << str(FV);

  // Collect the args, performing coercions if necessary.
  for (size_t i = 0; i < this->args.size(); ++i) {
    const llvm::Type* expectedType = FT->getParamType(valArgs.size());

    llvm::Value* argV = pass->emit(this->args[i], NULL);

    // This is a an artifact produced by the mutual recursion
    // of the environments of mutually recursive closures.
    if (isGenericClosureEnvType(argV->getType())
      && argV->getType() != expectedType) {
      EDiag() << "emitting bitcast gen2spec " << str(expectedType);
      argV = builder.CreateBitCast(argV, expectedType, "gen2spec");
    }

    if ((argV->getType() != expectedType)
        && matchesExceptForUnknownPointers(argV->getType(), expectedType)) {
      argV = builder.CreateBitCast(argV, expectedType, "spec2gen");
    }

    valArgs.push_back(argV);

    ASSERT(argV->getType() == expectedType)
              << "type mismatch, " << str(argV->getType())
              << " vs expected type " << str(expectedType)
              << "\nbase is " << str(FV)
              << "\nwith base type " << str(FV->getType())
              << "\nargV = " << str(argV);
  }

  ASSERT(FT->getNumParams() == valArgs.size())
            << "function arity mismatch for " << FV->getName()
            << "; got " << valArgs.size()
            << " args but expected " << FT->getNumParams();

  // Give the instruction a name, if we can...

  llvm::CallInst* callInst =
        builder.CreateCall(FV, valArgs.begin(), valArgs.end());
  callInst->setCallingConv(callingConv);
  trySetName(callInst, "calltmp");

  if (callingConv == llvm::CallingConv::Fast) {
    // In order to mark this call as a tail call, we must know that
    // none of the args being passed are pointers into this stack frame.
    // Because we don't do this analysis, we don't enable TCO for now.
    //callInst->setTailCall(true);
  }

  if (!this->callMightTriggerGC) {
    markAsNonAllocating(callInst);
  }

  // If we have e.g. a function like   mk-tree :: .... -> ref node
  // that returns a pointer, we assume that the pointer refers to
  // heap-allocated memory and must be stored on the stack and marked
  // as a GC root. In order that updates from the GC take effect,
  // we use the stack slot (of type T**) instead of the pointer (T*) itself
  // as the return value of the call.
  if ( callingConv == llvm::CallingConv::Fast
    && callInst->getType()->isPointerTy()) {
    // As a sanity check, we shouldn't ever get a pointer-to-pointer,
    // at least not from Foster code...
    ASSERT(!slotType(callInst)->isPointerTy());

    return pass->storeAndMarkPointerAsGCRoot(callInst);
  } else {
    return callInst;
  }
}

llvm::Value* LLTuple::codegenStorage(CodegenPass* pass) {
  if (vars.empty()) { return getUnitValue(); }

  ASSERT(this->allocator);
  TupleTypeAST* tuplety = dynamic_cast<TupleTypeAST*>(this->allocator->type);

  ASSERT(tuplety != NULL)
        << "allocator wants to emit type " << str(this->allocator->type)
        << "; var 0 :: " << str(vars[0]->type);

  registerTupleType(tuplety, this->typeName, foster::bogusCtorId(-2), pass->mod);

  return allocator->codegen(pass);
}

llvm::Value* LLTuple::codegen(CodegenPass* pass) {
  if (vars.empty()) { return getUnitValue(); }

  llvm::Value* slot = codegenStorage(pass);

  // Heap-allocated things codegen to a stack slot, which
  // is the Value we want the overall tuple to codegen as, but
  // we need temporary access to the pointer stored in the slot.
  // Otherwise, bad things happen.
  llvm::Value* pt = allocator->isStackAllocated()
           ? slot
           : emitNonVolatileLoad(slot, "normalize");
  codegenTo(pass, pt);
  return slot;
}

void LLTuple::codegenTo(CodegenPass* pass, llvm::Value* tup_ptr) {
  copyValuesToStruct(codegenAll(pass, this->vars), tup_ptr);
}

