// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterLL.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"
#include "parse/ParsingContext.h"

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
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::getGlobalContext;
using llvm::Value;
using llvm::ConstantInt;
using llvm::ConstantExpr;
using llvm::APInt;
using llvm::PHINode;
using llvm::dyn_cast;

using foster::builder;
using foster::currentOuts;
using foster::currentErrs;
using foster::SourceRange;
using foster::ParsingContext;
using foster::EDiag;
using foster::show;

char kFosterMain[] = "foster__main";

namespace foster {

void codegenLL(LLModule* package, llvm::Module* mod) {
  CodegenPass cp(mod);
  package->codegenModule(&cp);
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

} // namespace foster

const llvm::Type* getLLVMType(TypeAST* type) {
  ASSERT(type) << "getLLVMType must be given a non-null type!";
  return type->getLLVMType();
}

LLTuple* getEmptyTuple() {
  std::vector<LLVar*> vars;
  return new LLTuple(vars, NULL);
}

const llvm::Type* slotType(llvm::Value* v) {
  return v->getType()->getContainedType(0);
}

llvm::Value* emitStore(llvm::Value* val,
                       llvm::Value* ptr) {
  if (val->getType()->isVoidTy()) {
    // Can't store a void!
    return getUnitValue();
  }

  if (!isPointerToType(ptr->getType(), val->getType())) {
    ASSERT(false) << "ELIDING STORE DUE TO MISMATCHED TYPES:\n"
            << "ptr type: " << str(ptr->getType()) << "\n"
            << "val type: " << str(val->getType()) << "\n"
            << "val is  : " << str(val) << "\n"
            << "ptr is  : " << str(ptr);
    EDiag() << "unit is: " << str(getUnitValue());
    return builder.CreateBitCast(builder.getInt32(0),
                                 builder.getInt32Ty(),
                                 "elided store");
  } else {
    return builder.CreateStore(val, ptr, /*isVolatile=*/ false);
  }
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
    return builder.CreateLoad(v, /*isVolatile=*/ false,
                              v->getName() + ".autoload");
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
    if (!typesEqual(v->getType(), ty)) {
      ASSERT(false) << "********* expected type " << str(ty)
                           << "; had type " << str(v->getType())
                           << "\n for value " << str(v);
    }
  }
  ASSERT(v != NULL);
  return v;
}

////////////////////////////////////////////////////////////////////

void LLModule::codegenModule(CodegenPass* pass) {
  // Ensure that the llvm::Function*s are created for all the function
  // prototypes, so that mutually recursive function references resolve.
  for (size_t i = 0; i < procs.size(); ++i) {
    LLProc* f = procs[i];
    // Ensure that the value is in the SymbolInfo entry in the symbol table.
    f->codegenProto(pass);
    //pass->valueSymTab.insert(f->getName(), );
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegenProc(pass);
  }
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

CodegenPass::CodegenPass(llvm::Module* m) : mod(m) {
  //dib = new DIBuilder(*mod);
}

llvm::Function* CodegenPass::lookupFunctionOrDie(const std::string& fullyQualifiedSymbol) {
  // Otherwise, it should be a function name.
  llvm::Function* f = mod->getFunction(fullyQualifiedSymbol);

  if (!f) {
   currentErrs() << "Unable to find function in module named: "
              << fullyQualifiedSymbol << "\n";
   valueSymTab.dump(currentErrs());
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
    llvm::Value* mp_int_init_value = pass->mod->getFunction("mp_int_init_value");
    ASSERT(mp_int_init_value);

    builder.CreateCall2(mp_int_init_value, mpint, small);
    return mpint;
  }
}

llvm::Value* LLBool::codegen(CodegenPass* pass) {
  return builder.getInt1(this->boolValue);
}

llvm::Value* LLProcRef::codegen(CodegenPass* pass) {
  return pass->lookupFunctionOrDie(this->name);
}

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  // The variable for an environment can be looked up multiple times...
  llvm::Value* v = pass->valueSymTab.lookup(getName());
  if (v) return v;

  pass->valueSymTab.dump(currentOuts());
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

Value* allocateCell(CodegenPass* pass, TypeAST* type,
                    LLAllocate::MemRegion region) {
  const llvm::Type* ty = NULL;
  if (TupleTypeAST* tuplety = dynamic_cast<TupleTypeAST*>(type)) {
    ty = tuplety->getLLVMTypeUnboxed();
  } else {
    ty = type->getLLVMType();
  }

  switch (region) {
  case LLAllocate::MEM_REGION_STACK:
    EDiag() << "allocating cell on stack of type " << str(ty);
    return CreateEntryAlloca(ty, "alloc");

  case LLAllocate::MEM_REGION_GLOBAL_HEAP:
    return pass->emitMalloc(ty);

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
    return allocateCell(pass, this->type, this->region);
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
  llvm::Value* ptrSlot   = pass->emitMalloc(this->baseVar->type->getLLVMType());
  llvm::Value* storedVal = pass->emit(baseVar, NULL);
  llvm::Value* ptr       = builder.CreateLoad(ptrSlot, /*isVolatile=*/ false, "alloc_slot_ptr");
  emitStore(storedVal, ptr);
  return ptrSlot;
}

llvm::Value* LLDeref::codegen(CodegenPass* pass) {
  // base could be an array a[i] or a slot for a reference variable r.
  // a[i] should codegen to &a[i], the address of the slot in the array.
  // r    should codegen to the contents of the slot (the ref pointer value),
  //        not the slot address.
  return builder.CreateLoad(pass->emit(base, NULL),
                            /*isVolatile=*/ false,
                            "");
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
  } else {
    v->setName(name);
  }
}

llvm::Value* LLLetVals::codegen(CodegenPass* pass) {
  for (size_t i = 0; i < exprs.size(); ++i) {
    // We use codegen() instead of pass>emit()
    // because emit inserts implict loads, which we
    // want done as late as possible.
    Value* b = exprs[i]->codegen(pass);
    trySetName(b, (b->hasName()
                   && pystring::startswith(b->getName(), "stackref"))
                ? names[i] + "_slot"
                : names[i]);
    pass->valueSymTab.insert(names[i], b);
  }

  Value* rv = pass->emit(inexpr, NULL);

  for (size_t i = 0; i < exprs.size(); ++i) {
    pass->valueSymTab.remove(names[i]);
  }

  return rv;
}

////////////////////////////////////////////////////////////////////
//////////////// LLClosures ////////////////////////////////////////
////////////////////////////////////////////////////////////////////

llvm::Value* LLClosures::codegen(CodegenPass* pass) {
  // This AST node binds a mutually-recursive set of functions,
  // represented as closure values, in a designated expression.

  std::vector<llvm::Value*> envSlots;
  for (size_t i = 0; i < closures.size(); ++i) {
    envSlots.push_back(closures[i]->codegenStorage(pass));
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

  // And clean up.
  for (size_t i = 0; i < closures.size(); ++i) {
    pass->valueSymTab.remove(closures[i]->envname);
  }

  ////////////////////////////////////////////////////////
  ////////////////////////////////////////////////////////

  // Generate each closure, sticking it in the symbol table
  // so that the body of the LetClosures node has access.
  for (size_t i = 0; i < closures.size(); ++i) {
    llvm::Value* clo = closures[i]->codegenClosure(pass, envSlots[i]);
    pass->valueSymTab.insert(closures[i]->varname, clo);
  }

  llvm::Value* exp = pass->emit(expr, NULL);

  for (size_t i = 0; i < closures.size(); ++i) {
     pass->valueSymTab.remove(closures[i]->varname);
  }

  return exp;
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
const llvm::StructType*
genericClosureStructTy(const llvm::FunctionType* fnty) {
  const Type* retty = fnty->getReturnType();
  std::vector<const llvm::Type*> argTypes;
  for (size_t i = 0; i < fnty->getNumParams(); ++i) {
     argTypes.push_back(fnty->getParamType(i));
  }
  argTypes[0] = builder.getInt8PtrTy();

  return llvm::StructType::get(fnty->getContext(),
           ptrTo(FunctionType::get(retty, argTypes, false)),
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
    llvm::AllocaInst* clo_slot = pass->emitMalloc(genericClosureStructTy(fnty));
    clo = builder.CreateLoad(clo_slot, /*isVolatile=*/ false,
                                         varname + ".closure"); rv = clo_slot;
  } else { // { code*, env* }*
    clo = CreateEntryAlloca(cloStructTy, varname + ".closure"); rv = clo;
  }

  // TODO register closure type

  Value* clo_code_slot = builder.CreateConstGEP2_32(clo, 0, 0, varname + ".clo_code");
  emitStoreWithCast(proc, clo_code_slot);

  Value* clo_env_slot = builder.CreateConstGEP2_32(clo, 0, 1, varname + ".clo_env");
  if (env->vars.empty()) {
    storeNullPointerToSlot(clo_env_slot);
  } else {
    // Only store the env in the closure if the env contains entries.
    llvm::Value* envPtr = pass->autoload(envPtrOrSlot);
    emitStoreWithCast(envPtr, clo_env_slot);
  }

  //const llvm::StructType* genStructTy = genericClosureStructTy(fnty);
  //return builder.CreateBitCast(clo, ptrTo(genStructTy), varname + ".hideCloTy");
  return rv;
}

llvm::Value* LLClosure::codegenStorage(CodegenPass* pass) {
  return env->codegenStorage(pass);
}

////////////////////////////////////////////////////////////////////
//////////////// LLProc ////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

const llvm::FunctionType*
getLLVMFunctionType(FnTypeAST* t) {
  if (const llvm::PointerType* pt =
   dyn_cast<llvm::PointerType>(getLLVMType(t))) {
    return dyn_cast<FunctionType>(pt->getContainedType(0));
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

llvm::Value* LLProc::codegenProto(CodegenPass* pass) {
  std::string symbolName = foster::getGlobalSymbolName(this->name);

  this->type->markAsProc();
  const llvm::FunctionType* FT = getLLVMFunctionType(this->type);

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
  if (llvm::LoadInst* load = llvm::dyn_cast<llvm::LoadInst>(v)) {
    llvm::AllocaInst* slot = llvm::dyn_cast<llvm::AllocaInst>(load->getOperand(0));
    if (slot && pass->needsImplicitLoad.count(slot) == 1) {
      return slot;
    }
  }

  if (mightContainHeapPointers(v->getType())) {
    return pass->storeAndMarkPointerAsGCRootUnknownCtor(v);
  } else {
    llvm::AllocaInst* slot = stackSlotWithValue(v, v->getNameStr() + "_addr");
    pass->markAsNeedingImplicitLoads(slot);
    return slot;
  }
}

llvm::Value* LLProc::codegenProc(CodegenPass* pass) {
  ASSERT(this->getBody() != NULL);
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

  // Enforce that the main function always returns void.
  if (F->getName() == kFosterMain) {
    std::vector<std::string> names; names.push_back("!ignored");
    std::vector<LLExpr*>     exprs; exprs.push_back(this->body);
    this->body = new LLLetVals(names, exprs, getEmptyTuple());
  }

  Value* rv = pass->emit(getBody(), NULL);
  pass->valueSymTab.popExistingScope(scope);

  const FunctionType* ft = dyn_cast<FunctionType>(F->getType()->getContainedType(0));

  if (isVoidOrUnit(ft->getReturnType())) {
    builder.CreateRetVoid();
  } else {
    builder.CreateRet(rv);
    ASSERT(rv->getType() == ft->getReturnType())
        << "unable to return type " << str(ft->getReturnType()) << " from "
        << getName() << " given:\n" << str(rv);

  }
  //llvm::verifyFunction(*F);

  // Restore the insertion point, if there was one.
  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return F;
}

////////////////////////////////////////////////////////////////////

void addAndEmitTo(Function* f, BasicBlock* bb) {
  f->getBasicBlockList().push_back(bb);
  builder.SetInsertPoint(bb);
}

llvm::Value* LLIf::codegen(CodegenPass* pass) {
  //EDiag() << "Codegen for LLIfs should (eventually) be subsumed by CFG building!";
  Value* cond = pass->emit(getTestExpr(), NULL);

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then");
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);

  Value* iftmp = CreateEntryAlloca(getLLVMType(this->type), "iftmp_slot");
  pass->markAsNeedingImplicitLoads(iftmp);

  Function *F = builder.GetInsertBlock()->getParent();
  {
    addAndEmitTo(F, thenBB);
    emitStore(pass->emit(getThenExpr(), this->type), iftmp);
    builder.CreateBr(mergeBB);
  }

  {
    addAndEmitTo(F, elseBB);
    emitStore(pass->emit(getElseExpr(), this->type), iftmp);
    builder.CreateBr(mergeBB);
  }

  addAndEmitTo(F, mergeBB);
  return iftmp;
}

////////////////////////////////////////////////////////////////////

llvm::Value* LLUntil::codegen(CodegenPass* pass) {
  //EDiag() << "Codegen for LLUntils should (eventually) be subsumed by CFG building!";

  BasicBlock* testBB = BasicBlock::Create(getGlobalContext(), "until_test");
  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "until_body");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "until_cont");
  Function *F = builder.GetInsertBlock()->getParent();

  builder.CreateBr(testBB);

  addAndEmitTo(F, testBB);
  Value* cond = pass->emit(getTestExpr(), NULL);
  builder.CreateCondBr(cond, mergeBB, thenBB);

  { // Codegen the body of the loop
    addAndEmitTo(F, thenBB);
    pass->emit(getThenExpr(), NULL);
    builder.CreateBr(testBB);
  }

  addAndEmitTo(F, mergeBB);
  return getUnitValue();
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

llvm::Value* LLCase::codegen(CodegenPass* pass) {
  llvm::Value* v = pass->emit(scrutinee, NULL);
  llvm::AllocaInst* rv_slot = CreateEntryAlloca(getLLVMType(this->type), "case_slot");
  pass->markAsNeedingImplicitLoads(rv_slot);
  this->dt->codegenDecisionTree(pass, v, rv_slot);
  return rv_slot;
}

llvm::Value* lookupOccs(Occurrence* occ, llvm::Value* v, CodegenPass* pass) {
  const std::vector<int>& occs = occ->offsets;
  llvm::Value* rv = v;
  for (size_t i = 0; i < occs.size(); ++i) {
    llvm::Constant* idx = getConstantInt32For(occs[i]);
    rv = getElementFromComposite(rv, idx, "switch_insp");
  }
  return rv;
}

void DecisionTree::codegenDecisionTree(CodegenPass* pass,
                                       llvm::Value* scrutinee,
                                       llvm::AllocaInst* rv_slot) {
  Value* rv = NULL;
  switch (tag) {
  case DecisionTree::DT_FAIL:
    EDiag() << "DecisionTree codegen, tag = DT_FAIL; v = " << str(scrutinee);
    emitFosterAssert(pass->mod, builder.getInt1(false), "pattern match failure!");
    break;

  case DecisionTree::DT_LEAF:
    ASSERT(this->action != NULL);

    for (size_t i = 0; i < binds.size(); ++i) {
       Value* v = lookupOccs(binds[i].second, scrutinee, pass);
       Value* v_slot = ensureImplicitStackSlot(v, pass);
       trySetName(v_slot, "pat_" + binds[i].first + "_slot");
       pass->valueSymTab.insert(binds[i].first, v_slot);
    }
    rv = pass->emit(action, NULL);
    for (size_t i = 0; i < binds.size(); ++i) {
       pass->valueSymTab.remove(binds[i].first);
    }

    ASSERT(rv != NULL);
    emitStore(rv, rv_slot);
    break;

  case DecisionTree::DT_SWAP:
    ASSERT(false) << "Should not have DT_SWAP nodes at codegen!";
  // end DT_SWAP

  case DecisionTree::DT_SWITCH:
    sc->codegenSwitch(pass, scrutinee, rv_slot);
    break;
  }
}

void SwitchCase::codegenSwitch(CodegenPass* pass,
                               llvm::Value* scrutinee,
                               llvm::AllocaInst* rv_slot) {
  ASSERT(ctors.size() == trees.size());
  ASSERT(ctors.size() >= 1);

  BasicBlock* defaultBB = NULL;
  if (defaultCase != NULL) {
    defaultBB = BasicBlock::Create(getGlobalContext(), "case_default");
  }

  // Special-case codegen for when there's only one
  // possible case, to avoid superfluous branches.
  if (trees.size() == 1 && !defaultCase) {
    trees[0]->codegenDecisionTree(pass, scrutinee, rv_slot);
    return;
  }

  // TODO: switching on a.p. integers: possible at all?
  // If so, it will require manual if-else chaining,
  // not a simple int32 switch...

  BasicBlock* bbEnd = BasicBlock::Create(getGlobalContext(), "case_end");
  BasicBlock* defOrContBB = defaultBB ? defaultBB : bbEnd;
  // Fetch the subterm of the scrutinee being inspected.
  llvm::Value* v = lookupOccs(occ, scrutinee, pass);
  llvm::SwitchInst* si = builder.CreateSwitch(v, defOrContBB, ctors.size());

  Function *F = builder.GetInsertBlock()->getParent();

  for (size_t i = 0; i < ctors.size(); ++i) {
    CtorId c = ctors[i];
    DecisionTree* t = trees[i];

    ConstantInt* onVal = NULL;
    // Compute the "tag" associated with this branch.
    if (c.first == "Int32") {
      onVal = getConstantInt32For(c.second);
    } else if (c.first == "Bool") {
      onVal = builder.getInt1(c.second);
    } else {
      ASSERT(false) << "SwitchCase ctor " << i << "/" << ctors.size()
             << ": " << c.first << "."  << c.second
             << "\n" << str(v)  << "::" << str(v->getType());
    }

    // Emit the code for the branch expression,
    // ending with a branch to the end of the case-expr.
    std::stringstream ss; ss << "casetest_" << i;
    BasicBlock* destBB = BasicBlock::Create(getGlobalContext(), ss.str());
    addAndEmitTo(F, destBB);
    t->codegenDecisionTree(pass, scrutinee, rv_slot);
    builder.CreateBr(bbEnd);

    si->addCase(onVal, destBB);
  }

  if (defaultCase) {
    addAndEmitTo(F, defaultBB);
    defaultCase->codegenDecisionTree(pass, scrutinee, rv_slot);
    builder.CreateBr(bbEnd);
  }

  addAndEmitTo(F, bbEnd);
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
    const llvm::Type* sty = base->getType()->getContainedType(0);
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
  Value* val  = builder.CreateLoad(slot, /*isVolatile=*/ false);
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

LLProc* getClosureVersionOf(llvm::Function* f,
                            const llvm::Type* expectedType,
                            LLVar* arg,
                            CodegenPass* pass);

////////////////////////////////////////////////////////////////////

llvm::Value*
doLowLevelWrapperFnCoercions(const llvm::Type* expectedType,
                             llvm::Value* argV,
                             LLVar* arg,
                             CodegenPass* pass)
{
  // Codegenning   callee(... arg ...)  where arg is a procedure, not a closure.
  llvm::Function* f = llvm::dyn_cast<llvm::Function>(argV);
  if (!f) return argV;

  // Since we made it past type checking, we should have only two
  // possibilities for the callee:
  //
  // 1) A C-linkage function which expects a bare function pointer.
  // 2) A Foster function which expects a closure value.

  if (isPointerToFunction(expectedType)) {
    // Do we want to codegen to handle automatic insertion
    // of type-coercion wrappers? For now, we'll require
    // strict type compatibility.
    return argV;
  } else {
  // Case 2 (passing an env-less C function to a context expecting a closure)
  // is not so simple, since a closure code pointer must take the
  // environment pointer as its first argument, and presumably the external
  // caller will not be providing an env pointer. Thus we need a pointer
  // to a forwarding procedure, which acts as the opposite of a trampoline:
  // instead of excising one (implicitly-added) parameter,
  // the wrapper adds one (implicitly-ignored) parameter to the signature.
  //
  // The simplest approach is to lazily generate a "closure version" of any
  // functions we see being passed directly by name; it would forward
  // all parameters to the regular function, except for the env ptr.
    LLProc* wrapper = getClosureVersionOf(f, expectedType, arg, pass);
    std::string cloname = ParsingContext::freshName("c-clo");
    std::string envname = ParsingContext::freshName("c-clo-empty-env");
    std::vector<LLClosure*> closures;
    closures.push_back(new LLClosure(cloname, envname, wrapper->getName(), getEmptyTuple()));
    LLExpr* clo = new LLClosures(new LLVar(cloname), closures);
    return pass->emit(clo, NULL);
  }
}

////////////////////////////////////////////////////////////////////

llvm::Value* LLCallPrimOp::codegen(CodegenPass* pass) {
  std::vector<llvm::Value*> vals;
  for (size_t i = 0; i < this->args.size(); ++i) {
    vals.push_back(pass->emit(this->args[i], NULL));
  }
  return codegenPrimitiveOperation(this->op, builder, vals);
}

bool isGenericClosureEnvType(const Type* ty) {
  return ty == builder.getInt8PtrTy();
}

llvm::Value* LLCall::codegen(CodegenPass* pass) {
  ASSERT(base != NULL) << "unable to codegen call due to null base";

  Value* FV = pass->emit(base, NULL);
  ASSERT(FV) << "unable to codegen call due to missing value for base";

  const FunctionType* FT = NULL;
  std::vector<Value*> valArgs;

  // TODO extract directly from FnTypeAST
  llvm::CallingConv::ID callingConv = llvm::CallingConv::GHC; // conspicuous
  bool haveSetCallingConv = false;

  if (Function* F = llvm::dyn_cast<Function>(FV)) {
    // Call to top level function
    FT = F->getFunctionType();
    callingConv = F->getCallingConv(); haveSetCallingConv = true;
  } else if (FnTypeAST* closureFnType = dynamic_cast<FnTypeAST*>(base->type)) {
    // If our base has a Foster-level function type but not a
    // LLVM-level function type, it must mean we're calling a closure.
    callingConv = closureFnType->getCallingConventionID(); haveSetCallingConv = true;

    // The function type here includes a parameter for the
    // generic environment type, e.g. (i32 => i32) becomes
    // i32 (i8*, i32).
    FT = dyn_cast<const FunctionType>(
          genericClosureVersionOf(closureFnType)->getLLVMFnType());

    // Load code and env pointers from closure...
    llvm::Value* envPtr =
         getElementFromComposite(FV, getConstantInt32For(1), "getCloEnv");
    FV = getElementFromComposite(FV, getConstantInt32For(0), "getCloCode");

    // Pass env pointer as first parameter to function.
    ASSERT(valArgs.empty());
    valArgs.push_back(envPtr);
  } else {
    ASSERT(false);
  }

  ASSERT(haveSetCallingConv);
  ASSERT(FT) << "call to uncallable something "
             << base->tag << "\t" << base->type->tag
             << "\nFV: " << str(FV);

  // Collect the args, performing coercions if necessary.
  for (size_t i = 0; i < this->args.size(); ++i) {
    const llvm::Type* expectedType = FT->getParamType(valArgs.size());

    llvm::Value* argV = pass->emit(this->args[i], NULL);
    argV = doLowLevelWrapperFnCoercions(expectedType, argV,
                                        this->args[i], pass);

    // This is a an artifact produced by the mutual recursion
    // of the environments of mutually recursive closures.
    if (isGenericClosureEnvType(argV->getType())
      && argV->getType() != expectedType) {
      EDiag() << "emitting bitcast gen2spec " << str(expectedType);
      argV = builder.CreateBitCast(argV, expectedType, "gen2spec");
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
    ASSERT(!callInst->getType()->getContainedType(0)->isPointerTy());

    return pass->storeAndMarkPointerAsGCRootUnknownCtor(callInst);
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

  if (tuplety) {
    const llvm::Type* tupleType = tuplety->getLLVMTypeUnboxed();
    registerType(tupleType, this->typeName, pass->mod, NotArray);
  }

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
           : builder.CreateLoad(slot, "normalize");
  codegenTo(pass, pt);
  return slot;
}

void LLTuple::codegenTo(CodegenPass* pass, llvm::Value* tup_ptr) {
  // Store the values into the point.
  for (size_t i = 0; i < vars.size(); ++i) {
    ASSERT(tup_ptr != NULL);
    Value* dst = builder.CreateConstGEP2_32(tup_ptr, 0, i, "gep");
    Value* val = pass->emit(vars[i], NULL);
    emitStore(val, dst);
  }
}

// Create function    fnName({}* env, arg-args) { arg(arg-args) }
// that hard-codes call to fn referenced by arg,
// and is suitable for embedding as the code ptr in a closure pair,
// unlike the given function, which doesn't want the env ptr.
LLProc* getClosureVersionOf(llvm::Function* f,
                            const llvm::Type* expectedType,
                            LLVar* var,
                            CodegenPass* pass) {
  static std::map<string, LLProc*> sClosureVersions;

  string fnName = "__closureVersionOf__" + f->getName().str();
  if (LLProc* exists = sClosureVersions[fnName]) {
    return exists;
  }

  std::vector<std::string>   inArgNames;
  std::vector<TypeAST*> inArgTypes;
  std::vector<TypeAST*> envTypes;
  std::vector<LLVar*> callArgs;

  inArgNames.push_back(ParsingContext::freshName("__ignored_env__"));
  inArgTypes.push_back(TupleTypeAST::get(envTypes));

  FnTypeAST* oldfnty = dynamic_cast<FnTypeAST*>(var->type);
  ASSERT(oldfnty) << var->name << " :: " << str(var->type);
  for (int i = 0; i < oldfnty->getNumParams(); ++i) {
    LLVar* a = new LLVar(ParsingContext::freshName("_cv_arg"));
    inArgNames.push_back(a->name);
    inArgTypes.push_back(oldfnty->getParamType(i));
    callArgs.push_back(a);
  }

  // Create a scope for the new function's values.
  CodegenPass::ValueScope* scope = pass->valueSymTab.newScope(fnName);
  // But don't use it for doing codegen outside the proto.
  pass->valueSymTab.popExistingScope(scope);

  FnTypeAST* newfnty = new FnTypeAST(oldfnty->getReturnType(),
                                     inArgTypes,
                                     oldfnty->getAnnots());
  newfnty->markAsProc();
  LLExpr* body = new LLCall(var, callArgs, false);
  LLProc* proc = new LLProc(newfnty, fnName, inArgNames,
                            llvm::GlobalValue::InternalLinkage, body);

  // Regular functions get their proto values added when the module
  // starts codegenning, but we need to do it ourselves here.
  proc->codegenProto(pass);
  pass->valueSymTab.insert(proc->getName(), proc->F);
  proc->codegenProc(pass);

  sClosureVersions[fnName] = proc;

  return proc;
}
