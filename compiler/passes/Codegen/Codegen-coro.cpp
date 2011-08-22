// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
//

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h" // for str()
#include "parse/FosterUtils.h" // generic_coro_t

#include "passes/CodegenPass-impl.h"

#include "llvm/Attributes.h"
#include "llvm/CallingConv.h"
#include "llvm/LLVMContext.h"

#include "llvm/Metadata.h"
//#include "llvm/Analysis/DIBuilder.h"
#include "llvm/Support/Dwarf.h"

using llvm::Function;
using llvm::FunctionType;
using llvm::BasicBlock;

using llvm::getGlobalContext;
using foster::builder;
using foster::EDiag;

// Keep synchronized with libfoster_gc_roots.h
enum {
  FOSTER_CORO_INVALID,
  FOSTER_CORO_SUSPENDED,
  FOSTER_CORO_DORMANT,
  FOSTER_CORO_RUNNING,
  FOSTER_CORO_DEAD
};

bool isSingleElementStruct(const llvm::Type* t,
                     const llvm::StructType*& sty) {
  sty = llvm::dyn_cast<llvm::StructType>(t);
  return sty != NULL && sty->getNumElements() == 0;
}

void addCoroArgs(std::vector<const Type*>& fnTyArgs,
                 const llvm::Type* argTypes) {
  const llvm::StructType* sty;
  if (isSingleElementStruct(argTypes, sty)) {
    fnTyArgs.push_back(sty->getElementType(0));
  } else {
    fnTyArgs.push_back(argTypes);
  }
}

void addCoroArgs(std::vector<Value*>& fnArgs,
                 llvm::Value* argVals) {
  const llvm::StructType* sty;
  if (isSingleElementStruct(argVals->getType(), sty)) {
    fnArgs.push_back(getElementFromComposite(argVals, getConstantInt32For(0), "coroarg"));
  } else {
    fnArgs.push_back(argVals);
  }
}

// Returns { { ... generic coro ... }, argTypes }
const llvm::StructType* getSplitCoroType(
  const llvm::Type* argTypes)
{
  std::vector<const llvm::Type*> parts;
  parts.push_back(foster_generic_coro_t);
  // Multiple coro args added as single struct in memory, not separate items
  parts.push_back(argTypes);
  return llvm::StructType::get(getGlobalContext(), parts, /*isPacked=*/ false);
}

// Returns retTy(i8* env, .. arg types ..)
const llvm::FunctionType* getCoroClosureFnType(
  const llvm::Type* retTy,
  const llvm::Type* argTypes)
{
  std::vector<const Type*> args;
  args.push_back(builder.getInt8PtrTy());
  addCoroArgs(args, argTypes);
  return FunctionType::get(retTy, args, /*isVarArg=*/ false);
}

// Returns retTy ( {specific coro}*, .. args ..)
const llvm::FunctionType* getCoroInvokeFnTy(
  const llvm::Type* retTy,
  const llvm::Type* argTypes)
{
  std::vector<const Type*> fnTyArgs;
  fnTyArgs.push_back(ptrTo(getSplitCoroType(argTypes)));
  addCoroArgs(fnTyArgs, argTypes);
  return llvm::FunctionType::get(
                   /*Result=*/   retTy,
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

const llvm::FunctionType* getCoroYieldFnTy(
  const llvm::Type* retTypes,
  const llvm::Type* argTypes)
{
  std::vector<const Type*> fnTyArgs;
  addCoroArgs(fnTyArgs, retTypes);
  return llvm::FunctionType::get(
                   /*Result=*/   argTypes,
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

// Returns { coroFn*, i8* }
const llvm::StructType* getCoroClosureStructTy(
  const llvm::Type* retTy,
  const llvm::Type* argTypes)
{
  std::vector<const llvm::Type*> parts;
  parts.push_back(ptrTo(getCoroClosureFnType(retTy, argTypes)));
  parts.push_back(builder.getInt8PtrTy());
  return llvm::StructType::get(getGlobalContext(), parts, /*isPacked=*/ false);
}

// Returns { specific coro }* (closure struct*)
const llvm::FunctionType* getCoroCreateFnTy(
  const llvm::Type* retTy,
  const llvm::Type* argTypes)
{
  std::vector<const Type*> fnTyArgs;
  fnTyArgs.push_back(ptrTo(getCoroClosureStructTy(retTy, argTypes)));
  return llvm::FunctionType::get(
                   /*Result=*/   ptrTo(getSplitCoroType(argTypes)),
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

// Returns void (i8*)
const llvm::FunctionType* getCoroWrapperFnTy() {
  std::vector<const Type*> fnTyArgs;
  fnTyArgs.push_back(builder.getInt8PtrTy());
  return llvm::FunctionType::get(
                   /*Result=*/   builder.getVoidTy(),
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

void emitPrintI32(llvm::Module* mod, int x) {
  llvm::Value* print_i32 = mod->getFunction("print_i32");
  builder.CreateCall(print_i32, getConstantInt32For(x));
}

void emitPrintRef(llvm::Module* mod, llvm::Value* ref) {
  llvm::Value* print_ref = mod->getFunction("print_ref");
  llvm::Value* bc = builder.CreateBitCast(ref, builder.getInt8PtrTy());
  builder.CreateCall(print_ref, bc);
}

// in CodegenUtils.cpp
void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr);

////////////////////////////////////////////////////////////////////

int coroField_Context() { return 0; }
int coroField_Sibling() { return 1; }
int coroField_Fn() { return 2; }
int coroField_Env() { return 3; }
int coroField_Invoker() { return 4; }
int coroField_IndirectSelf() { return 5; }
int coroField_Status() { return 6; }

////////////////////////////////////////////////////////////////////
////////////////////////// CORO WRAPPER  ///////////////////////////
////////////////////////////////////////////////////////////////////

Value* emitCoroWrapperFn(
  CodegenPass* pass,
  const llvm::Type* retTy,
  const llvm::Type* argTypes)
{
  // Create a function of type  void (i8* f_c)
  // which passes arguments to/from a function of type  rTy (a1, ... , aN)
  std::string ss_str;
  llvm::raw_string_ostream ss(ss_str);
  ss << ".foster_coro_wrapper_" << str(retTy) << "__" << str(argTypes);

  std::string functionName = ss.str();

  Function* wrapper = Function::Create(
    /*Type=*/    getCoroWrapperFnTy(),
    /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
    /*Name=*/    functionName, pass->mod);

  // The wrapper has to use the C calling convention because
  // libcoro expects the f_c arg to be pushed on the stack.
  wrapper->setCallingConv(llvm::CallingConv::C);
  wrapper->setGC("fostergc");

  /////////////////////////////

  Function::arg_iterator args = wrapper->arg_begin();
  Value* ptr_f_c = args++;
  ptr_f_c->setName("f_c");

  BasicBlock* prevBB = builder.GetInsertBlock();
  pass->addEntryBB(wrapper);

  Value* fc  = builder.CreateBitCast(ptr_f_c, ptrTo(getSplitCoroType(argTypes)));
  Value* fcg = builder.CreateConstInBoundsGEP2_32(fc, 0, 0, "fc_gen");

  Value* fn_addr = builder.CreateConstInBoundsGEP2_32(fcg, 0, coroField_Fn(), "fnaddr");
  Value* fn_gen  = builder.CreateLoad(fn_addr, "fn_gen");
  Value* fn      = builder.CreateBitCast(fn_gen,
                                      ptrTo(getCoroClosureFnType(retTy, argTypes)));

  Value* sib_addr = builder.CreateConstInBoundsGEP2_32(fcg, 0, coroField_Sibling(), "sibaddr");
  Value* sib_gen  = builder.CreateLoad(sib_addr, "sib_gen");
  Value* sib      = builder.CreateBitCast(sib_gen, ptrTo(getSplitCoroType(retTy)));

  Value* env_addr = builder.CreateConstInBoundsGEP2_32(fcg, 0, coroField_Env(), "envaddr");
  Value* env      = builder.CreateLoad(env_addr, "env_ptr");

  Value* arg_addr = builder.CreateConstInBoundsGEP2_32(fc, 0, 1, "argaddr");
  Value* arg      = builder.CreateLoad(arg_addr, "arg");

  std::vector<Value*> callArgs;
  callArgs.push_back(env);
  addCoroArgs(callArgs, arg);

  llvm::CallInst* call  = builder.CreateCall(fn, callArgs.begin(), callArgs.end());
  call->setCallingConv(llvm::CallingConv::Fast);

  // Store the result of the call in the sibling's arg slot
  Value* sib_arg_addr = builder.CreateConstInBoundsGEP2_32(sib, 0, 1, "sibargaddr");
  builder.CreateStore(call, sib_arg_addr, /*isVolatile=*/ false);

  // Mark the coro as being dead
  Value* status_addr = builder.CreateConstInBoundsGEP2_32(fcg, 0, coroField_Status(), "statusaddr");
  builder.CreateStore(getConstantInt32For(4), status_addr);

  builder.CreateRetVoid();

  // TODO add assertion that control flow does not reach here

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return wrapper;
}

void registerCoroType(llvm::Module* mod, const llvm::Type* argTypes) {
  std::string ss_str;
  llvm::raw_string_ostream ss(ss_str);
  ss << "coro_" << str(argTypes);

  mod->addTypeName(ss.str(), ptrTo(getSplitCoroType(argTypes)));
}

////////////////////////////////////////////////////////////////////
////////////////////////// CORO CREATE  ////////////////////////////
////////////////////////////////////////////////////////////////////

// Returns a function of type  <coro> (closure)
Value* CodegenPass::emitCoroCreateFn(
                        const llvm::Type* retTy,
                        const llvm::Type* argTypes)
{
  std::string ss_str;
  llvm::raw_string_ostream ss(ss_str);
  ss << ".foster_coro_create_" << str(retTy) << "__" << str(argTypes);

  std::string functionName = ss.str();

  Function* create = Function::Create(
    /*Type=*/    getCoroCreateFnTy(retTy, argTypes),
    /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
    /*Name=*/    functionName, this->mod);

  create->setCallingConv(llvm::CallingConv::Fast);
  create->setGC("fostergc");

  registerCoroType(this->mod, argTypes);
  registerCoroType(this->mod, retTy);

  Function::arg_iterator args = create->arg_begin();
  Value* pclo = args++;
  pclo->setName("pclo");

  BasicBlock* prevBB = builder.GetInsertBlock();
  this->addEntryBB(create);

  int8_t bogusCtor = -1;
  // foster_coro_i32_i32* fcoro = (foster_coro_i32_i32*) memalloc_cell(NULL);
  // foster_coro_i32_i32* ccoro = (foster_coro_i32_i32*) memalloc_cell(NULL);
  Value* fcoro_slot = this->emitMalloc(getSplitCoroType(argTypes), bogusCtor);
  Value* ccoro_slot = this->emitMalloc(getSplitCoroType(retTy   ), bogusCtor);

  Value* fcoro      = builder.CreateLoad(fcoro_slot, "fcoro");
  Value* ccoro      = builder.CreateLoad(ccoro_slot, "ccoro");

  // TODO call memset on the full structs

  Value* gfcoro = builder.CreateConstInBoundsGEP2_32(fcoro, 0, 0, "gfcoro");
  Value* gccoro = builder.CreateConstInBoundsGEP2_32(ccoro, 0, 0, "gccoro");

  // fcoro->g.sibling = reinterpret_cast<foster_generic_coro*>(ccoro);
  // ccoro->g.sibling = reinterpret_cast<foster_generic_coro*>(fcoro);
  Value* fcoro_sibling_gen = builder.CreateConstInBoundsGEP2_32(gfcoro, 0, coroField_Sibling(), "fcoro_sib");
  Value* ccoro_sibling_gen = builder.CreateConstInBoundsGEP2_32(gccoro, 0, coroField_Sibling(), "ccoro_sib");
  Value* fcoro_sibling = builder.CreateBitCast(fcoro_sibling_gen, ptrTo(ccoro->getType()));
  Value* ccoro_sibling = builder.CreateBitCast(ccoro_sibling_gen, ptrTo(fcoro->getType()));
  builder.CreateStore(ccoro, fcoro_sibling);
  builder.CreateStore(fcoro, ccoro_sibling);

  // fcoro->g.fn = reinterpret_cast<coro_func>(pclo->code);
  // ccoro->g.fn  = NULL;
  Value* fcoro_fn = builder.CreateConstInBoundsGEP2_32(gfcoro, 0, coroField_Fn(), "fcoro_fn");
  Value* ccoro_fn = builder.CreateConstInBoundsGEP2_32(gccoro, 0, coroField_Fn(), "ccoro_fn");
  storeNullPointerToSlot(ccoro_fn);

  Value* clo_code_ptr = builder.CreateConstInBoundsGEP2_32(pclo, 0, 0, "clo_fn_slot");
  Value* clo_code     = builder.CreateLoad(clo_code_ptr, "clo_fn");
  Value* clo_code_gen = builder.CreateBitCast(clo_code, fcoro_fn->getType()->getContainedType(0));
  builder.CreateStore(clo_code_gen, fcoro_fn);

  // ccoro->g.env = NULL;
  // fcoro->g.env = pclo->env;
  Value* fcoro_env = builder.CreateConstInBoundsGEP2_32(gfcoro, 0, coroField_Env(), "fcoro_env");
  Value* ccoro_env = builder.CreateConstInBoundsGEP2_32(gccoro, 0, coroField_Env(), "ccoro_env");
  storeNullPointerToSlot(ccoro_env);

  Value* clo_env_ptr = builder.CreateConstInBoundsGEP2_32(pclo, 0, 1, "clo_env_slot");
  Value* clo_env     = builder.CreateLoad(clo_env_ptr, "clo_env");
  Value* clo_env_gen = builder.CreateBitCast(clo_env, fcoro_env->getType()->getContainedType(0));
  builder.CreateStore(clo_env_gen, fcoro_env);

  // fcoro->g.invoker = NULL;
  // ccoro->g.invoker = NULL;
  Value* fcoro_invoker = builder.CreateConstInBoundsGEP2_32(gfcoro, 0, coroField_Invoker(), "fcoro_sib");
  Value* ccoro_invoker = builder.CreateConstInBoundsGEP2_32(gccoro, 0, coroField_Invoker(), "ccoro_sib");
  storeNullPointerToSlot(fcoro_invoker);
  storeNullPointerToSlot(ccoro_invoker);

  // fcoro->g.indirect_self = NULL;
  // ccoro->g.indirect_self = NULL;
  Value* fcoro_indirect_self = builder.CreateConstInBoundsGEP2_32(gfcoro, 0, coroField_IndirectSelf(), "fcoro_self");
  Value* ccoro_indirect_self = builder.CreateConstInBoundsGEP2_32(gccoro, 0, coroField_IndirectSelf(), "ccoro_self");
  storeNullPointerToSlot(fcoro_indirect_self);
  storeNullPointerToSlot(ccoro_indirect_self);

  Value* fcoro_status = builder.CreateConstInBoundsGEP2_32(gfcoro, 0, coroField_Status(), "fcoro_status");
  Value* ccoro_status = builder.CreateConstInBoundsGEP2_32(gccoro, 0, coroField_Status(), "ccoro_status");
  builder.CreateStore(getConstantInt32For(FOSTER_CORO_DORMANT), fcoro_status);
  builder.CreateStore(getConstantInt32For(FOSTER_CORO_INVALID), ccoro_status);

  llvm::Value* wrapper = emitCoroWrapperFn(this, retTy, argTypes);
  // coro_func wrapper = ...;
  // foster_coro_create(wrapper, fcoro);
  llvm::Value* foster_coro_create = this->mod->getFunction("foster_coro_create");
  ASSERT(foster_coro_create != NULL);

  Value* fcoro_gen = builder.CreateBitCast(fcoro, builder.getInt8PtrTy());
  llvm::CallInst* call = builder.CreateCall2(foster_coro_create, wrapper, fcoro_gen);
  markAsNonAllocating(call);

  // return (foster_coro_i32_i32*) fcoro;
  builder.CreateRet(fcoro);

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return create;
}

////////////////////////////////////////////////////////////////////
//////////////////////////  INVOKE/YIELD  //////////////////////////
////////////////////////////////////////////////////////////////////

void generateInvokeYield(bool isYield,
                         CodegenPass* pass,
                         llvm::Value* coro,
                         const llvm::Type* retTy,
                         const llvm::Type* argTypes,
                         const std::vector<llvm::Value*>& inputArgs) {
  llvm::Value* coro_slot = pass->storeAndMarkPointerAsGCRoot(coro);

  llvm::Value* current_coro_slot = pass->mod->getGlobalVariable("current_coro");
  Value* current_coro = builder.CreateLoad(current_coro_slot);

  /// TODO: call coro_dump(coro)

  // Call foster_assert to verify that
  // the target coro is in the expected state.
  llvm::Value* expectedStatus = NULL;
  const char*  expectedStatusMsg = NULL;
  if (isYield) {
    expectedStatus = getConstantInt32For(FOSTER_CORO_SUSPENDED);
    expectedStatusMsg = "can only yield to a suspended coroutine";
  } else {
    expectedStatus = getConstantInt32For(FOSTER_CORO_DORMANT);
    expectedStatusMsg = "can only resume a dormant coroutine";
  }

  Value* status_addr = builder.CreateConstInBoundsGEP2_32(coro, 0, coroField_Status(), "statusaddr");
  Value* status = builder.CreateLoad(status_addr);
  Value* cond = builder.CreateICmpEQ(status, expectedStatus);
  emitFosterAssert(pass->mod, cond, expectedStatusMsg);

  // Store the input arguments to coro->arg.
  Value* concrete_coro = builder.CreateBitCast(coro,
                                         ptrTo(getSplitCoroType(
                                              (isYield ? retTy : argTypes))));
  Value* coroArg_slot = builder.CreateConstInBoundsGEP2_32(concrete_coro, 0, 1);
  if (inputArgs.size() == 1) {
    builder.CreateStore(inputArgs[0], coroArg_slot);
  } else {
    for (size_t i = 0; i < inputArgs.size(); ++i) {
      Value* slot = builder.CreateConstInBoundsGEP2_32(coroArg_slot, 0, i);
      builder.CreateStore(inputArgs[i], slot);
    }
  }

  // Set the status fields of both coros.
  Value* sibling_slot = builder.CreateConstInBoundsGEP2_32(coro, 0, coroField_Sibling(), "siblingaddr");
  Value* sibling_ptr_gen = builder.CreateLoad(sibling_slot);

  Value* sib_status_addr = builder.CreateConstInBoundsGEP2_32(sibling_ptr_gen, 0, coroField_Status(), "sibstatusaddr");

  // TODO once we have multiple threads, this will need to
  // be done atomically or under a lock (and error handling added).
  if (isYield) {
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_INVALID), status_addr);
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_DORMANT), sib_status_addr);
  } else {
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_RUNNING), status_addr);
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_SUSPENDED), sib_status_addr);
  }

  // If we're invoking, "push" the coro on the coro "stack".
  if (!isYield) {
    ///   coro->invoker = current_coro;
    Value* invoker_slot = builder.CreateConstInBoundsGEP2_32(coro, 0, coroField_Invoker());
    builder.CreateStore(current_coro, invoker_slot);

    ///   current_coro = coro;
    builder.CreateStore(coro, current_coro_slot);
  }

  Value* coroTransfer = pass->mod->getFunction("coro_transfer");
  ASSERT(coroTransfer != NULL);
  Value*     ctx_addr = builder.CreateConstInBoundsGEP2_32(coro,            0, coroField_Context());
  Value* sib_ctx_addr = builder.CreateConstInBoundsGEP2_32(sibling_ptr_gen, 0, coroField_Context());

  llvm::CallInst* transfer = builder.CreateCall2(coroTransfer, sib_ctx_addr, ctx_addr);
  transfer->addAttribute(1, llvm::Attribute::InReg);
  transfer->addAttribute(2, llvm::Attribute::InReg);

  //=================================================================
  //=================================================================

  // A GC may have been triggered, so re-load locals from the stack.
  coro = builder.CreateLoad(coro_slot);
  status_addr = builder.CreateConstInBoundsGEP2_32(coro, 0, coroField_Status(), "statusaddr");
  sibling_slot = builder.CreateConstInBoundsGEP2_32(coro, 0, coroField_Sibling(), "siblingaddr");
  sibling_ptr_gen = builder.CreateLoad(sibling_slot);

  sib_status_addr = builder.CreateConstInBoundsGEP2_32(sibling_ptr_gen, 0, coroField_Status(), "sibstatusaddr");

  if (!isYield) { // likewise, pop the "stack" when we return from
    ///   current_coro = coro->invoker;
    Value* invoker_slot = builder.CreateConstInBoundsGEP2_32(coro, 0, coroField_Invoker());
    Value* invoker      = builder.CreateLoad(invoker_slot);
    builder.CreateStore(invoker, current_coro_slot);
  }

  // So if we were originally yielding, then we are
  // now being re-invoked, possibly by a different
  // coro and/or a different thread!
  // But our sibling coro remains the same, it's just the
  // stack that it refers to that might have changed.
  if (isYield) {
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_SUSPENDED), status_addr);
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_RUNNING), sib_status_addr);
  } else {
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_DORMANT), status_addr);
    builder.CreateStore(getConstantInt32For(FOSTER_CORO_INVALID), sib_status_addr);
  }

  sibling_slot = builder.CreateConstInBoundsGEP2_32(coro, 0, coroField_Sibling(), "siblingaddr");
  sibling_ptr_gen      = builder.CreateLoad(sibling_slot);
  Value* sibling_ptr   = builder.CreateBitCast(sibling_ptr_gen,
                                         ptrTo(getSplitCoroType(
                                               (isYield ? argTypes : retTy))));
  /// return sibling->arg;
  Value* sibling_arg_slot = builder.CreateConstInBoundsGEP2_32(sibling_ptr, 0, 1, "sibling_arg_slot");
  Value* sibling_arg      = builder.CreateLoad(sibling_arg_slot);

  builder.CreateRet(sibling_arg);
}

////////////////////////////////////////////////////////////////////
////////////////////////// CORO INVOKE  ////////////////////////////
////////////////////////////////////////////////////////////////////

Value* CodegenPass::emitCoroInvokeFn(
                        const llvm::Type* retTy,
                        const llvm::Type* argTypes) {
  // Create a function of type  retTy (cloty*)

  std::string ss_str;
  llvm::raw_string_ostream ss(ss_str);
  ss << ".foster_coro_invoke_" << str(retTy) << "__" << str(argTypes);

  std::string functionName = ss.str();

  Function* create = Function::Create(
    /*Type=*/    getCoroInvokeFnTy(retTy, argTypes),
    /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
    /*Name=*/    functionName, this->mod);

  create->setCallingConv(llvm::CallingConv::Fast);
  create->setGC("fostergc");

  std::vector<Value*> inputArgs;
  Function::arg_iterator args = create->arg_begin();
  Value* coro_concrete = args++;

  while (args != create->arg_end()) {
    inputArgs.push_back(args++);
  }

  BasicBlock* prevBB = builder.GetInsertBlock();
  this->addEntryBB(create);

  Value* coro = builder.CreateBitCast(coro_concrete, ptrTo(foster_generic_coro_t));

  generateInvokeYield(false, this, coro, retTy, argTypes, inputArgs);

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return create;
}

////////////////////////////////////////////////////////////////////
////////////////////////// CORO YIELD //////////////////////////////
////////////////////////////////////////////////////////////////////

// Return a function with type   argTypes (retTy1...retTyN)
// Note that "retTypes" denote the arguments, and "argTypes"
// the (possibly structure-typed) result. The reason is that
// the parameter names match create/invoke for consistency,
// and yield does things the other way 'round.
Value* CodegenPass::emitCoroYieldFn(
                        const llvm::Type* retTy,
                        const llvm::Type* argTypes) {
  std::string ss_str;
  llvm::raw_string_ostream ss(ss_str);
  ss << ".foster_coro_yield_" << str(retTy) << "__" << str(argTypes);

  std::string functionName = ss.str();

  Function* yield = Function::Create(
    /*Type=*/    getCoroYieldFnTy(retTy, argTypes),
    /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
    /*Name=*/    functionName, this->mod);

  yield->setCallingConv(llvm::CallingConv::Fast);
  yield->setGC("fostergc");

  std::vector<Value*> inputArgs;
  Function::arg_iterator args = yield->arg_begin();
  while (args != yield->arg_end()) {
    inputArgs.push_back(args++);
  }

  BasicBlock* prevBB = builder.GetInsertBlock();
  this->addEntryBB(yield);

  Value* current_coro_slot = this->mod->getGlobalVariable("current_coro");
  ASSERT(current_coro_slot != NULL);

  Value* current_coro = builder.CreateLoad(current_coro_slot, "coro");

  // Ensure that we actually have a coroutine!
  emitFosterAssert(mod, builder.CreateIsNotNull(current_coro),
                   "Cannot call yield before invoking a coroutine!");

  Value* sibling_slot = builder.CreateConstInBoundsGEP2_32(current_coro, 0, coroField_Sibling(), "siblingaddr");
  Value* coro = builder.CreateLoad(sibling_slot);

  generateInvokeYield(true, this, coro, retTy, argTypes, inputArgs);

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return yield;
}

