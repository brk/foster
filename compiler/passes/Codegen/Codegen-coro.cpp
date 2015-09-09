// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
//

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h" // for str()

#include "passes/CodegenPass-impl.h"

#include "llvm/IR/Attributes.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/LLVMContext.h"

#include "llvm/IR/Metadata.h"
//#include "llvm/Analysis/DIBuilder.h"
#include "llvm/Support/Dwarf.h"

using llvm::Function;
using llvm::FunctionType;
using llvm::BasicBlock;

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

const char kFosterCoroCreate[] = "foster_coro_create";
const char kCoroTransfer[]     = "coro_transfer";

Value* codegenCurrentCoroSlot(llvm::Module* mod) {
  Value* f = mod->getFunction("__foster_get_current_coro_slot");
  return builder.CreateCall(f, llvm::None, "currentCoroSlot");
}

bool isSingleElementStruct(llvm::Type* t,
                     llvm::StructType*& sty) {
  sty = llvm::dyn_cast<llvm::StructType>(t);
  return sty != NULL && sty->getNumElements() == 0;
}

void addCoroArgs(std::vector<Type*>& fnTyArgs,
                 llvm::Type* argTypes) {
  llvm::StructType* sty;
  if (isSingleElementStruct(argTypes, sty)) {
    fnTyArgs.push_back(sty->getElementType(0));
  } else {
    fnTyArgs.push_back(argTypes);
  }
}

void addCoroArgs(std::vector<Value*>& fnArgs,
                 llvm::Value* argVals) {
  llvm::StructType* sty;
  if (isSingleElementStruct(argVals->getType(), sty)) {
    fnArgs.push_back(getElementFromComposite(argVals, 0, "coroarg"));
  } else {
    fnArgs.push_back(argVals);
  }
}

llvm::Value* gep(llvm::Value *Ptr, unsigned Idx0, unsigned Idx1, const llvm::Twine &Name="") {
  return builder.CreateConstInBoundsGEP2_32(nullptr, Ptr, Idx0, Idx1, Name);
}

// Returns { { ... generic coro ... }, argTypes }
StructTypeAST* getSplitCoroTyp(TypeAST* argTypes)
{
  std::vector<TypeAST*> parts;
  parts.push_back(foster_generic_coro_ast);
  // Multiple coro args added as single struct in memory, not separate items
  parts.push_back(argTypes);
  return StructTypeAST::get(parts);
}

// Returns { { ... generic coro ... }, argTypes }
llvm::StructType* getSplitCoroType(
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> parts;
  parts.push_back(foster_generic_coro_t);
  // Multiple coro args added as single struct in memory, not separate items
  parts.push_back(argTypes);
  return llvm::StructType::get(builder.getContext(),
                               llvm::makeArrayRef(parts),
                               /*isPacked=*/ false);
}

// Returns retTy(i8* env, .. arg types ..)
llvm::FunctionType* getCoroClosureFnType(
  llvm::Type* retTy,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> args;
  args.push_back(builder.getInt8PtrTy());
  addCoroArgs(args, argTypes);
  return FunctionType::get(retTy, args, /*isVarArg=*/ false);
}

// Returns retTy ( {specific coro}*, .. args ..)
llvm::FunctionType* getCoroInvokeFnTy(
  llvm::Type* retTy,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> fnTyArgs;
  fnTyArgs.push_back(ptrTo(getSplitCoroType(argTypes)));
  addCoroArgs(fnTyArgs, argTypes);
  return llvm::FunctionType::get(
                   /*Result=*/   retTy,
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

llvm::FunctionType* getCoroYieldFnTy(
  llvm::Type* retTypes,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> fnTyArgs;
  addCoroArgs(fnTyArgs, retTypes);
  return llvm::FunctionType::get(
                   /*Result=*/   argTypes,
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

// Returns { coroFn*, i8* }
llvm::StructType* getCoroClosureStructTy(
  llvm::Type* retTy,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> parts;
  parts.push_back(ptrTo(getCoroClosureFnType(retTy, argTypes)));
  parts.push_back(builder.getInt8PtrTy());
  return llvm::StructType::get(builder.getContext(), parts, /*isPacked=*/ false);
}

// Returns { specific coro }* (closure struct*)
llvm::FunctionType* getCoroCreateFnTy(
  llvm::Type* retTy,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> fnTyArgs;
  fnTyArgs.push_back(ptrTo(getCoroClosureStructTy(retTy, argTypes)));
  return llvm::FunctionType::get(
                   /*Result=*/   ptrTo(getSplitCoroType(argTypes)),
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

// Returns void (i8*)
llvm::FunctionType* getCoroWrapperFnTy() {
  std::vector<llvm::Type*> fnTyArgs;
  fnTyArgs.push_back(builder.getInt8PtrTy());
  return llvm::FunctionType::get(
                   /*Result=*/   builder.getVoidTy(),
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

// in CodegenUtils.cpp
void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr);

////////////////////////////////////////////////////////////////////

int coroField_Context()      { return 0; }
int coroField_Sibling()      { return 1; }
int coroField_Fn()           { return 2; }
int coroField_Env()          { return 3; }
int coroField_Invoker()      { return 4; }
int coroField_IndirectSelf() { return 5; }
int coroField_Status()       { return 6; }

////////////////////////////////////////////////////////////////////
////////////////////////// CORO WRAPPER  ///////////////////////////
////////////////////////////////////////////////////////////////////

Value* emitCoroWrapperFn(
  CodegenPass* pass,
  llvm::Type* retTy,
  llvm::Type* argTypes)
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
  Value* fcg = gep(fc, 0, 0, "fc_gen");

  Value* fn_addr = gep(fcg, 0, coroField_Fn(), "fnaddr");
  Value* fn_gen  = builder.CreateLoad(fn_addr, "fn_gen");
  Value* fn      = builder.CreateBitCast(fn_gen,
                                      ptrTo(getCoroClosureFnType(retTy, argTypes)));

  Value* sib_addr = gep(fcg, 0, coroField_Sibling(), "sibaddr");
  Value* sib_gen  = builder.CreateLoad(sib_addr, "sib_gen");
  Value* sib      = builder.CreateBitCast(sib_gen, ptrTo(getSplitCoroType(retTy)));

  Value* env_addr = gep(fcg, 0, coroField_Env(), "envaddr");
  Value* env      = builder.CreateLoad(env_addr, "env_ptr");

  Value* arg_addr = gep(fc, 0, 1, "argaddr");
  Value* arg      = builder.CreateLoad(arg_addr, "arg");

  std::vector<Value*> callArgs;
  callArgs.push_back(env);
  addCoroArgs(callArgs, arg);

  llvm::CallInst* call  = builder.CreateCall(fn, llvm::makeArrayRef(callArgs));
  call->setCallingConv(llvm::CallingConv::Fast);

  // Store the result of the call in the sibling's arg slot
  Value* sib_arg_addr = gep(sib, 0, 1, "sibargaddr");
  builder.CreateStore(call, sib_arg_addr, /*isVolatile=*/ false);

  // Mark the coro as being dead
  Value* status_addr = gep(fcg, 0, coroField_Status(), "statusaddr");
  builder.CreateStore(builder.getInt32(4), status_addr);

  builder.CreateRetVoid();

  // TODO add assertion that control flow does not reach here

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return wrapper;
}

void registerCoroType(llvm::Module* mod, llvm::Type* argTypes) {
  std::string ss_str;
  llvm::raw_string_ostream ss(ss_str);
  ss << "coro_" << str(argTypes);
  EDiag() << "Need to register type name: " << ss.str();
  //mod->addTypeName(ss.str(), ptrTo(getSplitCoroType(argTypes)));
}

////////////////////////////////////////////////////////////////////
////////////////////////// CORO CREATE  ////////////////////////////
////////////////////////////////////////////////////////////////////

// Returns a function of type  <coro> (closure)
Value* CodegenPass::emitCoroCreateFn(
                        TypeAST* retTyp,
                        TypeAST* argTyps)
{
  llvm::Type* retTy    = retTyp->getLLVMType();
  llvm::Type* argTypes = argTyps->getLLVMType();

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

  CtorRepr bogusCtor; bogusCtor.smallId = -1;
  // foster_coro_i32_i32* ccoro = (foster_coro_i32_i32*) memalloc_cell(NULL);
  // foster_coro_i32_i32* fcoro = (foster_coro_i32_i32*) memalloc_cell(NULL);
  Value* ccoro_slot = this->storeAndMarkPointerAsGCRoot(this->emitMalloc(getSplitCoroTyp(retTyp ), bogusCtor, "ccoro", /*init*/ false));
  Value* fcoro      =                                   this->emitMalloc(getSplitCoroTyp(argTyps), bogusCtor, "fcoro", /*init*/ true);
  // See note below: no root needed because foster_coro_create is written
  // not to induce a GC copy.
  Value* ccoro      = builder.CreateLoad(ccoro_slot, "ccoro");

  // TODO call memset on the full structs

  Value* gfcoro = gep(fcoro, 0, 0, "gfcoro");
  Value* gccoro = gep(ccoro, 0, 0, "gccoro");

  // fcoro->g.sibling = reinterpret_cast<foster_generic_coro*>(ccoro);
  // ccoro->g.sibling = reinterpret_cast<foster_generic_coro*>(fcoro);
  Value* fcoro_sibling_gen = gep(gfcoro, 0, coroField_Sibling(), "fcoro_sib");
  Value* ccoro_sibling_gen = gep(gccoro, 0, coroField_Sibling(), "ccoro_sib");
  Value* fcoro_sibling = builder.CreateBitCast(fcoro_sibling_gen, ptrTo(ccoro->getType()));
  Value* ccoro_sibling = builder.CreateBitCast(ccoro_sibling_gen, ptrTo(fcoro->getType()));
  builder.CreateStore(ccoro, fcoro_sibling);
  builder.CreateStore(fcoro, ccoro_sibling);

  // fcoro->g.fn = reinterpret_cast<coro_func>(pclo->code);
  // ccoro->g.fn  = NULL;
  Value* fcoro_fn = gep(gfcoro, 0, coroField_Fn(), "fcoro_fn");
  Value* ccoro_fn = gep(gccoro, 0, coroField_Fn(), "ccoro_fn");
  storeNullPointerToSlot(ccoro_fn);

  Value* clo_code_ptr = gep(pclo, 0, 0, "clo_fn_slot");
  Value* clo_code     = builder.CreateLoad(clo_code_ptr, "clo_fn");
  Value* clo_code_gen = builder.CreateBitCast(clo_code, fcoro_fn->getType()->getContainedType(0));
  builder.CreateStore(clo_code_gen, fcoro_fn);

  // ccoro->g.env = NULL;
  // fcoro->g.env = pclo->env;
  Value* fcoro_env = gep(gfcoro, 0, coroField_Env(), "fcoro_env");
  Value* ccoro_env = gep(gccoro, 0, coroField_Env(), "ccoro_env");
  storeNullPointerToSlot(ccoro_env);

  Value* clo_env_ptr = gep(pclo, 0, 1, "clo_env_slot");
  Value* clo_env     = builder.CreateLoad(clo_env_ptr, "clo_env");
  Value* clo_env_gen = builder.CreateBitCast(clo_env, fcoro_env->getType()->getContainedType(0));
  builder.CreateStore(clo_env_gen, fcoro_env);

  // fcoro->g.invoker = NULL;
  // ccoro->g.invoker = NULL;
  Value* fcoro_invoker = gep(gfcoro, 0, coroField_Invoker(), "fcoro_sib");
  Value* ccoro_invoker = gep(gccoro, 0, coroField_Invoker(), "ccoro_sib");
  storeNullPointerToSlot(fcoro_invoker);
  storeNullPointerToSlot(ccoro_invoker);

  // fcoro->g.indirect_self = NULL;
  // ccoro->g.indirect_self = NULL;
  Value* fcoro_indirect_self = gep(gfcoro, 0, coroField_IndirectSelf(), "fcoro_self");
  Value* ccoro_indirect_self = gep(gccoro, 0, coroField_IndirectSelf(), "ccoro_self");
  storeNullPointerToSlot(fcoro_indirect_self);
  storeNullPointerToSlot(ccoro_indirect_self);

  Value* fcoro_status = gep(gfcoro, 0, coroField_Status(), "fcoro_status");
  Value* ccoro_status = gep(gccoro, 0, coroField_Status(), "ccoro_status");
  builder.CreateStore(builder.getInt32(FOSTER_CORO_DORMANT), fcoro_status);
  builder.CreateStore(builder.getInt32(FOSTER_CORO_INVALID), ccoro_status);

  llvm::Value* wrapper = emitCoroWrapperFn(this, retTy, argTypes);
  // coro_func wrapper = ...;
  // foster_coro_create(wrapper, fcoro);
  llvm::Value* foster_coro_create = this->mod->getFunction(kFosterCoroCreate);
  ASSERT(foster_coro_create != NULL);

  Value* fcoro_gen = builder.CreateBitCast(fcoro, builder.getInt8PtrTy());
  llvm::CallInst* call = builder.CreateCall(foster_coro_create, { wrapper, fcoro_gen });
  markAsNonAllocating(call);

  // return (foster_coro_i32_i32*) fcoro;
  builder.CreateRet(builder.CreateBitCast(fcoro,
                                    ptrTo(getSplitCoroType(argTypes))));

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return create;
}

////////////////////////////////////////////////////////////////////
//////////////////////////  INVOKE/YIELD  //////////////////////////
////////////////////////////////////////////////////////////////////

// When LLVM links libfoster_coro with the rest of foster_runtime,
// for some reason it doesn't unify the two identical definitions
// of %struct.foster_generic_coro, so the function
// __foster_get_current_coro_slot() ends up with the "wrong" type.
// So we sometimes insert coercions to undo the silliness.
Value* createStore(Value* val, Value* ptr) {
  return builder.CreateStore(val, builder.CreateBitCast(ptr, ptrTo(val->getType())));
}

void generateInvokeYield(bool isYield,
                         CodegenPass* pass,
                         llvm::Value* coro,
                         llvm::Type* retTy,
                         llvm::Type* argTypes,
                         const std::vector<llvm::Value*>& inputArgs) {
  llvm::Value* coro_slot = pass->storeAndMarkPointerAsGCRoot(coro);

  llvm::Value* current_coro_slot = codegenCurrentCoroSlot(pass->mod);
  Value* current_coro = builder.CreateLoad(current_coro_slot);

  /// TODO: call coro_dump(coro)

  // Call foster_assert to verify that
  // the target coro is in the expected state.
  llvm::Value* expectedStatus = NULL;
  const char*  expectedStatusMsg = NULL;
  if (isYield) {
    expectedStatus = builder.getInt32(FOSTER_CORO_SUSPENDED);
    expectedStatusMsg = "can only yield to a suspended coroutine";
  } else {
    expectedStatus = builder.getInt32(FOSTER_CORO_DORMANT);
    expectedStatusMsg = "can only resume a dormant coroutine";
  }

  Value* status_addr = gep(coro, 0, coroField_Status(), "statusaddr");
  Value* status = builder.CreateLoad(status_addr);
  Value* cond = builder.CreateICmpEQ(status, expectedStatus);
  emitFosterAssert(pass->mod, cond, expectedStatusMsg);

  // Store the input arguments to coro->arg.
  Value* concrete_coro = builder.CreateBitCast(coro,
                                         ptrTo(getSplitCoroType(
                                              (isYield ? retTy : argTypes))));
  Value* coroArg_slot = gep(concrete_coro, 0, 1);
  if (inputArgs.size() == 1) {
    builder.CreateStore(inputArgs[0], coroArg_slot);
  } else {
    for (size_t i = 0; i < inputArgs.size(); ++i) {
      Value* slot = gep(coroArg_slot, 0, i);
      builder.CreateStore(inputArgs[i], slot);
    }
  }

  // Set the status fields of both coros.
  Value* sibling_slot = gep(coro, 0, coroField_Sibling(), "siblingaddr");
  Value* sibling_ptr_gen = builder.CreateLoad(sibling_slot);

  Value* sib_status_addr = gep(sibling_ptr_gen, 0, coroField_Status(), "sibstatusaddr");

  // TODO once we have multiple threads, this will need to
  // be done atomically or under a lock (and error handling added).
  if (isYield) {
    builder.CreateStore(builder.getInt32(FOSTER_CORO_INVALID), status_addr);
    builder.CreateStore(builder.getInt32(FOSTER_CORO_DORMANT), sib_status_addr);
  } else {
    builder.CreateStore(builder.getInt32(FOSTER_CORO_RUNNING), status_addr);
    builder.CreateStore(builder.getInt32(FOSTER_CORO_SUSPENDED), sib_status_addr);
  }

  // If we're invoking, "push" the coro on the coro "stack".
  if (!isYield) {
    ///   coro->invoker = current_coro;
    Value* invoker_slot = gep(coro, 0, coroField_Invoker());
    createStore(current_coro, invoker_slot);

    ///   current_coro = coro;
    createStore(coro, current_coro_slot);
  }

  Value* coroTransfer = pass->mod->getFunction(kCoroTransfer);
  ASSERT(coroTransfer != NULL);
  Value*     ctx_addr = gep(coro,            0, coroField_Context());
  Value* sib_ctx_addr = gep(sibling_ptr_gen, 0, coroField_Context());

  llvm::Type* coro_context_ptr_ty = coroTransfer->getType()->getContainedType(0)->getContainedType(1);
  llvm::CallInst* transfer = builder.CreateCall(coroTransfer, {
                                builder.CreateBitCast(sib_ctx_addr, coro_context_ptr_ty),
                                builder.CreateBitCast(ctx_addr, coro_context_ptr_ty) });
  transfer->addAttribute(1, llvm::Attribute::InReg);
  transfer->addAttribute(2, llvm::Attribute::InReg);

  //=================================================================
  //=================================================================

  // A GC may have been triggered, so re-load locals from the stack.
  coro = builder.CreateLoad(coro_slot);
  status_addr = gep(coro, 0, coroField_Status(), "statusaddr");
  sibling_slot = gep(coro, 0, coroField_Sibling(), "siblingaddr");
  sibling_ptr_gen = builder.CreateLoad(sibling_slot);

  sib_status_addr = gep(sibling_ptr_gen, 0, coroField_Status(), "sibstatusaddr");

  if (!isYield) { // likewise, pop the "stack" when we return from
    ///   current_coro = coro->invoker;
    Value* invoker_slot = gep(coro, 0, coroField_Invoker());
    Value* invoker      = builder.CreateLoad(invoker_slot);
    createStore(invoker, current_coro_slot);
  }

  // So if we were originally yielding, then we are
  // now being re-invoked, possibly by a different
  // coro and/or a different thread!
  // But our sibling coro remains the same, it's just the
  // stack that it refers to that might have changed.
  if (isYield) {
    builder.CreateStore(builder.getInt32(FOSTER_CORO_SUSPENDED), status_addr);
    builder.CreateStore(builder.getInt32(FOSTER_CORO_RUNNING), sib_status_addr);
  } else {
    builder.CreateStore(builder.getInt32(FOSTER_CORO_DORMANT), status_addr);
    builder.CreateStore(builder.getInt32(FOSTER_CORO_INVALID), sib_status_addr);
  }

  sibling_slot = gep(coro, 0, coroField_Sibling(), "siblingaddr");
  sibling_ptr_gen      = builder.CreateLoad(sibling_slot);
  Value* sibling_ptr   = builder.CreateBitCast(sibling_ptr_gen,
                                         ptrTo(getSplitCoroType(
                                               (isYield ? argTypes : retTy))));
  /// return sibling->arg;
  Value* sibling_arg_slot = gep(sibling_ptr, 0, 1, "sibling_arg_slot");
  Value* sibling_arg      = builder.CreateLoad(sibling_arg_slot);

  builder.CreateRet(sibling_arg);
}

////////////////////////////////////////////////////////////////////
////////////////////////// CORO INVOKE  ////////////////////////////
////////////////////////////////////////////////////////////////////

Value* CodegenPass::emitCoroInvokeFn(llvm::Type* retTy,
                                     llvm::Type* argTypes) {
  // Create a function of type  retTy (cloty*)
  Function*& fn = this->lazyCoroPrimInfo[
      std::make_pair(std::make_pair(false, retTy), argTypes)];
  if (!fn) {
    std::string ss_str;
    llvm::raw_string_ostream ss(ss_str);
    ss << ".foster_coro_invoke_" << str(retTy) << "__" << str(argTypes);

    std::string functionName = ss.str();

    fn = Function::Create(
      /*Type=*/    getCoroInvokeFnTy(retTy, argTypes),
      /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
      /*Name=*/    functionName, this->mod);

    fn->setCallingConv(llvm::CallingConv::Fast);
    fn->setGC("fostergc");

    // TODO when using inlining along with any codegen opt level greater
    //      than None, the basic-coro test segfaults after returning from
    //      coro_transfer or when using std::map to lookup stackmap entries.
    //      why?!?  :(
    fn->addFnAttr(llvm::Attribute::NoInline);
  }

  return fn;
}

////////////////////////////////////////////////////////////////////
////////////////////////// CORO YIELD //////////////////////////////
////////////////////////////////////////////////////////////////////

// Return a function with type   argTypes (retTy1...retTyN)
// Note that "retTypes" denote the arguments, and "argTypes"
// the (possibly structure-typed) result. The reason is that
// the parameter names match create/invoke for consistency,
// and yield does things the other way 'round.
Value* CodegenPass::emitCoroYieldFn(llvm::Type* retTy,
                                    llvm::Type* argTypes) {
  Function*& fn = this->lazyCoroPrimInfo[
      std::make_pair(std::make_pair(true, retTy), argTypes)];
  if (!fn) {
    std::string ss_str;
    llvm::raw_string_ostream ss(ss_str);
    ss << ".foster_coro_yield_" << str(retTy) << "__" << str(argTypes);

    std::string functionName = ss.str();

    fn = Function::Create(
      /*Type=*/    getCoroYieldFnTy(retTy, argTypes),
      /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
      /*Name=*/    functionName, this->mod);

    fn->setCallingConv(llvm::CallingConv::Fast);
    fn->setGC("fostergc");
  }

  return fn;
}


////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

Value* getCurrentCoroSibling(llvm::Module* mod) {
  // The current_coro global only exists after we link in libfoster_coro.
  Value* current_coro_slot = codegenCurrentCoroSlot(mod);
  ASSERT(current_coro_slot != NULL);

  Value* current_coro = builder.CreateLoad(current_coro_slot, "coro");

  // Ensure that we actually have a coroutine!
  emitFosterAssert(mod, builder.CreateIsNotNull(current_coro),
                  "Cannot call yield before invoking a coroutine!");

  Value* sibling_slot = gep(current_coro,
                                    0, coroField_Sibling(), "siblingaddr");
  return builder.CreateLoad(sibling_slot);
}

// We get two benefits by lazily generating coro primitive functions:
//  1) Only one instantition per type/type pair, rather than
//     one instantiation per call site.
//  2) It removes one dependency between codegen and linking with
//     libfoster_coro, which is a prerequisite for emitting LLVM
//     from the middle-end.
void CodegenPass::emitLazyCoroPrimInfo(bool isYield, Function* fn,
                             llvm::Type* retTy, llvm::Type* argTys) {
  std::vector<Value*> inputArgs;
  Function::arg_iterator args = fn->arg_begin();

  BasicBlock* prevBB = builder.GetInsertBlock();
  this->addEntryBB(fn);

  Value* coro = NULL;
  // When invoking, the coro to transfer to is available as the first arg;
  // when yielding, we yield to the sibling of the current thread's coro.
  if (isYield) {
    while (args != fn->arg_end()) {
      inputArgs.push_back(args++);
    }
    coro = getCurrentCoroSibling(this->mod);
  } else {
    Value* concrete_invoked_coro = args++;
    while (args != fn->arg_end()) {
      inputArgs.push_back(args++);
    }
    coro = builder.CreateBitCast(concrete_invoked_coro,
                                 ptrTo(foster_generic_coro_t));
  }

  generateInvokeYield(isYield, this, coro, retTy, argTys, inputArgs);

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }
}
