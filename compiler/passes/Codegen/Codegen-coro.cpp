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
//#include "llvm/Support/Dwarf.h"

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

void addCoroArgs(std::vector<llvm::Type*>& fnTyArgs,
                 llvm::Type* argTypes) {
  llvm::StructType* sty;
  if (isSingleElementStruct(argTypes, sty)) {
    fnTyArgs.push_back(sty->getElementType(0));
  } else {
    fnTyArgs.push_back(argTypes);
  }
}

// in LLCodegen.cpp
Value* getElementFromComposite(CodegenPass* pass, Value* compositeValue, int indexValue, const std::string& msg, bool assumeImmutable);

void addCoroArgs(std::vector<Value*>& fnArgs,
                 llvm::Value* argVals) {
  llvm::StructType* sty;
  if (isSingleElementStruct(argVals->getType(), sty)) {
    fnArgs.push_back(getElementFromComposite(nullptr, argVals, 0, "coroarg", false));
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

// Returns retTy(i8* env)
llvm::FunctionType* getCoroClosureFnType(
  llvm::Type* retTy,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> args;
  args.push_back(builder.getInt8PtrTy());
  //addCoroArgs(args, argTypes);
  return FunctionType::get(retTy, args, /*isVarArg=*/ false);
}

// Returns retTy ( {specific coro}*, .. args ..)
llvm::FunctionType* getCoroInvokeFnTy(
  llvm::Type* retTy,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> fnTyArgs;
  fnTyArgs.push_back(getHeapPtrTo(getSplitCoroType(argTypes)));
  fnTyArgs.push_back(builder.getInt64Ty());
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
  fnTyArgs.push_back(getHeapPtrTo(foster_generic_coro_t));
  //fnTyArgs.push_back(builder.getInt64Ty());
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
  parts.push_back(rawPtrTo(getCoroClosureFnType(retTy, argTypes)));
  parts.push_back(builder.getInt8PtrTy());
  return llvm::StructType::get(builder.getContext(), parts, /*isPacked=*/ false);
}

// Returns { specific coro }* (closure struct*)
llvm::FunctionType* getCoroCreateFnTy(
  llvm::Type* retTy,
  llvm::Type* argTypes)
{
  std::vector<llvm::Type*> fnTyArgs;
  fnTyArgs.push_back(getHeapPtrTo(getCoroClosureStructTy(retTy, argTypes)));
  return llvm::FunctionType::get(
                   /*Result=*/   getHeapPtrTo(getSplitCoroType(argTypes)),
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
int coroField_Fn()           { return 1; }
int coroField_Env()          { return 2; }
int coroField_Invoker()      { return 3; }
int coroField_IndirectSelf() { return 4; }
int coroField_EffectTag()    { return 5; }
int coroField_Status()       { return 6; }

////////////////////////////////////////////////////////////////////

void registerCoroType(llvm::Module* mod, llvm::Type* argTypes) {
  std::string ss_str;
  llvm::raw_string_ostream ss(ss_str);
  ss << "coro_" << str(argTypes);
  EDiag() << "Need to register type name: " << ss.str();
  //mod->addTypeName(ss.str(), ptrTo(getSplitCoroType(argTypes)));
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
  // TODO raw or heap ptr?
  return builder.CreateStore(val, builder.CreateBitCast(ptr, rawPtrTo(val->getType())));
}

Value* generateInvokeYield(bool isYield,
                         int yield_dormant_or_dead,
                         CodegenPass* pass,
                         llvm::Value* coro,
                         llvm::Value* tag, // null for yields and implicit invocations.
                         llvm::Type* retTy,
                         llvm::Type* argTypes,
                         const std::vector<llvm::Value*>& inputArgs) {
  llvm::Value* coro_slot = pass->storeAndMarkPointerAsGCRoot(coro);

  Value* current_coro_slot = codegenCurrentCoroSlot(pass->mod);
  Value* current_coro = builder.CreateLoad(current_coro_slot);

  /// TODO: call coro_dump(coro)

  Value* status_addr = gep(coro, 0, coroField_Status(), "statusaddr");
  Value* status = builder.CreateLoad(status_addr);

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

/*
  auto prf = pass->mod->getFunction("foster_printf_pi");
  ASSERT(prf) << "couldn't find foster_printf_pi?!?";
    builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString("invoke/yield: current_coro is %p , status is %d\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(current_coro, builder.getInt8PtrTy())
                     , status });

    builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString("invoke/yield:         coro is %p , expst is %d\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(coro,   builder.getInt8PtrTy())
                     , expectedStatus });
  */

  Value* cond = builder.CreateICmpEQ(status, expectedStatus);
  //emitFosterAssert(pass->mod, cond, expectedStatusMsg);

  Value* target_coro_pretransfer = coro;

/*
  auto prf = pass->mod->getFunction("foster_printf_2p");
  ASSERT(prf) << "couldn't find foster_printf_2p?!?";
  if (isYield) {
    builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString("pre-transfer(Y); current_coro is %p <<<, coro is %p\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(current_coro, builder.getInt8PtrTy())
                     , builder.CreateBitCast(coro,         builder.getInt8PtrTy()) });

  } else {
    builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString("pre-transfer(I); current_coro is %p, coro is %p <<<\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(current_coro, builder.getInt8PtrTy())
                     , builder.CreateBitCast(coro,         builder.getInt8PtrTy()) });

  }
  */

  if (tag) {
    builder.CreateStore(tag, gep(current_coro, 0, coroField_EffectTag(), "tag_addr"));
  }

  // Store the input arguments to target_coro->arg.
  llvm::outs() << "inputArgs.size() is " << inputArgs.size() << "\n";

  Value* concrete_coro = builder.CreateBitCast(target_coro_pretransfer,
                                         getHeapPtrTo(getSplitCoroType(
                                              (isYield ? retTy : argTypes))));
  Value* coroArg_slot = gep(concrete_coro, 0, 1);

/*
      builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString("invoke/yield:  writing args to target coro %p , dir is %d\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(concrete_coro,   builder.getInt8PtrTy())
                     , builder.getInt32( isYield ? 321 : 123 ) });
*/

  if (inputArgs.size() == 1) {
    builder.CreateStore(inputArgs[0], coroArg_slot);
  } else {
    /*
    llvm::errs() << "concrete coro: " << *concrete_coro << "\n";
    llvm::errs() << "coroArg_slot: " << *coroArg_slot << "\n";
    llvm::errs() << "coroArg_slot type: " << *(coroArg_slot->getType()) << "\n";
    llvm::errs() << "inputArgs.size(): " << inputArgs.size() << "\n";  
    */
    for (size_t i = 0; i < inputArgs.size(); ++i) {
      Value* slot = gep(coroArg_slot, 0, i);
      builder.CreateStore(inputArgs[i], slot);
    }
  }

  
  // Set the status fields of both coros.
  Value* curr_status_addr = gep(current_coro, 0, coroField_Status(), "status_addr");

  // TODO once we have multiple threads, this will need to
  // be done atomically or under a lock (and error handling added).
  if (isYield) {
    // The coro we yield from becomes dormant; the one yielded to running.
    builder.CreateStore(builder.getInt32(FOSTER_CORO_RUNNING),        status_addr);
    builder.CreateStore(builder.getInt32(yield_dormant_or_dead), curr_status_addr);
  } else {
    // The coro we invoke starts running; the one we left becomes suspended.
    builder.CreateStore(builder.getInt32(FOSTER_CORO_RUNNING),        status_addr);
    builder.CreateStore(builder.getInt32(FOSTER_CORO_SUSPENDED), curr_status_addr);
  }

  // Record our parent when doing invocations.
  if (!isYield) {
    ///  coro->invoker = current_coro;
    createStore(current_coro, gep(coro, 0, coroField_Invoker()));
  }

  ///   current_coro = coro;
  createStore(coro, current_coro_slot);

  Value* coroTransfer = pass->mod->getFunction(kCoroTransfer);
  ASSERT(coroTransfer != NULL);
  Value*      ctx_addr = gep(coro,         0, coroField_Context());
  Value* curr_ctx_addr = gep(current_coro, 0, coroField_Context());

  llvm::Type* coro_context_ptr_ty = coroTransfer->getType()->getContainedType(0)->getContainedType(1);
  llvm::CallInst* transfer = builder.CreateCall(coroTransfer, {
                                builder.CreateBitCast(curr_ctx_addr, coro_context_ptr_ty),
                                builder.CreateBitCast(     ctx_addr, coro_context_ptr_ty) });
  transfer->addAttribute(1, llvm::Attribute::InReg);
  transfer->addAttribute(2, llvm::Attribute::InReg);

  //=================================================================
  //=================================================================

  // A GC may have been triggered, so re-load locals from the stack.
  coro = builder.CreateLoad(coro_slot);
  current_coro = builder.CreateLoad(current_coro_slot);

  // So if we were originally yielding, then we are
  // now being re-invoked, possibly by a different
  // coro and/or a different thread!

/*
  auto prf2 = pass->mod->getFunction("foster_printf_2p");
  builder.CreateCall(prf2,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString(isYield ? "post-transfer(Y) current %p <<<, coro is %p\n"
                                                           : "post-transfer(I) current %p, coro is %p <<<\n"),
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(current_coro, builder.getInt8PtrTy())
                     , builder.CreateBitCast(coro,         builder.getInt8PtrTy()) });
*/

  auto target_coro_posttransfer = current_coro;
  Value* casted_ptr = builder.CreateBitCast(target_coro_posttransfer,
                                         getHeapPtrTo(getSplitCoroType(
                                               (isYield ? argTypes : retTy))));
  /// return coro->arg;
  Value* casted_arg      = builder.CreateLoad(gep(casted_ptr, 0, 1, "casted_arg_slot"));

  return casted_arg;
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
    this->markFosterFunction(fn);

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
    this->markFosterFunction(fn);
  }

  return fn;
}

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
  pass->markFosterFunction(wrapper);

  /////////////////////////////

  Function::arg_iterator args = wrapper->arg_begin();
  Value* ptr_f_c = &*(args++);
  ptr_f_c->setName("f_c");

  BasicBlock* prevBB = builder.GetInsertBlock();
  pass->addEntryBB(wrapper);

  Value* fc  = builder.CreateBitCast(ptr_f_c, getHeapPtrTo(getSplitCoroType(argTypes)));
  Value* fcg = gep(fc, 0, 0, "fc_gen");

  llvm::Value* coro_slot = pass->storeAndMarkPointerAsGCRoot(fcg);

  Value* fn_addr = gep(fcg, 0, coroField_Fn(), "fnaddr");
  Value* fn_gen  = builder.CreateLoad(fn_addr, "fn_gen");
  Value* fn      = builder.CreateBitCast(fn_gen,
                                      rawPtrTo(getCoroClosureFnType(retTy, argTypes)));

  // We don't initialize the parent field with the current coro
  // because it should reflect the context of its invoker,
  // which might be different than its creator.

  Value* env_addr = gep(fcg, 0, coroField_Env(), "envaddr");
  Value* env      = builder.CreateLoad(env_addr, "env_ptr");

  Value* arg_addr = gep(fc, 0, 1, "argaddr");
  Value* arg      = builder.CreateLoad(arg_addr, "arg");

  std::vector<Value*> callArgs;
  callArgs.push_back(env);
  //addCoroArgs(callArgs, arg);

/*
  auto prf = pass->mod->getFunction("foster_printf_2p");
  ASSERT(prf) << "couldn't find foster_printf_2p?!?";
  builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString("wrapper call; coro_slot is %p, coro is %p\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(coro_slot, builder.getInt8PtrTy())
                     , builder.CreateBitCast(fcg,       builder.getInt8PtrTy()) });
*/

  llvm::CallInst* call  = builder.CreateCall(fn, llvm::makeArrayRef(callArgs));
  call->setCallingConv(llvm::CallingConv::Fast);

    llvm::outs() << "Coro call is " << str(call) << "\n";

  std::vector<Value*> inputArgs;
  inputArgs.push_back(call);
  bool isYield = true;

  fcg = builder.CreateLoad(coro_slot);
  auto parent = builder.CreateLoad(gep(fcg, 0, coroField_Invoker()), "parent_final");
  // Returned value is never used because corresponds to the arg passed
  // by invoking the now-dead coroutine.
  
  /*
  builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString("wrapper yield; coro is %p, parent is %p\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(fcg,    builder.getInt8PtrTy())
                     , builder.CreateBitCast(parent, builder.getInt8PtrTy()) });
  */

  generateInvokeYield(isYield, FOSTER_CORO_DEAD,
                      pass, parent, nullptr, retTy, argTypes, inputArgs);

  // TODO add assertion that control flow does not reach here

  builder.CreateRetVoid();

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return wrapper;
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
  this->markFosterFunction(create);

  registerCoroType(this->mod, argTypes);
  registerCoroType(this->mod, retTy);

  Function::arg_iterator args = create->arg_begin();
  Value* pclo = &*(args++);
  pclo->setName("pclo");

  BasicBlock* prevBB = builder.GetInsertBlock();
  this->addEntryBB(create);

  CtorRepr bogusCtor; bogusCtor.smallId = -1;
  // foster_coro_i32_i32* fcoro = (foster_coro_i32_i32*) memalloc_cell(NULL);
  Value* fcoro      =                                   this->emitMalloc(getSplitCoroTyp(argTyps), bogusCtor, "fcoro", /*init*/ true);

  // TODO call memset on the full structs

  Value* gfcoro = gep(fcoro, 0, 0, "gfcoro");

  // fcoro->g.fn = reinterpret_cast<coro_func>(pclo->code);
  Value* fcoro_fn = gep(gfcoro, 0, coroField_Fn(), "fcoro_fn");
  Value* clo_code_ptr = gep(pclo, 0, 0, "clo_fn_slot");
  Value* clo_code     = builder.CreateLoad(clo_code_ptr, "clo_fn");
  Value* clo_code_gen = builder.CreateBitCast(clo_code, fcoro_fn->getType()->getContainedType(0));
  builder.CreateStore(clo_code_gen, fcoro_fn);

  // fcoro->g.env = pclo->env;
  Value* fcoro_env = gep(gfcoro, 0, coroField_Env(), "fcoro_env");
  Value* clo_env_ptr = gep(pclo, 0, 1, "clo_env_slot");
  Value* clo_env     = builder.CreateLoad(clo_env_ptr, "clo_env");
  Value* clo_env_gen = builder.CreateBitCast(clo_env, fcoro_env->getType()->getContainedType(0));
  builder.CreateStore(clo_env_gen, fcoro_env);

  // fcoro->g.parent = NULL;
  Value* fcoro_parent = gep(gfcoro, 0, coroField_Invoker(), "fcoro_parent");
  storeNullPointerToSlot(fcoro_parent);

  // fcoro->g.indirect_self = NULL;
  Value* fcoro_indirect_self = gep(gfcoro, 0, coroField_IndirectSelf(), "fcoro_self");
  storeNullPointerToSlot(fcoro_indirect_self);

  Value* fcoro_tag = gep(gfcoro, 0, coroField_EffectTag(), "fcoro_tag");
  builder.CreateStore(builder.getInt64(0), fcoro_tag);

  Value* fcoro_status = gep(gfcoro, 0, coroField_Status(), "fcoro_status");
  llvm::errs() << "gccoro type: " << *(gfcoro->getType()) << "\n";
  llvm::errs() << "status slot type: " << *(fcoro_status->getType()) << "\n";
  builder.CreateStore(builder.getInt32(FOSTER_CORO_DORMANT), fcoro_status);

  /*
  auto prf = this->mod->getFunction("foster_printf_pi");
  ASSERT(prf) << "couldn't find foster_printf_pi?!?";
    builder.CreateCall(prf,
                     { builder.CreateBitCast(
                        builder.CreateGlobalString(".coro_create: newly allocated coro is %p , status is %d\n") ,
                        builder.getInt8PtrTy())
                     , builder.CreateBitCast(fcoro, builder.getInt8PtrTy())
                     , builder.getInt32(0) });
  */

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
                                    getHeapPtrTo(getSplitCoroType(argTypes))));

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return create;
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

Value* CodegenPass::getCurrentCoroParent() {
  // The current_coro global only exists after we link in libfoster_coro.
  Value* current_coro_slot = codegenCurrentCoroSlot(mod);
  ASSERT(current_coro_slot != NULL);

  Value* current_coro = builder.CreateLoad(current_coro_slot, "coro");

  // Ensure that we actually have a coroutine!
  emitFosterAssert(mod, builder.CreateIsNotNull(current_coro),
                  "Attempted to the a non-existent parent coroutine!");

  return builder.CreateLoad(gep(current_coro,
                                    0, coroField_Invoker(), "parentaddr"));
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

  Value* concrete_invoked_coro = &*(args++);
  Value* tag = isYield ? nullptr : &*(args++);

  while (args != fn->arg_end()) {
    inputArgs.push_back(&*(args++));
  }
  Value* coro = builder.CreateBitCast(concrete_invoked_coro,
                                getHeapPtrTo(foster_generic_coro_t));

  llvm::errs() << "(G3)\n";
  llvm::errs() << "retTy: " << *retTy << "\n";
  llvm::errs() << "argTys: " << *argTys << "\n";
  llvm::errs() << "isYield: " << isYield << "\n";
  llvm::errs() << "# args: " << inputArgs.size() << "\n";
  for (auto& arg : inputArgs) {
    llvm::errs() << "   " << *arg << "\n";
  }
  
  builder.CreateRet(generateInvokeYield(isYield, FOSTER_CORO_DORMANT,
                      this, coro, tag, retTy, argTys, inputArgs));

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }
}
