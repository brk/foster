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
#include "parse/DumpStructure.h"

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

llvm::Value* emitStore(llvm::Value* val,
                       llvm::Value* ptr) {
  if (val->getType()->isVoidTy()) {
    // Can't store a void!
    return getUnitValue();
  }
  ASSERT(isPointerToType(ptr->getType(), val->getType())) << "\n"
  << "ptr type: " << str(ptr->getType()) << "\n"
  << "val type: " << str(val->getType()) << "\n"
  << "val is  : " << str(val) << "\n"
  << "ptr is  : " << str(ptr);

  return builder.CreateStore(val, ptr, /*isVolatile=*/ false);
}

// emit() serves as a wrapper around codegen()
// which inserts implicit loads as needed, and also
// verifies that the expected type matches the generated type.
// In most cases, emit() should be used instead of codegen().
llvm::Value* CodegenPass::emit(LLExpr* e, TypeAST* expectedType) {
  llvm::Value* v = e->codegen(this);

  if (this->needsImplicitLoad.count(v) == 1) {
    v = builder.CreateLoad(v, /*isVolatile=*/ false,
                           v->getName() + ".autoload");
  }

  if (expectedType) {
    const llvm::Type* ty = getLLVMType(expectedType);
    if (v->getType() != ty) {
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
    pass->valueSymTab.insert(f->getName(), f->codegenProto(pass));
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegenProc(pass);
  }
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

llvm::Function* generateAllocDAarray32(CodegenPass* pass) {
  // Create a function of type  array[i32] (i32 n)
  std::vector<const Type*> fnTyArgs;
  fnTyArgs.push_back(builder.getInt32Ty());

  const llvm::Type* elt_ty = builder.getInt32Ty();
  const llvm::FunctionType* fnty =
        llvm::FunctionType::get(
                   /*Result=*/   ArrayTypeAST::getZeroLengthTypeRef(elt_ty),
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);

  Function* f = Function::Create(
    /*Type=*/    fnty,
    /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
    /*Name=*/    ".foster_alloc_array_32", pass->mod);

  f->setGC("fostergc");

  /////////////////////////////

  Function::arg_iterator args = f->arg_begin();
  Value* n = args++;
  n->setName("n");

  BasicBlock* prevBB = builder.GetInsertBlock();
  pass->addEntryBB(f);

  Value* slot = pass->emitArrayMalloc(elt_ty, n);
  builder.CreateRet(builder.CreateLoad(slot, /*isVolatile=*/ false));

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return f;
}

llvm::Function* CodegenPass::lookupFunctionOrDie(const std::string& fullyQualifiedSymbol) {
  // Otherwise, it should be a function name.
  llvm::Function* f = mod->getFunction(fullyQualifiedSymbol);

  if (!f && fullyQualifiedSymbol == "allocDArray32") {
    f = generateAllocDAarray32(this);
  }

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
  if (this->type->getLLVMType()->isIntegerTy()) {
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

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  // The variable for an environment can be looked up multiple times...
  llvm::Value* v = pass->valueSymTab.lookup(getName());
  if (!v) v = pass->lookupFunctionOrDie(getName());
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

llvm::Value* LLAllocate::codegen(CodegenPass* pass) {
  const llvm::Type* ty = NULL;
  if (TupleTypeAST* tuplety = dynamic_cast<TupleTypeAST*>(this->type)) {
    ty = tuplety->getLLVMTypeUnboxed();
  } else {
    ty = this->type->getLLVMType();
  }

  switch (this->region) {
  case MEM_REGION_STACK:
    return CreateEntryAlloca(ty, "alloc");

  case MEM_REGION_GLOBAL_HEAP:
    return pass->emitMalloc(ty);

  default:
    ASSERT(false); return NULL;
  }
}

llvm::Value* LLAlloc::codegen(CodegenPass* pass) {
  // (alloc base) is equivalent to
  //    let sv = base;
  //        rs  = mallocType t;
  //        r   = rs^;
  //     in sv >^ r;
  //        r
  //    end
  ASSERT(this && this->baseVar && this->baseVar->type);
  llvm::Value* storedVal = pass->emit(baseVar, NULL);
  llvm::Value* ptrSlot   = pass->emitMalloc(this->baseVar->type->getLLVMType());
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

  ASSERT(closures.size() == 1)
       << "EXPEDIENT HACK: MUTUALLY RECURSIVE CLOSURE CODEGEN"
                << " NOT YET IMPLEMENTED!";

  LLClosure& c = *closures[0];

  llvm::Value* clo = c.codegen(pass);

  pass->valueSymTab.insert(c.varname, clo);

  llvm::Value* exp = pass->emit(expr, NULL);

  for (size_t i = 0; i < closures.size(); ++i) {
     pass->valueSymTab.remove(closures[i]->varname);
  }

  return exp;
}

bool tryBindClosureFunctionTypes(const llvm::Type*          origType,
                                 const llvm::FunctionType*& fnType,
                                 const llvm::StructType*  & envStructTy,
                                 const llvm::StructType*  & cloStructTy) {
  fnType = NULL; envStructTy = NULL; cloStructTy = NULL;

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
  envStructTy = llvm::dyn_cast<llvm::StructType>(
                          maybeEnvType->getContainedType(0));
  if (!envStructTy) {
    EDiag() << "expected " << str(fnType) << " to have a concrete struct env parameter.";
    return false;
  }

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

llvm::Value* LLClosure::codegen(CodegenPass* pass) {
  llvm::Value* proc = pass->lookupFunctionOrDie(procname);
  const llvm::FunctionType* fnty;
  const llvm::StructType* envStructTy;
  const llvm::StructType* cloStructTy;

  if (!tryBindClosureFunctionTypes(proc->getType(),
            fnty, envStructTy, cloStructTy)) {
    ASSERT(false) << "proc " << procname
                  << " with type " << str(proc->getType())
                  << " not closed??";
  }

  // { code*, env* }*
  llvm::AllocaInst* clo = CreateEntryAlloca(cloStructTy, varname + ".closure");

  //llvm::AllocaInst* clo_slot = pass->emitMalloc(cloStructTy);
  //llvm::Value* clo = builder.CreateLoad(clo_slot, /*isVolatile=*/ false,
  //                                      varname + ".closure");
  // TODO explicitly allocate with separate AST nodes
  // TODO register closure type


  // (code*)*
  Value* clo_code_slot = builder.CreateConstGEP2_32(clo, 0, 0, varname + ".clo_code");
  emitStore(proc, clo_code_slot);

  // (env*)*
  Value* clo_env_slot = builder.CreateConstGEP2_32(clo, 0, 1, varname + ".clo_env");


  if (env->vars.empty()) {
    storeNullPointerToSlot(clo_env_slot);
  } else {
    std::vector<llvm::Value*> values;

    // Ensure that the environment contains space for the type map.
    llvm::Value* envValue = pass->emit(env, NULL);
    //if (isPointerToPointer(envValue->getType())) {
    //  envValue = builder.CreateLoad(envValue, /*isVolatile=*/ false, "env_ptr");
    //}

    #if 0 // this is broken atm...
      // Store the typemap in the environment's typemap slot.
      llvm::GlobalVariable* clo_env_typemap
          = getTypeMapForType(envStructTy, pass->mod);

      Value* clo_env_typemap_slot =
            builder.CreateConstGEP2_32(envValue, 0, 0,
                                       varname + ".clo_env_typemap_slot");
      llvm::outs() << "clo_env_typemap :: " << clo_env_typemap <<"\n";
      llvm::outs() << "clo_env_typemap :: " << str(clo_env_typemap->getType()) <<"\n";
      llvm::outs() << "clo_env_typemap_slot : " << str(clo_env_typemap_slot->getType()) <<"\n";
      llvm::outs() << "clo_env_typemap_slot*: " << str(clo_env_typemap_slot->getType()->getContainedType(0)) <<"\n";

      Value* clo_env_typemap_cast =
          ConstantExpr::getBitCast(clo_env_typemap,
                                   clo_env_typemap_slot->getType()->getContainedType(0));

      emitStore(clo_env_typemap_cast, clo_env_typemap_slot);
    #endif

    // Only store the env in the closure if the env contains entries.
    emitStore(envValue, clo_env_slot);
  }

  const llvm::StructType* genStructTy = genericClosureStructTy(fnty);
  return builder.CreateBitCast(clo, ptrTo(genStructTy), varname + ".hideCloTy");
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

llvm::AllocaInst* newImplicitStackSlot(llvm::Value* v, CodegenPass* pass) {
  if (mightContainHeapPointers(v->getType())) {
    return pass->storeAndMarkPointerAsGCRoot(v, NotArray);
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
      llvm::Value* slot = newImplicitStackSlot(AI, pass);
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
  ASSERT(false); return NULL;
}

llvm::Value* LLCase::codegen(CodegenPass* pass) {
  llvm::Value* v = pass->emit(scrutinee, NULL);
  llvm::AllocaInst* rv_slot = CreateEntryAlloca(getLLVMType(this->type), "case_slot");
  pass->markAsNeedingImplicitLoads(rv_slot);
  this->dt->codegenDecisionTree(pass, v, rv_slot);
  return rv_slot;
}

llvm::Value* lookupOccs(Occurrence* occ, llvm::Value* v) {
  const std::vector<int>& occs = occ->offsets;
  llvm::Value* rv = v;
  for (size_t i = 0; i < occs.size(); ++i) {
    rv = getElementFromComposite(rv,
             getConstantInt32For(occs[i]), "switch_insp");
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
       Value* v = lookupOccs(binds[i].second, scrutinee);
       trySetName(v, "pat_" + binds[i].first);
       pass->valueSymTab.insert(binds[i].first, v);
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

  // Fetch the subterm of the scrutinee being inspected.
  llvm::Value* v = lookupOccs(occ, scrutinee);

  // TODO: switching on a.p. integers: possible at all?
  // If so, it will require manual if-else chaining,
  // not a simple int32 switch...

  BasicBlock* bbEnd = BasicBlock::Create(getGlobalContext(), "case_end");
  BasicBlock* defOrContBB = defaultBB ? defaultBB : bbEnd;
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
  return newImplicitStackSlot(val, pass);
}

llvm::Value* LLArrayPoke::codegen(CodegenPass* pass) {
  Value* val  = pass->emit(this->value, NULL);
  Value* base = pass->emit(this->base , NULL);
  Value* idx  = pass->emit(this->index, NULL);
  Value* slot = getArraySlot(base, idx, pass);
  return builder.CreateStore(val, slot, /*isVolatile=*/ false);
}

////////////////////////////////////////////////////////////////////

LLProc* getClosureVersionOf(LLExpr* arg,
                            const llvm::Type* expectedType,
                            FnTypeAST* fnty,
                            CodegenPass* pass);

bool
isKnownNonAllocating(LLVar* varast) {
  // silly hack for now...
  if (pystring::startswith(varast->getName(), "expect_")) return true;
  if (pystring::startswith(varast->getName(), "print_")) return true;
  return false;
}

////////////////////////////////////////////////////////////////////

void doLowLevelWrapperFnCoercions(const llvm::Type* expectedType,
                                  LLExpr*& arg,
                                  CodegenPass* pass) {
  FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(arg->type);
  if (!fnty) return;

  // FnTypeAST could mean a closure or a raw function...
  const llvm::FunctionType* llvmFnTy = getLLVMFunctionType(fnty);

  // Codegenning   callee( arg )  where arg has raw function type, not closure type!
  if (!llvmFnTy) return;

  // If we still have a bare function type at codegen time, it means
  // the code specified a (top-level) procedure name.
  // Since we made it past type checking, we should have only two
  // possibilities for what kind of function is doing the invoking:
  //
  // 1) A C-linkage function which expects a bare function pointer.
  // 2) A Foster function which expects a closure value.

  bool argExpectedFunctionPointer
          = expectedType->isPointerTy()
         && expectedType->getContainedType(0)->isFunctionTy();
  if (argExpectedFunctionPointer) {
    ASSERT(llvmFnTy == expectedType)
        << "calling a function that expects a bare pointer arg:\n\t"
        << str(expectedType) << " -VS- " << str(llvmFnTy);
    // Do we want to codegen to handle automatic insertion
    // of type-coercion wrappers? For now, we'll require
    // strict type compatibility.
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
    LLProc* wrapper = getClosureVersionOf(arg, expectedType, fnty, pass);
    std::string cloname = ParsingContext::freshName("c-clo");
    std::vector<LLClosure*> closures;
    closures.push_back(new LLClosure(cloname, wrapper->getName(), getEmptyTuple()));
    LLExpr* clo = new LLClosures(new LLVar(cloname), closures);
    arg = clo;
  }
}

////////////////////////////////////////////////////////////////////

// TODO this shouldn't need to be 200 lines :(
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

    LLExpr* arg = this->args[i];
    doLowLevelWrapperFnCoercions(expectedType, arg, pass);
    llvm::Value* argV = pass->emit(arg, NULL);
    valArgs.push_back(argV);

    ASSERT(argV->getType() == expectedType)
              << "type mismatch, " << str(argV->getType())
              << " vs expected type " << str(expectedType)
              << "\nbase is " << str(FV)
              << "\nwith base type " << str(FV->getType());
  }

  ASSERT(FT->getNumParams() == valArgs.size())
            << "function arity mismatch for " << base->getName()
            << "; got " << valArgs.size()
            << " args but expected " << FT->getNumParams();

  // Give the instruction a name, if we can...
  llvm::CallInst* callInst =
        builder.CreateCall(FV, valArgs.begin(), valArgs.end());
  callInst->setCallingConv(callingConv);
  trySetName(callInst, "calltmp");

  if (callingConv == llvm::CallingConv::Fast) {
    callInst->setTailCall(true);
  }

  if (isKnownNonAllocating(base)) {
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

    return pass->storeAndMarkPointerAsGCRoot(callInst, NotArray);
  } else {
    return callInst;
  }
}

llvm::Value* LLTuple::codegen(CodegenPass* pass) {
  if (vars.empty()) {
    return getUnitValue(); // It's silly to allocate a unit value!
  }

  TupleTypeAST* tuplety = dynamic_cast<TupleTypeAST*>(this->allocator->type);
  ASSERT(tuplety != NULL);

  const llvm::Type* tupleType = tuplety->getLLVMTypeUnboxed();
  const char* typeName = (isClosureEnvironment) ? "env" : "tuple";
  registerType(tupleType, typeName, pass->mod, NotArray, isClosureEnvironment);

  llvm::Value* rv = allocator->codegen(pass);
  // Heap-allocated things codegen to a stack slot, which
  // is the Value we want the tuple to codegen to, but
  // we need temporary access to the pointer stored in the slot.
  // Otherwise, bad things happen.
  llvm::Value* pt = allocator->isStackAllocated()
                        ? rv
                        : builder.CreateLoad(rv, "normalize");

  // Store the values into the point.
  for (size_t i = 0; i < vars.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    Value* val = pass->emit(vars[i], NULL);
    emitStore(val, dst);
  }

  return rv;
}


// Create function    fnName({}* env, arg-args) { arg(arg-args) }
// that hard-codes call to fn referenced by arg,
// and is suitable for embedding as the code ptr in a closure pair,
// unlike the given function, which doesn't want the env ptr.
LLProc* getClosureVersionOf(LLExpr* arg,
                            const llvm::Type* expectedType,
                            FnTypeAST* fnty,
                            CodegenPass* pass) {
  static std::map<string, LLProc*> sClosureVersions;

  LLVar* var = dynamic_cast<LLVar*>(arg);
  ASSERT(var != NULL) << "getClosureVersionOf() must be given a LLVar";

  string fnName = "__closureVersionOf__" + var->name;
  if (LLProc* exists = sClosureVersions[fnName]) {
    return exists;
  }

  std::vector<std::string>   inArgNames;
  std::vector<TypeAST*> inArgTypes;
  std::vector<TypeAST*> envTypes;
  std::vector<LLVar*> callArgs;

  inArgNames.push_back(ParsingContext::freshName("__ignored_env__"));
  inArgTypes.push_back(TupleTypeAST::get(envTypes));

  for (int i = 0; i < fnty->getNumParams(); ++i) {
    LLVar* a = new LLVar(ParsingContext::freshName("_cv_arg"));
    inArgNames.push_back(a->name);
    inArgTypes.push_back(fnty->getParamType(i));
    callArgs.push_back(a);
  }

  // Create a scope for the new function's values.
  CodegenPass::ValueScope* scope = pass->valueSymTab.newScope(fnName);
  // But don't use it for doing codegen outside the proto.
  pass->valueSymTab.popExistingScope(scope);

  FnTypeAST* newfnty = new FnTypeAST(fnty->getReturnType(),
                                     inArgTypes,
                                     fnty->getAnnots());
  newfnty->markAsProc();
  LLExpr* body = new LLCall(var, callArgs);
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
