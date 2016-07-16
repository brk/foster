// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "passes/CodegenPass-impl.h"
#include "parse/FosterTypeAST.h"
#include "parse/ParsingContext.h"

#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"

#include <string>

using namespace llvm;

using foster::EDiag;
using foster::builder;

////////////////////////////////////////////////////////////////////

CodegenPass::ValueScope* CodegenPass::newScope(const std::string& scopeName) {
  return valueSymTab.newScope(scopeName);
}

void CodegenPass::insertScopedValue(const std::string& name, llvm::Value* v) {
  valueSymTab.insert(name, v, this->currentProcName);
}

void CodegenPass::popExistingScope(ValueScope* scope) {
  valueSymTab.popExistingScope(scope);
}

////////////////////////////////////////////////////////////////////

Value* signExtend(Value* v, llvm::Type* dst) {
  return v->getType()->isIntegerTy(1)
           ? builder.CreateZExt(v, dst)
           : builder.CreateSExt(v, dst);
}

void emitFosterArrayBoundsCheck(llvm::Module* mod, llvm::Value* idx,
                                                   llvm::Value* len64,
                                                   const std::string& srclines) {
  Value* fosterBoundsCheck = mod->getFunction("foster__boundscheck64");
  ASSERT(fosterBoundsCheck != NULL);

  Value* msg_array = builder.CreateGlobalString(srclines);
  Value* msg = builder.CreateBitCast(msg_array, builder.getInt8PtrTy());
  Value* ext = signExtend(idx, len64->getType());
  llvm::CallInst* call = builder.CreateCall(fosterBoundsCheck, { ext, len64, msg });
  markAsNonAllocating(call);
}

void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr) {
  Value* fosterAssert = mod->getFunction("foster__assert");
  ASSERT(fosterAssert != NULL);

  Value* msg_array = builder.CreateGlobalString(cstr);
  Value* msg = builder.CreateBitCast(msg_array, builder.getInt8PtrTy());
  llvm::CallInst* call = builder.CreateCall(fosterAssert, { cond, msg });
  markAsNonAllocating(call);
}

llvm::Value* getUnitValue() {
  return llvm::ConstantPointerNull::get(
    llvm::dyn_cast<llvm::PointerType>(getUnitType()->getLLVMType()));
}

void checkPointerToIndex(Value* ptrToCompositeValue,
                         Value* idxValue,
                         const std::string& name) {
  ASSERT(ptrToCompositeValue->getType()->isPointerTy());
  llvm::Type* underlyingTy = ptrToCompositeValue->getType()->getContainedType(0);
  if (llvm::CompositeType* cty
      = llvm::dyn_cast<llvm::CompositeType>(underlyingTy)) {
    ASSERT(cty->indexValid(idxValue))
      << "Attempt to use index " << str(idxValue)
      << "\non val of type "     << str(ptrToCompositeValue->getType())
      << "\nwith value "         << str(ptrToCompositeValue);
  } else {
    builder.GetInsertBlock()->getParent()->dump();
    ASSERT(false) << "Pointer to non-composite type "
                  <<  str(ptrToCompositeValue->getType())
                  << "passed to getPointerToIndex(" << str(idxValue)
                                         << " ... " << name << ")";
  }
}

Value* getPointerToIndex(Value* ptrToCompositeValue,
                         Value* idxValue,
                         const std::string& name) {
  checkPointerToIndex(ptrToCompositeValue, idxValue, name);
  std::vector<Value*> idx;
  idx.push_back(builder.getInt32(0));
  idx.push_back(idxValue);
  return builder.CreateGEP(ptrToCompositeValue, llvm::makeArrayRef(idx), name.c_str());
}

Value* getElementFromComposite(Value* compositeValue, int indexValue,
                               const std::string& msg) {
  ASSERT(indexValue >= 0);
  Value* idxValue = builder.getInt32(indexValue);
  Type* compositeType = compositeValue->getType();
  // To get an element from an in-memory object, compute the address of
  // the appropriate struct field and emit a load.
  if (llvm::isa<llvm::PointerType>(compositeType)) {
    Value* gep = getPointerToIndex(compositeValue, idxValue, (msg + ".subgep").c_str());
    return builder.CreateLoad(gep, gep->getName() + "_ld");
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

////////////////////////////////////////////////////////////////////

Constant* getConstantArrayOfString(llvm::StringRef s, bool addNull) {
  return llvm::ConstantDataArray::getString(llvm::getGlobalContext(), s, addNull);
}

// Given a stack slot named s in a function called f,
// returns a pointer to a string called "f((s))".
Constant* getSlotName(llvm::AllocaInst* stackslot, CodegenPass* pass) {
  llvm::StringRef fnname = stackslot->getParent()->getParent()->getName();
  std::string slotname = fnname.str() + "(( " + stackslot->getName().str() + " ))";
  Constant* cslotname = getConstantArrayOfString(slotname);

  GlobalVariable* slotnameVar = new GlobalVariable(
      /*Module=*/      *(pass->mod),
      /*Type=*/        cslotname->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     GlobalValue::PrivateLinkage,
      /*Initializer=*/ cslotname,
      /*Name=*/        ".slotname." + slotname);
  slotnameVar->setAlignment(1);

  return llvm::ConstantExpr::getBitCast(arrayVariableToPointer(slotnameVar),
                                        builder.getInt8PtrTy());
}

////////////////////////////////////////////////////////////////////
Type* getSlotType(llvm::Value* v) { return v->getType()->getPointerElementType(); }

void markGCRootWithMetadata(llvm::Instruction* stackslot, CodegenPass* pass,
                            llvm::Constant* meta) {
  // If the original stack slot holds a bare struct type, we'll need to
  // insert an additional slot to point to it, and we'll mark the second slot...
  if (getSlotType(stackslot)->isStructTy()) {
    // We're assuming that someone else (in particular, LLCodegen:allocateSlot())
    // has taken care of wrapping the original struct with its typemap.

    llvm::Value* in_stackslot = getPointerToIndex(stackslot, builder.getInt32(2), "in_stackslot");
    llvm::AllocaInst* ptr_stackslot = CreateEntryAlloca(in_stackslot->getType(), "ptr_to_stackslot");
    builder.CreateStore(in_stackslot, ptr_stackslot);

    stackslot = ptr_stackslot;
  }

  llvm::Metadata* cmeta = ConstantAsMetadata::get(meta);
  llvm::MDNode* metamdnode = llvm::MDTuple::get(stackslot->getContext(),
                                llvm::makeArrayRef(cmeta));
  stackslot->setMetadata("fostergcroot", metamdnode);

  llvm::Function* F = builder.GetInsertBlock()->getParent();
  llvm::BasicBlock& entryBlock = F->getEntryBlock();
  ASSERT(pass->getCurrentAllocaPoint() != NULL) << F->getName();

  // Make sure that all the calls to llvm.gcroot() happen in the entry block.
  llvm::IRBuilder<> tmpBuilder(&entryBlock, pass->getCurrentAllocaPoint());
  ASSERT(getSlotType(stackslot)->isPointerTy()) << "\n"
              << "gc root slots must be pointers, not structs or such; had "
              << "non-pointer type " << str(getSlotType(stackslot));
  llvm::Value* root = tmpBuilder.CreateBitCast(stackslot,
                         ptrTo(tmpBuilder.getInt8PtrTy()), "gcroot");

  llvm::Constant* llvm_gcroot = llvm::Intrinsic::getDeclaration(pass->mod,
                                               llvm::Intrinsic::gcroot);
  ASSERT(llvm_gcroot) << "unable to mark GC root, llvm.gcroot not found";
  tmpBuilder.CreateCall(llvm_gcroot, { root, meta });
}

void markGCRoot(llvm::AllocaInst* stackslot, CodegenPass* pass) {
  markGCRootWithMetadata(stackslot, pass, getSlotName(stackslot, pass));
}

void CodegenPass::addEntryBB(Function* f) {
  BasicBlock* BB = BasicBlock::Create(builder.getContext(), "entry", f);
  this->allocaPoints[f] = new llvm::BitCastInst(builder.getInt32(0),
                                                builder.getInt32Ty(),
                                                "alloca point", BB);
  builder.SetInsertPoint(BB);
}

llvm::Instruction* CodegenPass::getCurrentAllocaPoint() {
  return allocaPoints[builder.GetInsertBlock()->getParent()];
}

// Creates an AllocaInst in the entry block of the current function,
// so that mem2reg will be able to optimize loads and stores from the alloca.
// Code from the Kaleidoscope tutorial on mutable variables,
// http://llvm.org/docs/tutorial/LangImpl7.html
llvm::AllocaInst* CreateEntryAlloca(llvm::Type* ty, const std::string& name) {
  llvm::BasicBlock& entryBlock =
      builder.GetInsertBlock()->getParent()->getEntryBlock();
  llvm::IRBuilder<> tmpBuilder(&entryBlock, entryBlock.begin());
  return tmpBuilder.CreateAlloca(ty, /*ArraySize=*/ 0, name);
}

llvm::AllocaInst* stackSlotWithValue(llvm::Value* val, const std::string& suffix) {
  llvm::AllocaInst* valptr = CreateEntryAlloca(val->getType(), val->getName().str() + suffix);
  builder.CreateStore(val, valptr, /*isVolatile=*/ false);
  return valptr;
}

// Unlike markGCRoot, this does not require the root be an AllocaInst
// (though it should still be a pointer).
// This function is intended for marking intermediate values. It stores
// the value into a new stack slot, and marks the stack slot as a root.
//
//      TODO need to guarantee that the val passed to us is either
//      a pointer to memalloc-ed memory, or a value that does not escape.
llvm::AllocaInst*
CodegenPass::storeAndMarkPointerAsGCRoot(llvm::Value* val) {
  ASSERT(val->getType()->isPointerTy());
  // allocate a slot for a T* on the stack
  llvm::AllocaInst* stackslot = stackSlotWithValue(val, ".gcroot");
  if (this->config.useGC) { markGCRoot(stackslot, this); }
  return stackslot;
}

Value* CodegenPass::getGlobalString(const std::string& s) {
  Value*& rv = this->staticStrings[s];
  if (!rv) { rv = builder.CreateGlobalString(s); }
  return rv;
}

void emitRecordMallocCallsite(llvm::Module* m,
                              llvm::Value* typemap,
                              llvm::Value* srclines) {
  llvm::Value* rmc = m->getFunction("record_memalloc_cell");
  ASSERT(rmc != NULL) << "NO record_memalloc_cell IN MODULE! :(";
  markAsNonAllocating(builder.CreateCall(rmc, { typemap, srclines }));
}

// |arg| is a 1-based index (0 is the fn return value).
llvm::Type* getFunctionTypeArgType(llvm::Type* fn_ptr_ty, int arg) {
 return fn_ptr_ty->getContainedType(0) // function
                 ->getContainedType(arg);
}

llvm::Value*
CodegenPass::emitMalloc(TypeAST* typ,
                        CtorRepr ctorRepr,
                        std::string srclines,
                        bool init) {
  llvm::Value* memalloc_cell = mod->getFunction("memalloc_cell");
  ASSERT(memalloc_cell != NULL) << "NO memalloc_cell IN MODULE! :(";

  llvm::GlobalVariable* ti = getTypeMapForType(typ, ctorRepr, mod, NotArray);
  ASSERT(ti != NULL) << "malloc must have type info for type " << str(typ)
                     << "; ctor id " << ctorRepr.smallId;
  llvm::Type* typemap_type = getFunctionTypeArgType(memalloc_cell->getType(), 1);
  llvm::Value* typemap = builder.CreateBitCast(ti, typemap_type);

  if (this->config.trackAllocSites) {
    llvm::Value* linesgv = (srclines.empty())
                ? llvm::ConstantPointerNull::get(builder.getInt8PtrTy())
                : builder.CreateBitCast(this->getGlobalString(srclines),
                                                 builder.getInt8PtrTy());
    emitRecordMallocCallsite(mod, typemap, linesgv);
  }

  llvm::CallInst* mem = builder.CreateCall(memalloc_cell, typemap, "mem");

  llvm::Type* ty = typ->getLLVMType();
  if (init) {
    markAsNonAllocating(builder.CreateMemSet(mem, builder.getInt8(0),
                                                  slotSizeOf(ty), /*align*/ 4));
  }

  return builder.CreateBitCast(mem, ptrTo(ty), "ptr");
}

llvm::Value*
CodegenPass::emitArrayMalloc(TypeAST* elt_type, llvm::Value* n, bool init) {
  llvm::Value* memalloc = mod->getFunction("memalloc_array");
  ASSERT(memalloc != NULL) << "NO memalloc_array IN MODULE! :(";

  CtorRepr ctorRepr; ctorRepr.smallId = -1;
  // TODO this is bogus; we should have, at most, 3 flat array representations:
  // 1) (packed) non-struct POD
  // 2) GC-able pointers
  // 3) (maybe) unboxed structs, for types with a single ctor.
  llvm::GlobalVariable* ti = getTypeMapForType(elt_type, ctorRepr, mod, YesArray);
  ASSERT(ti != NULL);
  llvm::Type* typemap_type = getFunctionTypeArgType(memalloc->getType(), 1);
  llvm::Value* typemap = builder.CreateBitCast(ti, typemap_type);
  llvm::Value* num_elts = signExtend(n, builder.getInt64Ty());
  llvm::CallInst* mem = builder.CreateCall(memalloc, { typemap, num_elts,
                                                       builder.getInt8(init) }, "arrmem");
  return builder.CreateBitCast(mem,
                  ArrayTypeAST::getZeroLengthTypeRef(elt_type), "arr_ptr");
}

// If _template has type i32, returns (v & 31) unless v is a constant < 32, in
// which case no mask is necessary to get well-defined cross-platform behavior.
llvm::Value* getMaskedForShift(IRBuilder<>& b,
                               llvm::Value* _template, llvm::Value* v) {
  ASSERT(_template->getType()->isIntegerTy());
  llvm::IntegerType* t = llvm::cast<llvm::IntegerType>(_template->getType());
  if (llvm::ConstantInt* c = llvm::dyn_cast<llvm::ConstantInt>(v)) {
    if (c->getValue().isNonNegative() && c->getValue().slt(t->getBitWidth())) {
      return v;
    }
  }
  ASSERT(t->isPowerOf2ByteWidth());
  return b.CreateAnd(v, llvm::ConstantInt::get(t, t->getBitWidth() - 1));
}

llvm::Value*
createIntrinsicCall(IRBuilder<>& b, llvm::Value* v,
                    const char* valname, llvm::Intrinsic::ID id) {
  Type*  tys[] = { v->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  Value* intrv = llvm::Intrinsic::getDeclaration(m, id, tys);

  CallInst *CI = b.CreateCall(intrv, v, valname);
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createIntrinsicCall2(IRBuilder<>& b, llvm::Value* v1, llvm::Value* v2,
                    const char* valname, llvm::Intrinsic::ID id) {
  Type*  tys[] = { v1->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  Value* intrv = llvm::Intrinsic::getDeclaration(m, id, tys);

  CallInst *CI = b.CreateCall(intrv, { v1, v2 }, valname);
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createCheckedOp(CodegenPass* pass,
                IRBuilder<>& b, llvm::Value* v1, llvm::Value* v2,
                    const char* valname, llvm::Intrinsic::ID id) {
  unsigned  arr[] = { 1 };
  llvm::Value* agg = createIntrinsicCall2(b, v1, v2, valname, id);
  llvm::Value* overflow_bit = b.CreateExtractValue(agg, arr);

  llvm::Function* F = b.GetInsertBlock()->getParent();

  llvm::BasicBlock* bb_ok  = BasicBlock::Create(b.getContext(), "check.ok", F);
  llvm::BasicBlock* bb_err = BasicBlock::Create(b.getContext(), "check.fail", F);

  b.CreateCondBr(overflow_bit, bb_ok, bb_err);

  b.SetInsertPoint(bb_err);
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << "invariant violated for " << llvm::Intrinsic::getName(id)
     << "(" << str(v1->getType()) << ")"
     << "; try running under gdb and break on `foster__assert_failed`";
  llvm::Value* msg = builder.CreateBitCast(pass->getGlobalString(ss.str()),
                                                 builder.getInt8PtrTy());
  b.CreateCall(pass->lookupFunctionOrDie("foster__assert_failed"), msg);
  b.CreateUnreachable();

  b.SetInsertPoint(bb_ok);
  unsigned  arr0[] = { 0 };
  return b.CreateExtractValue(agg, arr0, valname);
}

llvm::Value*
createCtlz(IRBuilder<>& b, llvm::Value* v, const char* valname) {
  Type*  tys[] = { v->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  Value* intrv = llvm::Intrinsic::getDeclaration(m, llvm::Intrinsic::ctlz, tys);
  Value* is_zero_undef = b.getInt1(false);
  CallInst *CI = b.CreateCall(intrv, { v, is_zero_undef }, valname);
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createFMulAdd(IRBuilder<>& b, llvm::Value* v1, llvm::Value* v2, llvm::Value* v3) {
  Type*  tys[] = { v1->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  Value* intrv = llvm::Intrinsic::getDeclaration(m, llvm::Intrinsic::fmuladd, tys);
  CallInst *CI = b.CreateCall(intrv, { v1, v2, v3 }, "fmuladdtmp");
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
CodegenPass::emitPrimitiveOperation(const std::string& op,
                                    IRBuilder<>& b,
                                    const std::vector<Value*>& args) {
  Value* VL = args.at(0);
       if (op == "negate") { return b.CreateNeg(VL, "negtmp", this->config.useNUW, this->config.useNSW); }
  else if (op == "bitnot") { return b.CreateNot(VL, "nottmp"); }
  else if (op == "sext_i64") { return b.CreateSExt(VL, b.getInt64Ty(), "sexti64tmp"); }
  else if (op == "zext_i64") { return b.CreateZExt(VL, b.getInt64Ty(), "zexti64tmp"); }
  else if (op == "sext_i32") { return b.CreateSExt(VL, b.getInt32Ty(), "sexti32tmp"); }
  else if (op == "zext_i32") { return b.CreateZExt(VL, b.getInt32Ty(), "zexti32tmp"); }
  else if (op == "zext_WordX2") { return b.CreateZExt(VL, getWordX2Ty(b), "zextWx2tmp"); }
  else if (op == "zext_Word")   { return b.CreateZExt(VL, getWordTy(b),   "zextWtmp"); }
  else if (op == "sext_WordX2") { return b.CreateZExt(VL, getWordX2Ty(b), "sextWx2tmp"); }
  else if (op == "sext_Word")   { return b.CreateZExt(VL, getWordTy(b),   "sextWtmp"); }
  else if (op == "trunc_i8") { return b.CreateTrunc(VL, b.getInt8Ty(), "trunci8tmp"); }
  else if (op == "trunc_i32"){ return b.CreateTrunc(VL, b.getInt32Ty(), "trunci32tmp"); }
  else if (op == "trunc_i64"){ return b.CreateTrunc(VL, b.getInt64Ty(), "trunci64tmp"); }
  else if (op == "trunc_w0") { return b.CreateTrunc(VL, getWordTy(b),   "truncw0tmp"); }
  else if (op == "trunc_w1") { return b.CreateTrunc(VL, getWordX2Ty(b), "truncw1tmp"); }
  else if (op == "ctlz")     { return createCtlz(b, VL, "ctlztmp"); }
  else if (op == "ctpop")    { return createIntrinsicCall(b, VL, "ctpoptmp", llvm::Intrinsic::ctpop); }
  else if (op == "fsqrt")    { return createIntrinsicCall(b, VL, "fsqrttmp", llvm::Intrinsic::sqrt); }
  else if (op == "fptosi_f64_i32") { return b.CreateFPToSI(VL, b.getInt32Ty(), "fptosi_f64_i32tmp"); }
  else if (op == "fptoui_f64_i32") { return b.CreateFPToUI(VL, b.getInt32Ty(), "fptoui_f64_i32tmp"); }
  else if (op == "fptosi_f64_i64") { return b.CreateFPToSI(VL, b.getInt64Ty(), "fptosi_f64_i64tmp"); }
  else if (op == "fptoui_f64_i64") { return b.CreateFPToUI(VL, b.getInt64Ty(), "fptoui_f64_i64tmp"); }
  else if (op == "sitofp_f64")     { return b.CreateSIToFP(VL, b.getDoubleTy(), "sitofp_f64tmp"); }
  else if (op == "uitofp_f64")     { return b.CreateUIToFP(VL, b.getDoubleTy(), "uitofp_f64tmp"); }

  ASSERT(args.size() > 1) << "CodegenUtils.cpp missing implementation of " << op << "\n";

  Value* VR = args.at(1);

  if (VL->getType() != VR->getType()) {
    b.GetInsertBlock()->getParent()->dump();
    ASSERT(false) << "primop values for " << op << " did not have equal types\n"
           << "VL: " << str(VL) << " :: " << str(VL->getType()) << "\n"
           << "VR: " << str(VR) << " :: " << str(VR->getType()) << "\n"
           << "32-bit: " << is32Bit() << "; " << str(getWordTy(b));
  }

  // Other variants: F (float), NSW (no signed wrap), NUW,
  // UDiv, ExactSDiv, URem, SRem,
       if (op == "+") { return b.CreateAdd(VL, VR, "addtmp", this->config.useNUW, this->config.useNSW); }
  else if (op == "-") { return b.CreateSub(VL, VR, "subtmp", this->config.useNUW, this->config.useNSW); }
  else if (op == "*") { return b.CreateMul(VL, VR, "multmp", this->config.useNUW, this->config.useNSW); }
  else if (op == "+uc") { return createCheckedOp(this, b, VL, VR, "addtmp", llvm::Intrinsic::uadd_with_overflow); }
  else if (op == "*uc") { return createCheckedOp(this, b, VL, VR, "multmp", llvm::Intrinsic::umul_with_overflow); }
  else if (op == "-uc") { return createCheckedOp(this, b, VL, VR, "subtmp", llvm::Intrinsic::usub_with_overflow); }
  else if (op == "+sc") { return createCheckedOp(this, b, VL, VR, "addtmp", llvm::Intrinsic::sadd_with_overflow); }
  else if (op == "*sc") { return createCheckedOp(this, b, VL, VR, "multmp", llvm::Intrinsic::smul_with_overflow); }
  else if (op == "-sc") { return createCheckedOp(this, b, VL, VR, "subtmp", llvm::Intrinsic::ssub_with_overflow); }
  else if (op == "sdiv-unsafe") { return b.CreateSDiv(VL, VR, "sdivtmp"); }
  else if (op == "udiv-unsafe") { return b.CreateUDiv(VL, VR, "udivtmp"); }
  else if (op == "srem-unsafe") { return b.CreateSRem(VL, VR, "sremtmp"); }
  else if (op == "urem-unsafe") { return b.CreateURem(VL, VR, "uremtmp"); }
  else if (op == "frem-unsafe") { return b.CreateFRem(VL, VR, "fremtmp"); }
  else if (op == "f+"         ) { return b.CreateFAdd(VL, VR, "faddtmp"); }
  else if (op == "f-"         ) { return b.CreateFSub(VL, VR, "fsubtmp"); }
  else if (op == "fdiv"       ) { return b.CreateFDiv(VL, VR, "fdivtmp"); }
  else if (op == "f*"         ) { return b.CreateFMul(VL, VR, "fmultmp"); }

  else if (op ==  "<s"        ) { return b.CreateICmpSLT(VL, VR, "slttmp"); }
  else if (op == "<=s"        ) { return b.CreateICmpSLE(VL, VR, "sletmp"); }
  else if (op ==  ">s"        ) { return b.CreateICmpSGT(VL, VR, "sgttmp"); }
  else if (op == ">=s"        ) { return b.CreateICmpSGE(VL, VR, "sgetmp"); }
  else if (op ==  "<u"        ) { return b.CreateICmpULT(VL, VR, "ulttmp"); }
  else if (op == "<=u"        ) { return b.CreateICmpULE(VL, VR, "uletmp"); }
  else if (op ==  ">u"        ) { return b.CreateICmpUGT(VL, VR, "ugttmp"); }
  else if (op == ">=u"        ) { return b.CreateICmpUGE(VL, VR, "ugetmp"); }
  else if (op == "=="         ) { return b.CreateICmpEQ(VL, VR, "eqtmp"); }
  else if (op == "!="         ) { return b.CreateICmpNE(VL, VR, "netmp"); }
  // Use unordered (U) variants because we don't analyze for QNANs.
  else if (op == "f<"         ) { return b.CreateFCmpULT(VL, VR, "fulttmp"); }
  else if (op == "f<="        ) { return b.CreateFCmpULE(VL, VR, "fuletmp"); }
  else if (op == "f>"         ) { return b.CreateFCmpUGT(VL, VR, "fugttmp"); }
  else if (op == "f>="        ) { return b.CreateFCmpUGE(VL, VR, "fugetmp"); }
  else if (op == "f=="        ) { return b.CreateFCmpUEQ(VL, VR, "fueqtmp"); }
  else if (op == "f!="        ) { return b.CreateFCmpUNE(VL, VR, "funetmp"); }
  // TODO: ORD = no nans, UNO = either nans

  else if (op == "bitand" ) { return b.CreateAnd(VL, VR, "bitandtmp"); }
  else if (op == "bitor"  ) {  return b.CreateOr( VL, VR, "bitortmp"); }
  else if (op == "bitxor" ) { return b.CreateXor(VL, VR, "bitxortmp"); }

  else if (op == "bitshl" ) { return b.CreateShl(VL,  getMaskedForShift(b, VL, VR), "shltmp", this->config.useNUW, this->config.useNSW); }
  else if (op == "bitlshr") { return b.CreateLShr(VL, getMaskedForShift(b, VL, VR), "lshrtmp"); }
  else if (op == "bitashr") { return b.CreateAShr(VL, getMaskedForShift(b, VL, VR), "ashrtmp"); }

  ASSERT(args.size() > 2) << "CodegenUtils.cpp missing implementation of " << op << "\n";

  Value* VT = args.at(2);
       if (op == "fmuladd") { return createFMulAdd(b, VL, VR, VT); }

  ASSERT(false) << "unhandled op '" << op << "'";
  return NULL;
}

struct LLProcPrimBase : public LLProc {
protected:
  std::string name;
  std::vector<std::string> argnames;
public:
  explicit LLProcPrimBase() {}
  virtual ~LLProcPrimBase() {}

  virtual llvm::GlobalValue::LinkageTypes getFunctionLinkage() const { return llvm::GlobalValue::ExternalLinkage; }
  virtual std::vector<std::string>        getFunctionArgNames() const { return argnames; }
  virtual const std::string getName() const { return name; }
  virtual const std::string getCName() const { return name; }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) = 0;
};

// So much boilerplate...
struct LLProcStringOfCStringPrim : public LLProcPrimBase {
  explicit LLProcStringOfCStringPrim() {
      this->name = "foster_emit_string_of_cstring";
      this->argnames.push_back("buf");
      this->argnames.push_back("len");
      std::vector<TypeAST*> argTypes;
      argTypes.push_back(RefTypeAST::get(TypeAST::i(8)));
      argTypes.push_back(TypeAST::i(32));
      std::map<std::string, std::string> annots; annots["callconv"] = "ccc";
      this->type = new FnTypeAST(foster::ParsingContext::lookupType("Text"),
                                 argTypes, NULL, annots);
  }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) {
    Function::arg_iterator AI = F->arg_begin();
    Value* cstr = AI++;
    Value* sz   = AI++;
    Value* str = pass->emitFosterStringOfCString(cstr, sz);
    builder.CreateRet(str);
  }
};

void codegenCall1ToFunction(llvm::Function* F, llvm::Value* f) {
    Function::arg_iterator AI = F->arg_begin();
    Value* n = AI++;
    llvm::CallInst* call = builder.CreateCall(f, n);
    call->setCallingConv(llvm::CallingConv::C);
    // Implicitly: called function may GC...
    builder.CreateRet(builder.CreateBitCast(call, F->getReturnType()));
}

struct LLProcGetCmdlineArgPrim : public LLProcPrimBase {
  explicit LLProcGetCmdlineArgPrim() {
      this->name = "get_cmdline_arg_n";
      this->argnames.push_back("n");
      std::vector<TypeAST*> argTypes;
      argTypes.push_back(TypeAST::i(32));
      std::map<std::string, std::string> annots; annots["callconv"] = "ccc";
      this->type = new FnTypeAST(foster::ParsingContext::lookupType("Text"),
                                 argTypes, NULL, annots);
  }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) {
    return codegenCall1ToFunction(F,
             pass->lookupFunctionOrDie("foster_get_cmdline_arg_n_raw"));
  }
};

struct LLProcFmtTimePrim : public LLProcPrimBase {
  explicit LLProcFmtTimePrim() {
      this->name = "foster_fmttime_secs";
      this->argnames.push_back("n");
      std::vector<TypeAST*> argTypes;
      argTypes.push_back(PrimitiveTypeAST::get("Float64", builder.getDoubleTy()));
      std::map<std::string, std::string> annots; annots["callconv"] = "ccc";
      this->type = new FnTypeAST(foster::ParsingContext::lookupType("Text"),
                                 argTypes, NULL, annots);
  }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) {
    return codegenCall1ToFunction(F,
             pass->lookupFunctionOrDie("foster_fmttime_secs_raw"));
  }
};

void extendWithImplementationSpecificProcs(CodegenPass* _pass,
                                           std::vector<LLProc*>& procs) {
  // This function is useful to the runtime (and should therefore
  // be generated with external linkage and C calling convention)
  // but involves code most easily generated by the compiler.
  procs.push_back(new LLProcStringOfCStringPrim());
  procs.push_back(new LLProcGetCmdlineArgPrim());
  procs.push_back(new LLProcFmtTimePrim());
}


