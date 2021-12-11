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
#include "llvm/Support/MathExtras.h"

#include <string>
#include <sstream>

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
  llvm::Function* fosterBoundsCheck = mod->getFunction("foster__boundscheck64");
  ASSERT(fosterBoundsCheck != NULL);

  Value* msg_array = builder.CreateGlobalString(srclines);
  Value* msg = builder.CreateBitCast(msg_array, builder.getInt8PtrTy());
  Value* ext = signExtend(idx, len64->getType());
  builder.CreateCall(from(fosterBoundsCheck), { ext, len64, msg });
}

void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr) {
  llvm::Function* fosterAssert = mod->getFunction("foster__assert");
  ASSERT(fosterAssert != NULL);

  Value* msg_array = builder.CreateGlobalString(cstr);
  Value* msg = builder.CreateBitCast(msg_array, builder.getInt8PtrTy());
  builder.CreateCall(from(fosterAssert), { cond, msg });
}

llvm::Value* getUnitValue() {
  return llvm::ConstantPointerNull::get(
    llvm::dyn_cast<llvm::PointerType>(getUnitType()->getLLVMType()));
}

Value* getPointerToIndex(Value* ptrToCompositeValue,
                         Value* idxValue,
                         const std::string& name) {
  std::vector<Value*> idx;
  idx.push_back(builder.getInt32(0));
  idx.push_back(idxValue);

  llvm::Type* underlyingTy = ptrToCompositeValue->getType()->getContainedType(0);
  auto indexedTy = llvm::GetElementPtrInst::getIndexedType(underlyingTy, idx);
  ASSERT(indexedTy != nullptr)
      << "Attempt to use index " << str(idxValue)
      << "\non val of type "     << str(ptrToCompositeValue->getType())
      << "\nwith value "         << str(ptrToCompositeValue);

  return builder.CreateGEP(ptrToCompositeValue, llvm::makeArrayRef(idx), name.c_str());
}

////////////////////////////////////////////////////////////////////

Constant* getConstantArrayOfString(llvm::StringRef s, bool addNull) {
  return llvm::ConstantDataArray::getString(foster::fosterLLVMContext, s, addNull);
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
  slotnameVar->setAlignment(llvm::MaybeAlign(1));

  return llvm::ConstantExpr::getBitCast(arrayVariableToPointer(slotnameVar),
                                        builder.getInt8PtrTy());
}

////////////////////////////////////////////////////////////////////
Type* getSlotType(llvm::Value* v) { return v->getType()->getPointerElementType(); }

extern char kFosterMain[];
void CodegenPass::markFosterFunction(Function* f) {
  if (!this->fosterFunctionAttributes.isEmpty()) {
    f->setAttributes(this->fosterFunctionAttributes);
  }

  // We must not inline foster__main, which is marked with our gc,
  // into its caller, which is a gc-less function!
  if (   f->getName() == kFosterMain
      || f->getName().find("noinline_llvm_") == 0) {
    f->addFnAttr(llvm::Attribute::NoInline);
  }
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

Value* CodegenPass::getGlobalString(const std::string& s) {
  Value*& rv = this->staticStrings[s];
  if (!rv) { rv = builder.CreateGlobalString(s); }
  return rv;
}

void emitRecordMallocCallsite(llvm::Module* m,
                              llvm::Value* mem,
                              llvm::Value* typemap,
                              llvm::Value* srcloc,
                              llvm::Value* typedesc) {
  llvm::Function* rmc = m->getFunction("record_memalloc_cell");
  ASSERT(rmc != NULL) << "NO record_memalloc_cell IN MODULE! :(";
  builder.CreateCall(from(rmc), { mem, typemap, srcloc, typedesc });
}

// |arg| is a 1-based index (0 is the fn return value).
llvm::Type* getFunctionTypeArgType(llvm::Type* fn_ptr_ty, int arg) {
 return fn_ptr_ty->getContainedType(0) // function
                 ->getContainedType(arg);
}

llvm::Value*
CodegenPass::emitMalloc(TypeAST* typ,
                        CtorRepr ctorRepr,
                        std::string typedesc,
                        std::string srcloc_str,
                        bool init) {
  llvm::Function* memalloc_cell = mod->getFunction("memalloc_cell");
  ASSERT(memalloc_cell != NULL) << "NO memalloc_cell IN MODULE! :(";

  llvm::GlobalVariable* ti = getTypeMapForType(typ, ctorRepr, mod, NotArray);
  ASSERT(ti != NULL) << "malloc must have type info for type " << str(typ)
                     << "; ctor id " << ctorRepr.smallId;
  llvm::Type* typemap_type = getFunctionTypeArgType(memalloc_cell->getType(), 1);
  llvm::Value* typemap = builder.CreateBitCast(ti, typemap_type);

  llvm::CallInst* mem = builder.CreateCall(memalloc_cell, typemap, "mem");

  if (this->config.trackAllocSites) {
    llvm::Value* linesgv = (typedesc.empty())
                ? llvm::ConstantPointerNull::get(builder.getInt8PtrTy())
                : builder.CreateBitCast(this->getGlobalString(typedesc),
                                                 builder.getInt8PtrTy());

    llvm::Value* srcloc = 
                 builder.CreateBitCast(this->getGlobalString(srcloc_str),
                                                 builder.getInt8PtrTy());
    emitRecordMallocCallsite(mod, mem, typemap, srcloc, linesgv);
  }

  llvm::Type* ty = typ->getLLVMType();
  if (init) {
    builder.CreateMemSet(mem, builder.getInt8(0), slotSizeOf(ty), llvm::MaybeAlign(4));
  }

  return builder.CreateBitCast(mem, ptrTo(ty), "ptr");
}

llvm::Value*
CodegenPass::emitArrayMalloc(TypeAST* elt_type, llvm::Value* n, bool init) {
  llvm::Function* memalloc = mod->getFunction("memalloc_array");
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
  llvm::CallInst* mem = builder.CreateCall(from(memalloc),
                          { typemap, num_elts, builder.getInt8(init) }, "arrmem");

  if (this->config.trackAllocSites) {
    auto linesgv = llvm::ConstantPointerNull::get(builder.getInt8PtrTy());
    auto srcloc  = llvm::ConstantPointerNull::get(builder.getInt8PtrTy());
    emitRecordMallocCallsite(mod, mem, typemap, srcloc, linesgv);
  }

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
  ASSERT(llvm::isPowerOf2_32(t->getBitWidth()));
  return b.CreateAnd(v, llvm::ConstantInt::get(t, t->getBitWidth() - 1));
}

llvm::Value*
createIntrinsicCall(IRBuilder<>& b, llvm::Value* v,
                    const char* valname, llvm::Intrinsic::ID id) {
  Type*  tys[] = { v->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  llvm::Function* intrv = llvm::Intrinsic::getDeclaration(m, id, tys);

  CallInst *CI = b.CreateCall(from(intrv), v, valname);
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createIntrinsicCall2(IRBuilder<>& b, llvm::Value* v1, llvm::Value* v2,
                    const char* valname, llvm::Intrinsic::ID id) {
  Type*  tys[] = { v1->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  llvm::Function* intrv = llvm::Intrinsic::getDeclaration(m, id, tys);

  CallInst *CI = b.CreateCall(from(intrv), { v1, v2 }, valname);
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createCheckedOp(CodegenPass* pass,
                IRBuilder<>& b, llvm::Value* v1, llvm::Value* v2,
                    const char* valname, const std::string& op, llvm::Intrinsic::ID id) {
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
  ss << "invariant violated for LLVM intrinisic corresponding to " << op
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
  llvm::Function* intrv = llvm::Intrinsic::getDeclaration(m, llvm::Intrinsic::ctlz, tys);
  Value* is_zero_undef = b.getInt1(false);
  CallInst *CI = b.CreateCall(from(intrv), { v, is_zero_undef }, valname);
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createFMulAdd(IRBuilder<>& b, llvm::Value* v1, llvm::Value* v2, llvm::Value* v3) {
  Type*  tys[] = { v1->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  llvm::Function* intrv = llvm::Intrinsic::getDeclaration(m, llvm::Intrinsic::fmuladd, tys);
  CallInst *CI = b.CreateCall(from(intrv), { v1, v2, v3 }, "fmuladdtmp");
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createPowi(IRBuilder<>& b, llvm::Value* vd, llvm::Value* vi) {
  Type*  tys[] = { vd->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  llvm::Function* intrv = llvm::Intrinsic::getDeclaration(m, llvm::Intrinsic::powi, tys);
  CallInst *CI = b.CreateCall(from(intrv), { vd, vi }, "powi");
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
createPow(IRBuilder<>& b, llvm::Value* vd, llvm::Value* vi) {
  Type*  tys[] = { vd->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  llvm::Function* intrv = llvm::Intrinsic::getDeclaration(m, llvm::Intrinsic::pow, tys);
  CallInst *CI = b.CreateCall(from(intrv), { vd, vi }, "pow");
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Function*
getFunction(IRBuilder<>& b, const std::string& name) {
  Module* m = b.GetInsertBlock()->getParent()->getParent();
  auto func = m->getFunction(name);
  ASSERT(func != NULL) << "MISSING " << name << " IN MODULE! :(";
  return func;
}

llvm::Value*
createCall1(IRBuilder<>& b, const std::string& name, llvm::Value* vd) {
  return b.CreateCall(getFunction(b, name), { vd });
}

llvm::Value*
createFtan(IRBuilder<>& b, llvm::Value* vd) {
  auto name = vd->getType()->isFloatTy() ? "foster__tanf32" : "foster__tanf64";
  return createCall1(b, name, vd);
}

llvm::Value*
createIntIsSmall(IRBuilder<>& b, llvm::Value* vd) {
  auto func = getFunction(b, "foster_prim_Int_isSmall");
  // Open-coded autowrapper.
  return b.CreateCall(func, { b.CreateBitCast(vd, func->getFunctionType()->getParamType(0)) });
}

llvm::Value*
createIntToSmall(IRBuilder<>& b, llvm::Value* vd) {
  auto func = getFunction(b, "foster_prim_Int_to_smallWord");
  // Open-coded autowrapper.
  return b.CreateCall(func, { b.CreateBitCast(vd, func->getFunctionType()->getParamType(0)) });
}

llvm::Value*
createIntOfSmall(IRBuilder<>& b, llvm::Value* vd) {
  auto func = getFunction(b, "foster_prim_smallWord_to_Int");
  auto call = b.CreateCall(func, { vd }); // Open-coded autowrapper.

  std::vector<DataCtor*> ctors;
  auto dt = DataTypeAST("Int", ctors, SourceRange::getEmptyRange());
  auto intType = dt.getLLVMType();
  return b.CreateBitCast(call, intType);
}

llvm::Value*
CodegenPass::emitPrimitiveOperation(const std::string& op,
                                    IRBuilder<>& b, TypeAST* assoc,
                                    const std::vector<Value*>& args) {
  Value* VL = args.at(0);
       if (op == "negate") { return b.CreateNeg(VL, "negtmp", this->config.useNUW, this->config.useNSW); }
  else if (op == "bitnot") { return b.CreateNot(VL, "nottmp"); }
  else if (op == "sext") { return b.CreateSExt(VL, assoc->getLLVMType(), "sexttmp"); }
  else if (op == "zext") { return b.CreateZExt(VL, assoc->getLLVMType(), "zexttmp"); }
  else if (op == "trunc")   { return b.CreateTrunc(VL, assoc->getLLVMType(), "trunctmp"); }
  else if (op == "fpext_f64")   { return b.CreateFPExt(VL, b.getDoubleTy(), "fptexttmp"); }
  else if (op == "fptrunc_f32") { return b.CreateFPTrunc(VL, b.getFloatTy(), "fptrunctmp"); }
  else if (op == "ctlz")     { return createCtlz(b, VL, "ctlztmp"); }
  else if (op == "ctpop")    { return createIntrinsicCall(b, VL, "ctpoptmp", llvm::Intrinsic::ctpop); }
  else if (op == "fsqrt")    { return createIntrinsicCall(b, VL, "fsqrttmp", llvm::Intrinsic::sqrt); }
  else if (op == "fabs")     { return createIntrinsicCall(b, VL, "fabstmp",  llvm::Intrinsic::fabs); }
  else if (op == "fsin")     { return createIntrinsicCall(b, VL, "fsintmp",  llvm::Intrinsic::sin); }
  else if (op == "fcos")     { return createIntrinsicCall(b, VL, "fcostmp",  llvm::Intrinsic::cos); }
  else if (op == "fexp")     { return createIntrinsicCall(b, VL, "fexptmp",  llvm::Intrinsic::exp); }
  else if (op == "fexp2")    { return createIntrinsicCall(b, VL, "fexp2tmp", llvm::Intrinsic::exp2); }
  else if (op == "flog"    ) { return createIntrinsicCall(b, VL, "flogtmp",  llvm::Intrinsic::log); }
  else if (op == "flog2"   ) { return createIntrinsicCall(b, VL, "flogtmp",  llvm::Intrinsic::log2); }
  else if (op == "flog10"  ) { return createIntrinsicCall(b, VL, "flogtmp",  llvm::Intrinsic::log10); }
  else if (op == "fceil"   ) { return createIntrinsicCall(b, VL, "fceiltmp", llvm::Intrinsic::ceil); }
  else if (op == "ffloor"  ) { return createIntrinsicCall(b, VL, "floortmp", llvm::Intrinsic::floor); }
  else if (op == "fround"  ) { return createIntrinsicCall(b, VL, "frondtmp", llvm::Intrinsic::round); }
  else if (op == "ftrunc"  ) { return createIntrinsicCall(b, VL, "ftrnctmp", llvm::Intrinsic::trunc); }
  else if (op == "fptosi_f64_i32") { return b.CreateFPToSI(VL, b.getInt32Ty(), "fptosi_f64_i32tmp"); }
  else if (op == "fptoui_f64_i32") { return b.CreateFPToUI(VL, b.getInt32Ty(), "fptoui_f64_i32tmp"); }
  else if (op == "fptosi_f64_i64") { return b.CreateFPToSI(VL, b.getInt64Ty(), "fptosi_f64_i64tmp"); }
  else if (op == "fptoui_f64_i64") { return b.CreateFPToUI(VL, b.getInt64Ty(), "fptoui_f64_i64tmp"); }
  else if (op == "sitofp_f64")     { return b.CreateSIToFP(VL, b.getDoubleTy(), "sitofp_f64tmp"); }
  else if (op == "uitofp_f64")     { return b.CreateUIToFP(VL, b.getDoubleTy(), "uitofp_f64tmp"); }
  else if (op == "fptosi_f32_i32") { return b.CreateFPToSI(VL, b.getInt32Ty(), "fptosi_f32_i32tmp"); }
  else if (op == "fptoui_f32_i32") { return b.CreateFPToUI(VL, b.getInt32Ty(), "fptoui_f32_i32tmp"); }
  else if (op == "sitofp_f32")     { return b.CreateSIToFP(VL, b.getFloatTy(),  "sitofp_f32tmp"); }
  else if (op == "uitofp_f32")     { return b.CreateUIToFP(VL, b.getFloatTy(),  "uitofp_f32tmp"); }
  else if (op == "bitcast")        { return b.CreateBitCast(VL, assoc->getLLVMType(), "bitcast_tmp"); }
  else if (op == "ftan")           { return createFtan(b, VL); }
  else if (op == "Int-isSmall")    { return createIntIsSmall(b, VL); }
  else if (op == "Int-toSmall")    { return createIntToSmall(b, VL); }
  else if (op == "Int-ofSmall")    { return createIntOfSmall(b, VL); }

  ASSERT(args.size() > 1) << "CodegenUtils.cpp missing implementation of " << op << "\n";

  Value* VR = args.at(1);

  if ((VL->getType() != VR->getType()) && op != "fpowi") {
    llvm::errs() << b.GetInsertBlock()->getParent() << "\n";
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
  else if (op == "+uc") { return createCheckedOp(this, b, VL, VR, "addtmp", op, llvm::Intrinsic::uadd_with_overflow); }
  else if (op == "*uc") { return createCheckedOp(this, b, VL, VR, "multmp", op, llvm::Intrinsic::umul_with_overflow); }
  else if (op == "-uc") { return createCheckedOp(this, b, VL, VR, "subtmp", op, llvm::Intrinsic::usub_with_overflow); }
  else if (op == "+sc") { return createCheckedOp(this, b, VL, VR, "addtmp", op, llvm::Intrinsic::sadd_with_overflow); }
  else if (op == "*sc") { return createCheckedOp(this, b, VL, VR, "multmp", op, llvm::Intrinsic::smul_with_overflow); }
  else if (op == "-sc") { return createCheckedOp(this, b, VL, VR, "subtmp", op, llvm::Intrinsic::ssub_with_overflow); }
  else if (op == "sdiv-unsafe") { return b.CreateSDiv(VL, VR, "sdivtmp"); }
  else if (op == "udiv-unsafe") { return b.CreateUDiv(VL, VR, "udivtmp"); }
  else if (op == "srem-unsafe") { return b.CreateSRem(VL, VR, "sremtmp"); }
  else if (op == "urem-unsafe") { return b.CreateURem(VL, VR, "uremtmp"); }
  else if (op == "frem-unsafe") { return b.CreateFRem(VL, VR, "fremtmp"); }
  else if (op == "f+"         ) { return b.CreateFAdd(VL, VR, "faddtmp"); }
  else if (op == "f-"         ) { return b.CreateFSub(VL, VR, "fsubtmp"); }
  else if (op == "fdiv"       ) { return b.CreateFDiv(VL, VR, "fdivtmp"); }
  else if (op == "frem"       ) { return b.CreateFRem(VL, VR, "fremtmp"); }
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
  else if (op == "fpowi")   { return createPowi(b, VL, VR); }
  else if (op == "fpow")    { return createPow(b, VL, VR); }

  ASSERT(args.size() > 2) << "CodegenUtils.cpp missing implementation of " << op << "\n";

  Value* VT = args.at(2);
       if (op == "fmuladd") { return createFMulAdd(b, VL, VR, VT); }

  ASSERT(false) << "unhandled op '" << op << "'";
  return NULL;
}


// Some C functions need to take or return types (like FILE*) for
// which it's awkward to arrange for the LLVM representation of the Foster
// arg/return type to agree with Clang's representation. For these functions,
// we want to generate a wrapper which bitcasts away the type mismatch.
//
// We'll create a function with the given symbolName which calls function F.
void codegenAutoWrapper(llvm::Function* F,
                        llvm::FunctionType* wrappedTy,
                        //llvm::CallingConv::ID cc,
                        //llvm::GlobalValue::LinkageTypes linkage,
                           std::string symbolName,
                           CodegenPass* pass) {
    auto linkage = llvm::GlobalValue::ExternalLinkage;
    auto Ffunc = Function::Create(wrappedTy, linkage, symbolName, pass->mod);
    Ffunc->setAttributes(F->getAttributes());
    Ffunc->setCallingConv(F->getCallingConv());
    pass->addEntryBB(Ffunc);
    std::vector<llvm::Value*> args;
    auto arg = Ffunc->arg_begin();
    for (int n = 0; arg != Ffunc->arg_end(); ++n) {
      args.push_back(builder.CreateBitCast(&*arg,
                        F->getFunctionType()->getParamType(n)));
      ++arg;
    }

    auto callInst = builder.CreateCall(F, args);
    callInst->setTailCall(true);
    callInst->setCallingConv(F->getCallingConv());

    if (callInst->getType()->isVoidTy()) {
      if (!wrappedTy->getReturnType()->isVoidTy()) {
        builder.CreateRet(getUnitValue());
      } else builder.CreateRetVoid();
    } else {
      builder.CreateRet(builder.CreateBitCast(callInst, wrappedTy->getReturnType()));
    }
    //pass->markFosterFunction(Ffunc);
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
                                 argTypes, annots);
  }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) {
    pass->markFosterFunction(F);
    Function::arg_iterator AI = F->arg_begin();
    Value* cstr = &*(AI++);
    Value* sz   = &*(AI++);
    Value* str = pass->emitFosterStringOfCString(cstr, sz);
    builder.CreateRet(str);
  }
};

void codegenCall0ToFunction(llvm::Function* F, llvm::FunctionCallee f) {
    llvm::CallInst* call = builder.CreateCall(f);
    call->setCallingConv(llvm::CallingConv::C);
    // Implicitly: called function may GC...
    builder.CreateRet(builder.CreateBitCast(call, F->getReturnType()));
}

void codegenCall1ToFunctionWithArg(llvm::Function* F, llvm::FunctionCallee f, llvm::Value* n) {
    llvm::CallInst* call = builder.CreateCall(f, n);
    call->setCallingConv(llvm::CallingConv::C);
    // Implicitly: called function may GC...
    if (F->getReturnType()->isVoidTy()) {
      builder.CreateRetVoid();
    } else {
      builder.CreateRet(builder.CreateBitCast(call, F->getReturnType()));
    }
}

void codegenCall1ToFunction(llvm::Function* F, llvm::FunctionCallee f) {
    Function::arg_iterator AI = F->arg_begin();
    Value* n = &*(AI++);
    codegenCall1ToFunctionWithArg(F, f, n);
}

struct LLProcGetCmdlineArgPrim : public LLProcPrimBase {
  explicit LLProcGetCmdlineArgPrim() {
      this->name = "get_cmdline_arg_n";
      this->argnames.push_back("n");
      std::vector<TypeAST*> argTypes;
      argTypes.push_back(TypeAST::i(32));
      std::map<std::string, std::string> annots; annots["callconv"] = "ccc";
      this->type = new FnTypeAST(foster::ParsingContext::lookupType("Text"),
                                 argTypes, annots);
  }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) {
    pass->markFosterFunction(F);
    return codegenCall1ToFunction(F,
             pass->lookupFunctionOrDie("foster_get_cmdline_arg_n_raw"));
  }
};

struct LLProcAllocDefaultCoro : public LLProcPrimBase {
  explicit LLProcAllocDefaultCoro() {
      this->name = "foster__runtime__alloc_default_coro";
      std::vector<TypeAST*> argTypes;
      std::map<std::string, std::string> annots; annots["callconv"] = "ccc";
      this->type = new FnTypeAST(RefTypeAST::get(foster_generic_coro_ast), argTypes, annots);
  }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) {
    pass->markFosterFunction(F);
    // The returned coro is uninitialized, but this should only be
    // called by the runtime, which will do the appropriate intialization.
    CtorRepr bogusCtor; bogusCtor.smallId = -1;
    Value* dcoro = pass->emitMalloc(getSplitCoroTyp(getUnitType()), bogusCtor, "dcoro", "<default coro>", /*init*/ true);
    builder.CreateRet(builder.CreateBitCast(dcoro,
                  ptrTo(foster_generic_coro_ast->getLLVMType())));
  }

  // Returns { { ... generic coro ... }, argTypes }
  StructTypeAST* getSplitCoroTyp(TypeAST* argTypes)
  {
    std::vector<TypeAST*> parts;
    parts.push_back(foster_generic_coro_ast);
    parts.push_back(argTypes);
    return StructTypeAST::get(parts);
  }
};


void extendWithImplementationSpecificProcs(CodegenPass* _pass,
                                           std::vector<LLProc*>& procs) {
  // These functions are useful to the runtime (and should therefore
  // be generated with external linkage and C calling convention)
  // but involves code most easily generated by the compiler.
  procs.push_back(new LLProcStringOfCStringPrim());
  procs.push_back(new LLProcGetCmdlineArgPrim());
  
  procs.push_back(new LLProcAllocDefaultCoro());
}


