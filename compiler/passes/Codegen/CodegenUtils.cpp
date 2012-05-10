// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "passes/CodegenPass-impl.h"
#include "parse/FosterTypeAST.h"

#include "llvm/Intrinsics.h"
#include "llvm/LLVMContext.h"

#include <string>

using namespace llvm;

using foster::EDiag;
using foster::builder;

////////////////////////////////////////////////////////////////////

CodegenPass::ValueScope* CodegenPass::newScope(const std::string& scopeName) {
  return valueSymTab.newScope(scopeName);
}

void CodegenPass::insertScopedValue(const std::string& name, llvm::Value* v) {
  valueSymTab.insert(name, v);
}

void CodegenPass::popExistingScope(ValueScope* scope) {
  valueSymTab.popExistingScope(scope);
}

////////////////////////////////////////////////////////////////////

void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr) {
  Value* fosterAssert = mod->getFunction("foster__assert");
  ASSERT(fosterAssert != NULL);

  Value* msg_array = builder.CreateGlobalString(cstr);
  Value* msg = builder.CreateBitCast(msg_array, builder.getInt8PtrTy());
  llvm::CallInst* call = builder.CreateCall2(fosterAssert, cond, msg);
  markAsNonAllocating(call);
}

llvm::Value* getUnitValue() {
  return llvm::ConstantPointerNull::get(builder.getInt8PtrTy());
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

// Given a stack slot named s in a function called f,
// returns a pointer to a string called "f((s))".
Constant* getSlotName(llvm::AllocaInst* stackslot, CodegenPass* pass) {
  llvm::StringRef fnname = stackslot->getParent()->getParent()->getName();
  std::string slotname = fnname.str() + "(( " + stackslot->getName().str() + " ))";
  Constant* cslotname = ConstantArray::get(builder.getContext(),
                                           slotname.c_str(),
                                           true);
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

void markGCRootWithMetadata(llvm::AllocaInst* stackslot, CodegenPass* pass,
                            llvm::Value* meta) {
  llvm::MDNode* metamdnode = llvm::MDNode::get(stackslot->getContext(),
                                llvm::makeArrayRef(meta));
  stackslot->setMetadata("fostergcroot", metamdnode);

  llvm::Function* F = builder.GetInsertBlock()->getParent();
  llvm::BasicBlock& entryBlock = F->getEntryBlock();
  ASSERT(pass->getCurrentAllocaPoint() != NULL) << F->getName();

  // Make sure that all the calls to llvm.gcroot() happen in the entry block.
  llvm::IRBuilder<> tmpBuilder(&entryBlock, pass->getCurrentAllocaPoint());
  llvm::Value* root = tmpBuilder.CreateBitCast(stackslot,
                         ptrTo(tmpBuilder.getInt8PtrTy()), "gcroot");

  llvm::Constant* llvm_gcroot = llvm::Intrinsic::getDeclaration(pass->mod,
                                               llvm::Intrinsic::gcroot);
  ASSERT(llvm_gcroot) << "unable to mark GC root, llvm.gcroot not found";
  tmpBuilder.CreateCall2(llvm_gcroot, root, meta);
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

llvm::Value* CodegenPass::markAsNeedingImplicitLoads(llvm::Value* v) {
  this->needsImplicitLoad.insert(v); return v;
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
  llvm::AllocaInst* stackslot = stackSlotWithValue(val, ".stackref");
  this->markAsNeedingImplicitLoads(stackslot);

  if (this->useGC) {
    markGCRoot(stackslot, this);
  }

  // Instead of returning the pointer (of type T*),
  // we return the stack slot (of type T**) so that copying GC will be able to
  // modify the stack slot effectively.
  return stackslot;
}


llvm::AllocaInst*
CodegenPass::emitMalloc(TypeAST* typ, int8_t ctorId, bool init) {
  llvm::Value* memalloc_cell = mod->getFunction("memalloc_cell");
  ASSERT(memalloc_cell != NULL) << "NO memalloc_cell IN MODULE! :(";

  llvm::Type* ty = typ->getLLVMType();
  llvm::GlobalVariable* ti = getTypeMapForType(ty, ctorId, mod, NotArray);
  ASSERT(ti != NULL) << "malloc must have type info for type " << str(ty)
                     << "; ctor id " << ctorId;
  llvm::Type* typemap_type = memalloc_cell->getType()
                                            ->getContainedType(0)
                                            ->getContainedType(1);
  llvm::Value* typemap = builder.CreateBitCast(ti, typemap_type);
  llvm::CallInst* mem = builder.CreateCall(memalloc_cell, typemap, "mem");

  if (init) {
    markAsNonAllocating(builder.CreateMemSet(mem, builder.getInt8(0),
                                                  slotSizeOf(ty), /*align*/ 4));
  }

  return storeAndMarkPointerAsGCRoot(
                       builder.CreateBitCast(mem, ptrTo(ty), "ptr"));
}


llvm::Value*
CodegenPass::emitArrayMalloc(TypeAST* elt_type, llvm::Value* n, bool init) {
  llvm::Type* elt_ty = elt_type->getLLVMType();
  llvm::Value* memalloc = mod->getFunction("memalloc_array");
  ASSERT(memalloc != NULL) << "NO memalloc_array IN MODULE! :(";

  int8_t ctorId = -1;
  // TODO this is bogus; we should have, at most, 3 flat array representations:
  // 1) (packed) non-struct POD
  // 2) GC-able pointers
  // 3) (maybe) unboxed structs, for types with a single ctor.
  llvm::GlobalVariable* ti = getTypeMapForType(elt_ty, ctorId, mod, YesArray);
  ASSERT(ti != NULL);
  llvm::Type* typemap_type = memalloc->getType() // function ptr
                                            ->getContainedType(0) // function
                                            ->getContainedType(1); // first arg
  llvm::Value* typemap = builder.CreateBitCast(ti, typemap_type);
  llvm::Value* num_elts = builder.CreateSExt(n, builder.getInt64Ty(), "ext");
  llvm::Value* vinit   = builder.getInt8(init);
  llvm::CallInst* mem = builder.CreateCall3(memalloc, typemap, num_elts, vinit, "arrmem");

  return storeAndMarkPointerAsGCRoot(
           builder.CreateBitCast(mem,
                  ArrayTypeAST::getZeroLengthTypeRef(elt_ty), "arr_ptr"));
}

llvm::Value*
CodegenPass::allocateMPInt() {
  llvm::Value* mp_int_alloc = mod->getFunction("mp_int_alloc");
  ASSERT(mp_int_alloc);
  return builder.CreateCall(mp_int_alloc);
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
createSqrt(IRBuilder<>& b, llvm::Value* v, const char* valname) {
  Type*  tys[] = { v->getType() };
  Module*    m = b.GetInsertBlock()->getParent()->getParent();
  // We need to resolve the overloaded "type" of the sqrt intrinsic.
  Value* sqrtv = llvm::Intrinsic::getDeclaration(m, llvm::Intrinsic::sqrt, tys);

  CallInst *CI = b.CreateCall(sqrtv, v, valname);
  //b.SetInstDebugLocation(CI);
  return CI;
}

llvm::Value*
CodegenPass::emitPrimitiveOperation(const std::string& op,
                                    IRBuilder<>& b,
                                    const std::vector<Value*>& args) {
  Value* VL = args[0];
       if (op == "negate") { return b.CreateNeg(VL, "negtmp", this->useNUW, this->useNSW); }
  else if (op == "bitnot") { return b.CreateNot(VL, "nottmp"); }
  else if (op == "sext_i64") { return b.CreateSExt(VL, b.getInt64Ty(), "sexti64tmp"); }
  else if (op == "sext_i32") { return b.CreateSExt(VL, b.getInt32Ty(), "sexti32tmp"); }
  else if (op == "trunc_i8") { return b.CreateTrunc(VL, b.getInt8Ty(), "trunci8tmp"); }
  else if (op == "fsqrt")    { return createSqrt(b, VL, "fsqrttmp"); }

  Value* VR = args[1];
  // Other variants: F (float), NSW (no signed wrap), NUW,
  // UDiv, ExactSDiv, URem, SRem,
       if (op == "+") { return b.CreateAdd(VL, VR, "addtmp", this->useNUW, this->useNSW); }
  else if (op == "-") { return b.CreateSub(VL, VR, "subtmp", this->useNUW, this->useNSW); }
  else if (op == "/") { return b.CreateSDiv(VL, VR, "divtmp"); }
  else if (op == "*") { return b.CreateMul(VL, VR, "multmp", this->useNUW, this->useNSW); }
  else if (op == "srem") { return b.CreateSRem(VL, VR, "sremtmp"); }
  else if (op == "urem") { return b.CreateURem(VL, VR, "uremtmp"); }
  else if (op == "frem") { return b.CreateFRem(VL, VR, "fremtmp"); }
  else if (op == "f+") { return b.CreateFAdd(VL, VR, "faddtmp"); }
  else if (op == "f-") { return b.CreateFSub(VL, VR, "fsubtmp"); }
  else if (op == "fdiv"){return b.CreateFDiv(VL, VR, "fdivtmp"); }
  else if (op == "f*") { return b.CreateFMul(VL, VR, "fmultmp"); }

  // Also have unsigned variants (TODO)
  else if (op == "<")  { return b.CreateICmpSLT(VL, VR, "slttmp"); }
  else if (op == "<=") { return b.CreateICmpSLE(VL, VR, "sletmp"); }
  else if (op == ">")  { return b.CreateICmpSGT(VL, VR, "sgttmp"); }
  else if (op == ">=") { return b.CreateICmpSGE(VL, VR, "sgetmp"); }
  else if (op == "==") { return b.CreateICmpEQ(VL, VR, "eqtmp"); }
  else if (op == "!=") { return b.CreateICmpNE(VL, VR, "netmp"); }
  // Use unordered (U) variants because we don't analyze for QNANs.
  else if (op == "f<")  { return b.CreateFCmpULT(VL, VR, "fulttmp"); }
  else if (op == "f<=") { return b.CreateFCmpULE(VL, VR, "fuletmp"); }
  else if (op == "f>")  { return b.CreateFCmpUGT(VL, VR, "fugttmp"); }
  else if (op == "f>=") { return b.CreateFCmpUGE(VL, VR, "fugetmp"); }
  else if (op == "f==") { return b.CreateFCmpUEQ(VL, VR, "fueqtmp"); }
  else if (op == "f!=") { return b.CreateFCmpUNE(VL, VR, "funetmp"); }
  // TODO: ORD = no nans, UNO = either nans

  else if (op == "bitand") { return b.CreateAnd(VL, VR, "bitandtmp"); }
  else if (op == "bitor") {  return b.CreateOr( VL, VR, "bitortmp"); }
  else if (op == "bitxor") { return b.CreateXor(VL, VR, "bitxortmp"); }

  else if (op == "bitshl")  { return b.CreateShl(VL,  getMaskedForShift(b, VL, VR), "shltmp", this->useNUW, this->useNSW); }
  else if (op == "bitlshr") { return b.CreateLShr(VL, getMaskedForShift(b, VL, VR), "lshrtmp"); }
  else if (op == "bitashr") { return b.CreateAShr(VL, getMaskedForShift(b, VL, VR), "ashrtmp"); }

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
      this->name            = "foster_emit_string_of_cstring";
      this->argnames.push_back("buf");
      this->argnames.push_back("len");
      std::vector<TypeAST*> argTypes;
      argTypes.push_back(RefTypeAST::get(TypeAST::i(8)));
      argTypes.push_back(TypeAST::i(32));
      std::map<std::string, std::string> annots; annots["callconv"] = "ccc";
      this->type            = new FnTypeAST(RefTypeAST::get(TypeAST::i(999)),
                                            argTypes, annots);
      this->type->markAsProc();
  }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) {
    Function::arg_iterator AI = F->arg_begin();
    Value* cstr = AI++;
    Value* sz   = AI++;
    Value* str = pass->emitFosterStringOfCString(cstr, sz);
    builder.CreateRet(str);
  }
};

void extendWithImplementationSpecificProcs(CodegenPass* _pass,
                                           std::vector<LLProc*>& procs) {
  // This function is useful to the runtime (and should therefore
  // be generated with external linkage and C calling convention)
  // but involves code most easily generated by the compiler.
  procs.push_back(new LLProcStringOfCStringPrim());
}
