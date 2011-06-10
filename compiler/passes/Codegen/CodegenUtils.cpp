// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "passes/CodegenPass-impl.h"

#include "llvm/Intrinsics.h"
#include "llvm/LLVMContext.h"

#include <string>

using namespace llvm;

using foster::EDiag;
using foster::builder;

////////////////////////////////////////////////////////////////////

void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr) {
  Value* fosterAssert = mod->getFunction("foster__assert");
  ASSERT(fosterAssert != NULL);

  Value* msg_array = builder.CreateGlobalString(cstr);
  Value* msg = builder.CreateBitCast(msg_array, builder.getInt8PtrTy());
  builder.CreateCall2(fosterAssert, cond, msg);
}

llvm::Value* getUnitValue() {
  std::vector<llvm::Constant*> noArgs;
  return llvm::ConstantStruct::get(
            llvm::StructType::get(builder.getContext()), noArgs);
}

void checkPointerToIndex(Value* ptrToCompositeValue,
                         Value* idxValue,
                         const std::string& name) {
  ASSERT(ptrToCompositeValue->getType()->isPointerTy());
  const llvm::Type* underlyingTy = ptrToCompositeValue->getType()->getContainedType(0);
  if (const llvm::CompositeType* cty
      = llvm::dyn_cast<llvm::CompositeType>(underlyingTy)) {
    ASSERT(cty->indexValid(idxValue))
      << "Attempt to use index " << str(idxValue)
      << "\non val of type "     << str(ptrToCompositeValue->getType())
      << "\nwith value "         << str(ptrToCompositeValue);
      llvm::outs() << "gep " << str(ptrToCompositeValue->getType())
                    << "  of type " << str(idxValue) << "\n";
  } else {
    ASSERT(false) << "Pointer to non-composite type "
                  <<  str(ptrToCompositeValue->getType())
                  << "passed to getPointerToIndex(... " << name << ")";
  }
}

Value* getPointerToIndex(Value* ptrToCompositeValue,
                         Value* idxValue,
                         const std::string& name) {
  checkPointerToIndex(ptrToCompositeValue, idxValue, name);
  std::vector<Value*> idx;
  idx.push_back(getConstantInt32For(0));
  idx.push_back(idxValue);
  return builder.CreateGEP(ptrToCompositeValue,
                           idx.begin(), idx.end(), name.c_str());
}

uint64_t getSaturating(const llvm::ConstantInt* ci) {
  typedef uint64_t T;
  // If the value requires more bits than T can represent, we want
  // to return ~0, not 0. Otherwise, we should leave the value alone.
  T allOnes = ~T(0);
  if (!ci) {
    EDiag() << "getSaturating() given a null value, returning " << allOnes;
    return allOnes;
  }

  return static_cast<T>(ci->getLimitedValue(allOnes));
}

Value* getElementFromComposite(Value* compositeValue, Value* idxValue,
                               const std::string& msg) {
  const Type* compositeType = compositeValue->getType();
  if (llvm::isa<llvm::PointerType>(compositeType)) {
    // Pointers to composites are indexed via getelementptr
    // TODO: "When indexing into a (optionally packed) structure,
    //        only i32 integer constants are allowed. When indexing
    //        into an array, pointer or vector, integers of any width
    //        are allowed, and they are not required to be constant."
    //   -- http://llvm.org/docs/LangRef.html#i_getelementptr
    Value* gep = getPointerToIndex(compositeValue, idxValue, (msg + ".subgep").c_str());
    return builder.CreateLoad(gep, "subgep_ld");
  } else if (llvm::isa<llvm::StructType>(compositeType)
          && llvm::isa<llvm::Constant>(idxValue)) {
    ASSERT(llvm::isa<llvm::ConstantInt>(idxValue))
        << "struct values may be indexed only by constant expressions";
    unsigned uidx = unsigned(getSaturating(dyn_cast<ConstantInt>(idxValue)));
    return builder.CreateExtractValue(compositeValue, uidx, (msg + "subexv").c_str());
  } else if (llvm::isa<llvm::VectorType>(compositeType)) {
    if (llvm::isa<llvm::Constant>(idxValue)) {
      return builder.CreateExtractElement(compositeValue, idxValue, (msg + "simdexv").c_str());
    } else {
      EDiag() << "TODO: codegen for indexing vectors by non-constants"
              << __FILE__ << ":" << __LINE__ << "\n";
    }
  } else {
    EDiag() << "Cannot index into value type " << str(compositeType)
            << " with non-constant index " << str(idxValue);
  }
  return NULL;
}

////////////////////////////////////////////////////////////////////

// root should be an AllocaInst or a bitcast of such
void markGCRoot(llvm::Value* root,
                llvm::Constant* meta,
                llvm::Module* mod) {
  llvm::Constant* llvm_gcroot = llvm::Intrinsic::getDeclaration(mod,
                                               llvm::Intrinsic::gcroot);

  ASSERT(llvm_gcroot) << "unable to mark GC root, llvm.gcroot not found";

  // If we don't have something more specific, try using
  // the lowered type's type map.
  if (!meta) {
    meta = getTypeMapForType(root->getType(), mod);
  }

  if (!meta) {
    // If we don't have a type map, use a NULL pointer.
    meta = llvm::ConstantPointerNull::get(builder.getInt8PtrTy());
  } else if (meta->getType() != builder.getInt8PtrTy()) {
    // If we do have a type map, make sure it's of type i8*.
    meta = ConstantExpr::getBitCast(meta, builder.getInt8PtrTy());
  }

  llvm::Value* const vmeta = meta;
  llvm::MDNode* metamdnode =
            llvm::MDNode::get(builder.getContext(), &vmeta, 1);
  llvm::Instruction* rootinst = llvm::dyn_cast<llvm::Instruction>(root);
  if (!rootinst) {
    llvm::outs() << "root kind is " << llvmValueTag(root) << "\n";
    ASSERT(false) << "need inst!";
  }
  rootinst->setMetadata("fostergcroot", metamdnode);

  builder.CreateCall2(llvm_gcroot, root, meta);
}


// Creates an AllocaInst in the entry block of the current function,
// so that mem2reg will be able to optimize loads and stores from the alloca.
// Code from the Kaleidoscope tutorial on mutable variables,
// http://llvm.org/docs/tutorial/LangImpl7.html
llvm::AllocaInst* CreateEntryAlloca(const llvm::Type* ty, const std::string& name) {
  llvm::BasicBlock& entryBlock =
      builder.GetInsertBlock()->getParent()->getEntryBlock();
  llvm::IRBuilder<> tmpBuilder(&entryBlock, entryBlock.begin());
  return tmpBuilder.CreateAlloca(ty, /*ArraySize=*/ 0, name);
}

llvm::AllocaInst* stackSlotWithValue(llvm::Value* val, const std::string& name) {
  llvm::AllocaInst* valptr = CreateEntryAlloca(val->getType(), name);
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
llvm::Value* storeAndMarkPointerAsGCRoot(llvm::Value* val,
                                         llvm::Module* mod) {
  if (!val->getType()->isPointerTy()) {
     llvm::AllocaInst* valptr = stackSlotWithValue(val, "ptrfromnonptr");
     val = valptr;
     // We end up with a stack slot pointing to a stack slot, rather than
     // a stack slot pointing to a heap-allocated block.
     // The garbage collector detects this and skips collection.
  }

  // val now has pointer type.

  // allocate a slot for a T* on the stack
  llvm::AllocaInst* stackslot = CreateEntryAlloca(val->getType(), "stackref");
  llvm::Value* root = builder.CreateBitCast(stackslot,
                                      ptrTo(builder.getInt8PtrTy()), "gcroot");

  markGCRoot(root, getTypeMapForType(val->getType()->getContainedType(0), mod),
             mod);
  builder.CreateStore(val, stackslot, /*isVolatile=*/ false);

  // Instead of returning the pointer (of type T*),
  // we return the stack slot (of type T**) so that copying GC will be able to
  // modify the stack slot effectively.
  return stackslot;
}


llvm::Value*
CodegenPass::emitMalloc(const llvm::Type* ty) {
  llvm::Value* memalloc_cell = mod->getFunction("memalloc_cell");
  ASSERT(memalloc_cell != NULL) << "NO memalloc_cell IN MODULE! :(";

  llvm::GlobalVariable* ti = getTypeMapForType(ty, mod);
  ASSERT(ti != NULL);
  const llvm::Type* typemap_type = memalloc_cell->getType()
                                            ->getContainedType(0)
                                            ->getContainedType(1);
  llvm::Value* typemap = builder.CreateBitCast(ti, typemap_type);
  llvm::CallInst* mem = builder.CreateCall(memalloc_cell, typemap, "mem");

  return storeAndMarkPointerAsGCRoot(
                       builder.CreateBitCast(mem, ptrTo(ty), "ptr"),
                       mod);
}

llvm::Value*
CodegenPass::allocateMPInt() {
  llvm::Value* mp_int_alloc = mod->getFunction("mp_int_alloc");
  ASSERT(mp_int_alloc);
  return builder.CreateCall(mp_int_alloc);
}

