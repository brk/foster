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

llvm::Value* getUnitValue() {
  std::vector<llvm::Constant*> noArgs;
  return llvm::ConstantStruct::get(
            llvm::StructType::get(builder.getContext()), noArgs);
}

Value* getPointerToIndex(Value* compositeValue,
                         Value* idxValue,
                         const std::string& name) {
  std::vector<Value*> idx;
  idx.push_back(ConstantInt::get(Type::getInt32Ty(builder.getContext()), 0));
  idx.push_back(idxValue);
  return builder.CreateGEP(compositeValue, idx.begin(), idx.end(), name.c_str());
}

Value* getElementFromComposite(Value* compositeValue, Value* idxValue) {
  const Type* compositeType = compositeValue->getType();
  if (llvm::isa<llvm::PointerType>(compositeType)) {
    // Pointers to composites are indexed via getelementptr
    // TODO: "When indexing into a (optionally packed) structure,
    //        only i32 integer constants are allowed. When indexing
    //        into an array, pointer or vector, integers of any width
    //        are allowed, and they are not required to be constant."
    //   -- http://llvm.org/docs/LangRef.html#i_getelementptr
    Value* gep = getPointerToIndex(compositeValue, idxValue, "subgep");
    return builder.CreateLoad(gep, "subgep_ld");
  } else if (llvm::isa<llvm::StructType>(compositeType)
          && llvm::isa<llvm::Constant>(idxValue)) {
    // Struct values may be indexed only by constant expressions
    ASSERT(llvm::isa<llvm::ConstantInt>(idxValue));
    unsigned uidx = unsigned(getSaturating(dyn_cast<ConstantInt>(idxValue)));
    return builder.CreateExtractValue(compositeValue, uidx, "subexv");
  } else if (llvm::isa<llvm::VectorType>(compositeType)) {
    if (llvm::isa<llvm::Constant>(idxValue)) {
      return builder.CreateExtractElement(compositeValue, idxValue, "simdexv");
    } else {
      EDiag() << "TODO: codegen for indexing vectors by non-constants"
              << __FILE__ << ":" << __LINE__ << "\n";
    }
  } else {
    llvm::errs() << "Cannot index into value type " << *compositeType
                 << " with non-constant index " << *idxValue << "\n";
  }
  return NULL;
}

////////////////////////////////////////////////////////////////////

// If the provided root is an alloca, return it directly;
// if it's a bitcast, return the first arg bitcast to alloca (or NULL);
// otherwise, die.
llvm::AllocaInst* getAllocaForRoot(llvm::Instruction* root) {
  if (llvm::AllocaInst* ai = llvm::dyn_cast<llvm::AllocaInst>(root)) {
    return ai;
  }

  if (llvm::BitCastInst* bi = llvm::dyn_cast<llvm::BitCastInst>(root)) {
    llvm::Value* op = *(bi->op_begin());
    return llvm::cast<llvm::AllocaInst>(op);
  }

  ASSERT(false) << "root must be alloca or bitcast of alloca!";
  return NULL;
}


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
  llvm::AllocaInst* allocainst = getAllocaForRoot(rootinst);
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

