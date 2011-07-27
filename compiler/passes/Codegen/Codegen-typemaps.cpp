// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterUtils.h"
#include "parse/ParsingContext.h"
#include "parse/FosterTypeAST.h"

#include "llvm/DerivedTypes.h"
#include "llvm/InstrTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/ADT/VectorExtras.h"

#include <map>
#include <set>
#include <vector>

#include "pystring/pystring.h"

#include "passes/CodegenPass-impl.h"

using namespace llvm;

using foster::EDiag;
using foster::builder;
using foster::ParsingContext;

llvm::GlobalVariable* getTypeMapForType(const llvm::Type*, llvm::Module*, ArrayOrNot);

typedef Constant*   Offset;
typedef std::vector<Offset> OffsetSet;

bool isGarbageCollectible(const Type* ty) {
  // For now, we don't distinguish between different kinds of pointer;
  // we consider any pointer to be a possible heap pointer.
  return ty->isPointerTy() && ty->getContainedType(0)->isSized();
}

OffsetSet countPointersInType(const Type* ty) {
  ASSERT(ty) << "Can't count pointers in a NULL type!";

  OffsetSet rv;
  if (isGarbageCollectible(ty)) {
    // Pointers to functions/labels/other non-sized types do not get GC'd.
    rv.push_back(getConstantInt64For(0));
  }

  // array, struct, union
  else if (dyn_cast<const ArrayType>(ty)) {
    // TODO need to decide how Foster semantics will map to LLVM IR for arrays.
    // Will EVERY (C++), SOME (Factor, C#?), or NO (Java) types be unboxed?
    // Also need to figure out how the gc will collect arrays.
    //return aty->getNumElements() * countPointersInType(aty->getElementType());
  }

  // if we have a struct { T1; T2 } then our offset set will be the set for T1,
  // plus the set for T2 with offsets incremented by the offset of T2.
  else if (const StructType* sty = dyn_cast<StructType>(ty)) {
    for (size_t i = 0; i < sty->getNumElements(); ++i) {
      Constant* slotOffset = ConstantExpr::getOffsetOf(sty, i);
      OffsetSet sub = countPointersInType(sty->getTypeAtIndex(i));
      for (OffsetSet::iterator si = sub.begin(); si != sub.end(); ++si) {
        Offset suboffset = *si;
        rv.push_back(ConstantExpr::getAdd(suboffset, slotOffset));
      }
    }
  }

  // TODO Also need to decide how to represent type maps for unions
  // in such a way that the GC can safely collect unions.

  // Note! Now that LLVM has removed IR support for unions, codegen
  // will require a Foster TypeAST*, not just a Type*,
  // in order to properly codegen unions.

  // all other types do not contain pointers
  return rv;
}

bool mightContainHeapPointers(const llvm::Type* ty) {
  OffsetSet offsets = countPointersInType(ty);
  return !offsets.empty();
}

const Type* getHeapCellHeaderTy() {
  return builder.getInt64Ty();
}

// Rounds up to nearest multiple of the given power of two.
Constant* roundUpToNearestMultiple(Constant* v, Constant* powerOf2) {
  Constant* mask = ConstantExpr::getSub(powerOf2, getConstantInt64For(1));
  // Compute the value of      let m = p - 1 in ((v + m) & ~m)
  return ConstantExpr::getAnd(
           ConstantExpr::getAdd(v, mask),
           ConstantExpr::getNot(mask));
}

Constant* defaultHeapAlignment() {
  return getConstantInt64For(16);
}

// Returns the smallest multiple of the default heap alignment
// which is larger than the size of the given type plus the heap header size.
Constant* cellSizeOf(const Type* ty) {
  Constant* sz = ConstantExpr::getSizeOf(ty);
  Constant* hs = ConstantExpr::getSizeOf(getHeapCellHeaderTy());
  Constant* cs = ConstantExpr::getAdd(sz, hs);
  return roundUpToNearestMultiple(cs, defaultHeapAlignment());
}

typedef std::pair<const Type*, std::pair<ArrayOrNot, int8_t> > TypeSig;
TypeSig mkTypeSig(const Type* t, ArrayOrNot a, int8_t c) {
  return std::make_pair(t, std::make_pair(a, c));
}

std::map<TypeSig, GlobalVariable*> typeMapCache;

const Type* getTypeMapOffsetType() {
  return builder.getInt32Ty();
}

// Keep synchronized with runtime/gc/foster_gc_utils.h
// struct {
//   i64         cellSize;
//   i8*         typeName;
//   i32         numPtrEntries;
//   i8          ctorId;
//   i8          isCoro;
//   i8          isArray;
//   i8          unused_padding;
//   i32         offsets[numPtrEntries];
// }
const StructType* getTypeMapType(int numPointers) {
  ArrayType* offsetsTy = ArrayType::get(getTypeMapOffsetType(), numPointers);

  std::vector<const Type*> typeMapTyFields;
  typeMapTyFields.push_back(builder.getInt64Ty());   // cellSize
  typeMapTyFields.push_back(builder.getInt8PtrTy()); // typeName
  typeMapTyFields.push_back(builder.getInt32Ty());   // numPtrEntries
  typeMapTyFields.push_back(builder.getInt8Ty());    // ctorId
  typeMapTyFields.push_back(builder.getInt8Ty());    // isCoro
  typeMapTyFields.push_back(builder.getInt8Ty());    // isArray
  typeMapTyFields.push_back(builder.getInt8Ty());    // unused_padding
  typeMapTyFields.push_back(offsetsTy);              // i32[n]

  return StructType::get(getGlobalContext(), typeMapTyFields);
}

// Return a global corresponding to layout of getTypeMapType()
// The returned global is also stored in the typeMapForType[] map.
GlobalVariable* constructTypeMap(const llvm::Type*  ty,
                                 const std::string& name,
                                 const OffsetSet&   pointerOffsets,
                                 ArrayOrNot         arrayStatus,
                                 int8_t             ctorId,
                                 llvm::Module*      mod) {
  int numPointers = pointerOffsets.size();
  const StructType* typeMapTy = getTypeMapType(numPointers);

  GlobalVariable* typeMapVar = new GlobalVariable(
    /*Module=*/     *mod,
    /*Type=*/       typeMapTy,
    /*isConstant=*/ false,
    /*Linkage=*/    GlobalValue::ExternalLinkage,
    /*Initializer=*/ 0,
    /*Name=*/        "__foster_typemap_" + name,
    /*ThreadLocal=*/ false);
  typeMapVar->setAlignment(16);

  std::string wrapped;
  raw_string_ostream ss(wrapped); ss << name << " = " << *ty;
  Constant* cname = ConstantArray::get(getGlobalContext(),
                                       ss.str().c_str(),
                                       true);
  GlobalVariable* typeNameVar = new GlobalVariable(
      /*Module=*/      *mod,
      /*Type=*/        cname->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     GlobalValue::PrivateLinkage,
      /*Initializer=*/ cname,
      /*Name=*/        ".typename." + name);
  typeNameVar->setAlignment(1);


  std::vector<Constant*> typeMapOffsets;
  for (OffsetSet::const_iterator it =  pointerOffsets.begin();
                                 it != pointerOffsets.end(); ++it) {
    typeMapOffsets.push_back(ConstantExpr::getTruncOrBitCast(
                                     *it, builder.getInt32Ty()));
  }

  bool isCoro = pystring::startswith(name, "coro_");
  bool isArray = arrayStatus == YesArray;
  ArrayType* offsetsTy = ArrayType::get(getTypeMapOffsetType(), numPointers);

  // Construct the type map itself
  std::vector<Constant*> typeMapFields;
  typeMapFields.push_back(cellSizeOf(ty));
  typeMapFields.push_back(arrayVariableToPointer(typeNameVar));
  typeMapFields.push_back(getConstantInt32For(numPointers));
  typeMapFields.push_back(getConstantInt8For(ctorId));
  typeMapFields.push_back(getConstantInt8For(isCoro ? 1 : 0));
  typeMapFields.push_back(getConstantInt8For(isArray ? 1 : 0));
  typeMapFields.push_back(getConstantInt8For(0)); // unused padding
  typeMapFields.push_back(ConstantArray::get(offsetsTy, typeMapOffsets));

  typeMapVar->setInitializer(ConstantStruct::get(typeMapTy, typeMapFields));
  return typeMapVar;
}

// Computes the offsets of all pointers in the given type,
// and constructs a type map using those offsets.
GlobalVariable* emitTypeMap(
    const Type* ty,
    std::string name,
    ArrayOrNot arrayStatus,
    int8_t        ctorId,
    llvm::Module* mod,
    std::vector<int> skippedIndexVector) {
  // Careful! The indices here are relative to the values
  // returend by countPointersInType(), not the indicies
  // in the type of those pointers.
  std::set<int> skippedOffsets(skippedIndexVector.begin(),
                               skippedIndexVector.end());
  for(size_t i = 0; i < skippedIndexVector.size(); ++i) {
    EDiag() << "plan to skip index " << skippedIndexVector[i];
  }
  OffsetSet filteredOffsets;
  OffsetSet pointerOffsets = countPointersInType(ty);
  for(size_t i = 0; i < pointerOffsets.size(); ++i) {
    if (skippedOffsets.count(i) == 0) {
      filteredOffsets.push_back(pointerOffsets[i]);
    }
  }

  TypeSig sig = mkTypeSig(ty, arrayStatus, ctorId);
  typeMapCache[sig] = constructTypeMap(ty, name, filteredOffsets, arrayStatus, ctorId, mod);
  return typeMapCache[sig];
}

// The struct type is
// { { { i8** }, \2*, void (i8*)*, i8*, \2*, i32 }, i32 }
// {
//   { <coro_context>           0
//   , sibling         <---    [1]
//   , fn
//   , env             <---    (2)
//   , invoker         <---    [3]
//   , indirect_self            4
//   , status
//   }
//   argty
// }
GlobalVariable* emitCoroTypeMap(const StructType* sty, llvm::Module* mod) {
  bool hasKnownTypes = sty->getNumElements() == 2;
  if (!hasKnownTypes) {
    // Generic coro; don't generate a typemap,
    // because it will be the wrong size at runtime!
    return NULL;
  }

  std::string sname;
  llvm::raw_string_ostream ss(sname);
  ss << "coro_" << *(sty->getTypeAtIndex(1));

  // We skip the first entry, which is the stack pointer in the coro_context.
  // The pointer-to-function will be automatically skipped, and the remaining
  // pointers are precisely those which we want the GC to notice.
  int8_t bogusCtor = -1;
  return emitTypeMap(sty, ss.str(), NotArray, bogusCtor, mod,
                     make_vector(0, 4, NULL));
}

void registerTupleType(TupleTypeAST* tupletyp,
                       std::string desiredName,
                       int8_t        ctorId,
                       llvm::Module* mod) {
  static std::map<TypeSig, bool> registeredTypes;

  const llvm::Type* ty = tupletyp->getLLVMTypeUnboxed();
  TypeSig sig = mkTypeSig(ty, NotArray, ctorId);
  if (registeredTypes[sig]) return;

  registeredTypes[sig] = true;

  std::string name = ParsingContext::freshName(desiredName);
  mod->addTypeName(name, ty);
  EDiag() << "registered type " << name << " = " << str(ty) << "; ctor id " << ctorId;
  emitTypeMap(ty, name, NotArray, ctorId, mod, std::vector<int>());
}

const llvm::StructType*
isCoroStruct(const llvm::Type* ty) {
  if (const llvm::StructType* sty = llvm::dyn_cast<llvm::StructType>(ty)) {
    if (sty == foster_generic_coro_t
     ||  ( sty->getNumContainedTypes() > 0
        && sty->getTypeAtIndex(0U) == foster_generic_coro_t)) {
      return sty;
    }
  }
  return NULL;
}

llvm::GlobalVariable* getTypeMapForType(const llvm::Type* ty,
                                        int8_t ctorId,
                                        llvm::Module* mod,
                                        ArrayOrNot arrayStatus) {
  llvm::GlobalVariable* gv = typeMapCache[mkTypeSig(ty, arrayStatus, ctorId)];
  if (gv) return gv;

  if (const llvm::StructType* sty = isCoroStruct(ty)) {
    gv = emitCoroTypeMap(sty, mod);
  } else if (!ty->isAbstract() && !ty->isAggregateType()) {
    gv = emitTypeMap(ty, ParsingContext::freshName("gcatom"), arrayStatus,
                     ctorId, mod, std::vector<int>());
    // emitTypeMap also sticks gv in typeMapForType
  } else if (isGenericClosureType(ty)) {
    gv = emitTypeMap(ty, ParsingContext::freshName("genericClosure"), arrayStatus,
                     ctorId, mod, std::vector<int>());
  }

  if (!gv) {
    foster::currentOuts() << "No type map for type " << (*ty) << "\n"
        << "\tfoster_generic_coro_t is " << *foster_generic_coro_t << "\n";
  }

  return gv;
}

