// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterUtils.h"
#include "parse/ParsingContext.h"

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

typedef std::pair<const Type*, Constant*> OffsetInfo;
typedef std::vector<OffsetInfo> OffsetSet;

// Converts a global variable of type [_ x T] to a local var of type T*.
Constant* arrayVariableToPointer(GlobalVariable* arr) {
  std::vector<Constant*> idx;
  idx.push_back(getConstantInt64For(0));
  idx.push_back(getConstantInt64For(0));
  return ConstantExpr::getGetElementPtr(arr, &idx[0], idx.size());
}

OffsetSet countPointersInType(const Type* ty) {
  ASSERT(ty) << "Can't count pointers in a NULL type!";

  OffsetSet rv;
  if (ty->isPointerTy()
    && ty->getContainedType(0)->isSized()) {
    // Pointers to functions/labels/other non-sized types do not get GC'd.
    rv.push_back(OffsetInfo(ty->getContainedType(0),
                         getConstantInt64For(0)));
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
        const Type* subty = si->first;
        Constant* suboffset = si->second;
        rv.push_back(OffsetInfo(subty,
            ConstantExpr::getAdd(suboffset, slotOffset)));
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
  // For now, we don't distinguish between different kinds of pointer;
  // we consider any pointer to be a possible heap pointer.
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

std::map<const Type*, GlobalVariable*> typeMapForType;

// %typemap_entry = type { i8*, i32 }
const StructType* getTypeMapEntryType(llvm::Module* mod) {
  const StructType* entryty = dyn_cast_or_null<StructType>(
                                mod->getTypeByName("typemap_entry"));
  if (!entryty) {
    std::vector<const Type*> entryty_types;
    entryty_types.push_back(builder.getInt8PtrTy()); // typeinfo
    entryty_types.push_back(builder.getInt32Ty());   // offset
    entryty = StructType::get(getGlobalContext(), entryty_types,
                                          /*isPacked=*/false);
    mod->addTypeName("typemap_entry", entryty);
  }
  return entryty;
}

// A type map entry is a pair:
//  struct { i8* typeinfo; i32 offset }
//
// The |offset| field is the offset of a slot in the parent type.
// The |typeinfo| field is either a pointer to a typemap describing
// the slot, or (for atomic types) the size of the cell.
//
// We can distinguish the two cases at runtime since only arrays
// can lead to objects of any significant (multi-KB) size.
Constant* getTypeMapEntryFor(const Type* entryTy,
                             Constant*   offset,
                             ArrayOrNot  arrayStatus,
                             llvm::Module* mod) {
  std::vector<Constant*> fields;

  GlobalVariable* typeMapVar = getTypeMapForType(entryTy, mod, arrayStatus);

  // Get the type map or (if no pointers) body size, cast to an i8*.
  if (typeMapVar) {
        fields.push_back(ConstantExpr::getCast(Instruction::BitCast,
                        typeMapVar, builder.getInt8PtrTy()));
  } else {
        // If we can't tell the garbage collector how to collect a type by
        // giving it a pointer to a type map, it's probably because the type
        // doesn't have a type map, i.e. the type is atomic. Instead, tell
        // the garbage collector how large the type is.
        fields.push_back(
            ConstantExpr::getCast(Instruction::IntToPtr,
                                  cellSizeOf(entryTy),
                                  builder.getInt8PtrTy()));
  }

  // Convert the Constant* offset to an i32.
  fields.push_back(ConstantExpr::getTruncOrBitCast(
                   offset, builder.getInt32Ty()));

  return ConstantStruct::get(getTypeMapEntryType(mod), fields);
}

// Keep synchronized with runtime/gc/foster_gc.cpp
// struct {
//   i64         cellSize;
//   i8*         typeName;
//   i32         numPtrEntries;
//   i8          isCoro;
//   i8          isArray;
//   struct { i8* typeinfo; i32 offset }[numPtrEntries];
// }
const StructType* getTypeMapType(int numPointers, llvm::Module* mod) {
  ArrayType* entriesty = ArrayType::get(getTypeMapEntryType(mod), numPointers);

  std::vector<const Type*> typeMapTyFields;
  typeMapTyFields.push_back(builder.getInt64Ty()); // cellSize
  typeMapTyFields.push_back(builder.getInt8PtrTy()); // typeName
  typeMapTyFields.push_back(builder.getInt32Ty()); // numPtrEntries
  typeMapTyFields.push_back(builder.getInt8Ty()); // isCoro
  typeMapTyFields.push_back(builder.getInt8Ty()); // isArray
  typeMapTyFields.push_back(entriesty); // { i8*, i32 }[n]

  return StructType::get(getGlobalContext(), typeMapTyFields);
}

// Return a global corresponding to layout of getTypeMapType()
// The returned global is also stored in the typeMapForType[] map.
GlobalVariable* constructTypeMap(const llvm::Type* ty,
                                 const std::string& name,
                                 const OffsetSet& pointerOffsets,
                                 ArrayOrNot arrayStatus,
                                 llvm::Module* mod) {
  int numPointers = pointerOffsets.size();
  const StructType* typeMapTy = getTypeMapType(numPointers, mod);

  GlobalVariable* typeMapVar = new GlobalVariable(
    /*Module=*/     *mod,
    /*Type=*/       typeMapTy,
    /*isConstant=*/ false,
    /*Linkage=*/    GlobalValue::ExternalLinkage,
    /*Initializer=*/ 0,
    /*Name=*/        "__foster_typemap_" + name,
    /*ThreadLocal=*/ false);
  typeMapVar->setAlignment(16);

  // Register the (as-yet uninitialized) variable to avoid problems
  // with recursive types.
  typeMapForType[ty] = typeMapVar;

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


  std::vector<Constant*> typeMapEntries;
  for (OffsetSet::const_iterator si =  pointerOffsets.begin();
                                 si != pointerOffsets.end(); ++si) {
    const Type* subty = si->first;
    Constant* suboffset = si->second;
    typeMapEntries.push_back(getTypeMapEntryFor(subty, suboffset, arrayStatus, mod));
  }

  bool isCoro = pystring::startswith(name, "coro_");
  bool isArray = arrayStatus == YesArray;

  // Construct the type map itself
  std::vector<Constant*> typeMapFields;
  typeMapFields.push_back(cellSizeOf(ty));
  typeMapFields.push_back(arrayVariableToPointer(typeNameVar));
  typeMapFields.push_back(getConstantInt32For(numPointers));
  typeMapFields.push_back(getConstantInt8For(isCoro ? 1 : 0));
  typeMapFields.push_back(getConstantInt8For(isArray ? 1 : 0));
  typeMapFields.push_back(
         ConstantArray::get(
                ArrayType::get(getTypeMapEntryType(mod), numPointers),
                typeMapEntries));

  typeMapVar->setInitializer(
        ConstantStruct::get(typeMapTy, typeMapFields));
  return typeMapVar;
}

// Computes the offsets of all pointers in the given type,
// and constructs a type map using those offsets.
GlobalVariable* emitTypeMap(
    const Type* ty,
    std::string name,
    ArrayOrNot arrayStatus,
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
      EDiag() << "adding pointer offset " << i;
      filteredOffsets.push_back(pointerOffsets[i]);
    } else {
      EDiag() << "skipping pointer offset " << i;
    }
  }

  return constructTypeMap(ty, name, filteredOffsets, arrayStatus, mod);
}

// The struct type is
// { { { i8** }, \2*, void (i8*)*, i8*, \2*, i32 }, i32 }
// {
//   { <coro_context>           0
//   , sibling         <---    (1)
//   , fn
//   , env             <---    (2)
//   , invoker         <---    (3)
//   , indirect_self            4
//   , status
//   }
//   argty
// }
GlobalVariable* emitCoroTypeMap(const StructType* sty, llvm::Module* mod) {
  std::string sname;
  llvm::raw_string_ostream ss(sname); ss << "coro_";
  bool hasKnownTypes = sty->getNumElements() == 2;
  if (hasKnownTypes) {
    ss << *(sty->getTypeAtIndex(1));
  } else {
    ss << "gen";
  }

  // We skip the first entry, which is the stack pointer in the coro_context.
  // The pointer-to-function will be automatically skipped, and the remaining
  // pointers are precisely those which we want the GC to notice.
  return emitTypeMap(sty, ss.str(), NotArray, mod, make_vector(0, 4, NULL));
}

void registerType(const Type* ty,
                  std::string desiredName,
                  llvm::Module* mod,
                  ArrayOrNot arrayStatus,
                  bool isClosureEnvironment) {
  static std::map<const Type*, bool> registeredTypes;

  if (registeredTypes[ty]) return;

  registeredTypes[ty] = true;

  std::string name = ParsingContext::freshName(desiredName);
  mod->addTypeName(name, ty);

  std::vector<int> skipOffsets;
  if (isClosureEnvironment) {
    skipOffsets.push_back(0);
  }
  emitTypeMap(ty, name, arrayStatus, mod, skipOffsets);
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
                                        llvm::Module* mod,
                                        ArrayOrNot arrayStatus) {
  llvm::GlobalVariable* gv = typeMapForType[ty];
  if (gv) return gv;

  if (const llvm::StructType* sty = isCoroStruct(ty)) {
    gv = emitCoroTypeMap(sty, mod);
  } else if (!ty->isAbstract() && !ty->isAggregateType()) {
    gv = emitTypeMap(ty, ParsingContext::freshName("gcatom"), arrayStatus, mod,
                     std::vector<int>());
    // emitTypeMap also sticks gv in typeMapForType
  } else if (isGenericClosureType(ty)) {
    gv = emitTypeMap(ty, ParsingContext::freshName("genericClosure"), arrayStatus, mod,
                     make_vector(0, NULL));
  }

  if (!gv) {
    foster::currentOuts() << "No type map for type " << (*ty) << "\n"
        << "\tfoster_generic_coro_t is " << *foster_generic_coro_t << "\n";
  }

  return gv;
}

