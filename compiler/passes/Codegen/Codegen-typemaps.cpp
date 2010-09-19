// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "parse/FosterUtils.h"
#include "parse/CompilationContext.h"

#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"

#include <map>
#include <set>
#include <vector>

using foster::LLVMTypeFor;

using namespace llvm;

llvm::GlobalVariable* getTypeMapForType(const llvm::Type*);

typedef std::pair<const Type*, Constant*> OffsetInfo;
typedef std::set<OffsetInfo> OffsetSet;

Constant* arrayVariableToPointer(GlobalVariable* arr) {
  std::vector<Constant*> idx;
  idx.push_back(getConstantInt64For(0));
  idx.push_back(getConstantInt64For(0));
  return ConstantExpr::getGetElementPtr(arr, &idx[0], idx.size());
}

OffsetSet countPointersInType(const Type* ty) {
  ASSERT(ty) << "Can't count pointers in a NULL type!";

  OffsetSet rv;
  if (ty->isPointerTy()) {
    rv.insert(OffsetInfo(ty->getContainedType(0),
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
  // plus the set for T2 with offsets incremented by the size of T1.
  else if (const StructType* sty
                            = dyn_cast<const StructType>(ty)) {
    for (size_t i = 0; i < sty->getNumElements(); ++i) {
      Constant* slotOffset = ConstantExpr::getOffsetOf(sty, i);
      OffsetSet sub = countPointersInType(sty->getTypeAtIndex(i));
      for (OffsetSet::iterator si = sub.begin(); si != sub.end(); ++si) {
        const Type* subty = si->first;
        Constant* suboffset = si->second;
        rv.insert(OffsetInfo(subty,
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


std::map<const Type*, GlobalVariable*> typeMapForType;


// A type map entry is a pair:
//  struct { i8* typeinfo; i32 offset }
//
// The second field is the offset of a slot in the parent type.
// The first field is either a pointer to a typemap describing
// the slot, or (for atomic types) the size of the type.
//
// We can distinguish the two cases at runtime since only arrays
// can lead to objects of any significant (multi-KB) size.
Constant* getTypeMapEntryFor(
                const StructType* typeMapEntryTy,
                const Type* entryTy,
                Constant* offset) {
  std::vector<Constant*> fields;

  GlobalVariable* typeMapVar = getTypeMapForType(entryTy);
  if (typeMapVar) {
        fields.push_back(ConstantExpr::getCast(Instruction::BitCast,
                        typeMapVar, LLVMTypeFor("i8*")));
  } else {
        // If we can't tell the garbage collector how to collect a type by
        // giving it a pointer to a type map, it's probably because the type
        // doesn't have a type map, i.e. the type is atomic. Instead, tell
        // the garbage collector how large the type is.
        fields.push_back(
            ConstantExpr::getCast(Instruction::IntToPtr,
                                  ConstantExpr::getSizeOf(entryTy),
                                  LLVMTypeFor("i8*")));
  }

  fields.push_back(ConstantExpr::getTruncOrBitCast(
                   offset, LLVMTypeFor("i32")));

  return ConstantStruct::get(typeMapEntryTy, fields);
}

void removeEntryWithOffset(OffsetSet& os, Constant* offset) {
  OffsetSet::iterator toRemove = os.end();
  for (OffsetSet::iterator it = os.begin(); it != os.end(); ++it) {
    if (it->second == offset) {
      toRemove = it;
      break;
    }
  }

  if (toRemove != os.end()) {
    os.erase(toRemove);
  }
}

// Return a global corresponding to the following layout:
// struct {
//   const char* typeName;
//   i32 numPtrEntries;
//   struct { i8* typeinfo; i32 offset }[numPtrEntries];
// }
// The returned global is also stored in the typeMapForType[] map.
GlobalVariable* emitTypeMap(const Type* ty, std::string name,
    bool skipOffsetZero = false) {
  OffsetSet pointerOffsets = countPointersInType(ty);
  //currentOuts() << "emitting type map for type " << str(ty)
  // << " ; skipping offset zero? " << skipOffsetZero << "\n";

  if (skipOffsetZero) {
    // Remove entry for first pointer, which corresponds
    // to the type map for the environment.
    removeEntryWithOffset(pointerOffsets,
                          getConstantInt64For(0));
  }
  int numPointers = pointerOffsets.size();

  // Construct the type map's LLVM type
  std::vector<const Type*> entryty_types;
  entryty_types.push_back(LLVMTypeFor("i8*"));
  entryty_types.push_back(LLVMTypeFor("i32"));
  StructType* entryty = StructType::get(getGlobalContext(),
                                        entryty_types,
                                        /*isPacked=*/false);
  foster::module->addTypeName("typemap_entry", entryty);

  std::vector<const Type*> typeMapTyFields;
  ArrayType* entriesty = ArrayType::get(entryty, numPointers);

  typeMapTyFields.push_back(LLVMTypeFor("i8*"));
  typeMapTyFields.push_back(LLVMTypeFor("i32"));
  typeMapTyFields.push_back(entriesty);

  const StructType* typeMapTy = StructType::get(getGlobalContext(),
                                                typeMapTyFields);

  GlobalVariable* typeMapVar = new GlobalVariable(
    /*Module=*/     *foster::module,
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

  // Construct the type map itself
  std::string wrapped;
  raw_string_ostream ss(wrapped); ss << name << " = " << *ty;
  std::vector<Constant*> typeMapFields;
  Constant* cname = ConstantArray::get(getGlobalContext(),
                                                   ss.str().c_str(),
                                                   true);
  GlobalVariable* typeNameVar = new GlobalVariable(
      /*Module=*/      *foster::module,
      /*Type=*/        cname->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     GlobalValue::PrivateLinkage,
      /*Initializer=*/ cname,
      /*Name=*/        ".typename." + name);
  typeNameVar->setAlignment(1);

  Constant* cnameptr = arrayVariableToPointer(typeNameVar);
  typeMapFields.push_back(cnameptr);
  typeMapFields.push_back(getConstantInt32For(numPointers));

  std::vector<Constant*> typeMapEntries;
  for (OffsetSet::iterator si =  pointerOffsets.begin();
                                   si != pointerOffsets.end(); ++si) {
        const Type* subty = si->first;
        Constant* suboffset = si->second;
        typeMapEntries.push_back(
          getTypeMapEntryFor(entryty, subty, suboffset));
  }


  typeMapFields.push_back(ConstantArray::get(entriesty, typeMapEntries));

  Constant* typeMap = ConstantStruct::get(typeMapTy, typeMapFields);

  typeMapVar->setInitializer(typeMap);
  return typeMapVar;
}

void registerType(const Type* ty, std::string desiredName,
    bool isClosureEnvironment = false) {
  static std::map<const Type*, bool> registeredTypes;

  if (registeredTypes[ty]) return;

  registeredTypes[ty] = true;

  std::string name = freshName(desiredName);
  foster::module->addTypeName(name, ty);
  emitTypeMap(ty, name, isClosureEnvironment);
}


llvm::GlobalVariable* getTypeMapForType(const llvm::Type* ty) {
  llvm::GlobalVariable* gv = typeMapForType[ty];
  if (gv) return gv;

  if (!ty->isAbstract() && !ty->isAggregateType()) {
    gv = emitTypeMap(ty, freshName("gcatom"));
    // emitTypeMap also sticks gv in typeMapForType
  } else if (isGenericClosureType(ty)) {
    gv = emitTypeMap(ty, freshName("genericClosure"),
                     /*skipOffsetZero*/ true);
  }

  if (!gv) {
    foster::currentOuts() << "No type map for type " << (*ty) << "\n";
  }

  return gv;
}

