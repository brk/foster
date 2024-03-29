// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/ParsingContext.h"
#include "parse/FosterTypeAST.h"

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

#include <map>
#include <set>
#include <vector>

#include "passes/CodegenPass-impl.h"

using namespace llvm;

using foster::DDiag;
using foster::EDiag;
using foster::builder;
using foster::ParsingContext;

typedef uint64_t    Offset;
typedef std::vector<Offset> OffsetSet;

unsigned kDefaultHeapAlignment = 16;

bool isPointerToSized(Type* ty) {
  // For now, we don't distinguish between different kinds of pointer;
  // we consider any pointer to be a possible heap pointer.
  return ty->isPointerTy() && ty->getContainedType(0)->isSized();
}

// TODO vector of pointers now supported by LLVM...
// will we allow vectors of pointers-to-GC-heap? probably unwise.

OffsetSet countPointersInType(const TypeAST* typ, Type* ty, Module* mod) {
  ASSERT(ty) << "Can't count pointers in a NULL type!";

  OffsetSet rv;
  if (typ->isGarbageCollectible()) {
    // Pointers to functions/labels/other non-sized types do not get GC'd.
    rv.push_back(0);
  }

  // unboxed array, struct, union
  else if (dyn_cast<ArrayType>(ty)) {
    // TODO need to decide how Foster semantics will map to LLVM IR for arrays.
    // Will EVERY (C++), SOME (Factor, C#?), or NO (Java) types be unboxed?
    // Also need to figure out how the gc will collect arrays.
    ASSERT(false) << "array map offsets?";
    //return aty->getNumElements() * countPointersInType(aty->getElementType());
  }

  // if we have a struct { T1; T2 } then our offset set will be the set for T1,
  // plus the set for T2 with offsets incremented by the offset of T2.
  else if (StructType* sty = dyn_cast<StructType>(ty)) {
    StructTypeAST* stp = const_cast<StructTypeAST*>(typ->castStructTypeAST());
    ASSERT(stp) << "StructType without corresponding StructTypeAST?!? "
                << str(typ) << " ~~tag = " << typ->tag;
    auto layout = mod->getDataLayout().getStructLayout(sty);
    for (size_t i = 0; i < sty->getNumElements(); ++i) {
      auto slotOffset = layout->getElementOffset(i);
      OffsetSet sub = countPointersInType(stp->getContainedType(i),
                                            sty->getTypeAtIndex(i), mod);
      for (Offset suboffset : sub) {
        rv.push_back(suboffset + slotOffset);
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

Type* getHeapCellHeaderTy() {
  return builder.getInt64Ty();
}

// Rounds up to nearest multiple of the given power of two.
uint64_t roundUpToNearestMultiple(uint64_t v, uint64_t powerOf2) {
  uint64_t mask = powerOf2 - 1;
  return (v + mask) & ~mask;
}

// A slot is a cell which is *NOT* directly preceded by a heap cell header.
// For example, the repeated elements of an array are slots, not cells.
Constant* slotSizeOf(Type* ty) {
  return ConstantExpr::getSizeOf(ty);
}

// A cell is a memory region which is directly preceded by a heap cell header.
// Returns the smallest multiple of the default heap alignment
// which is larger than the size of the given type plus the heap header size.
Constant* cellSizeOf(Type* ty, Module* m) {
  auto& dl = m->getDataLayout();
  uint64_t sz = dl.getTypeAllocSize(ty);
  uint64_t hs = dl.getTypeAllocSize(getHeapCellHeaderTy());
  uint64_t rv = roundUpToNearestMultiple(hs + sz, kDefaultHeapAlignment);
  return ConstantInt::get(builder.getInt64Ty(), rv);
}

typedef std::pair<Type*, std::pair<ArrayOrNot, int8_t> > TypeSig;
TypeSig mkTypeSig(Type* t, ArrayOrNot a, int8_t c) {
  return std::make_pair(t, std::make_pair(a, c));
}

std::map<TypeSig, GlobalVariable*> typeMapCache;

Type* getTypeMapOffsetType() {
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
StructType* getTypeMapType(int numPointers, llvm::Module* mod) {
  if (numPointers == 0) {
    // In version 4.0 something changed in LLVM's linking strategy,
    // with the result that the named struct type from foster_gc_utils.h
    // and the anonymous version below, which are structurally identical,
    // were linked in favor of the anonymous version instead of the named
    // version, which in turn meant that C functions taking typemaps,
    // such as the memalloc_* family, were left unlinked!
    //
    // We just avoid the whole mess by getting the named struct type here.

    llvm::Function* memalloc = mod->getFunction("memalloc_array");
    ASSERT(memalloc != NULL);
    auto typemapty = mod->getGlobalVariable("foster_gc_utils_typemap_exemplar")->getValueType();
    llvm::StructType* tmty = llvm::dyn_cast<llvm::StructType>(typemapty);
    if (tmty) { return tmty; }
  }

  ArrayType* offsetsTy = ArrayType::get(getTypeMapOffsetType(), numPointers);

  std::vector<Type*> typeMapTyFields;
  typeMapTyFields.push_back(builder.getInt64Ty());   // cellSize
  typeMapTyFields.push_back(builder.getPtrTy());     // typeName
  typeMapTyFields.push_back(builder.getInt32Ty());   // numPtrEntries
  typeMapTyFields.push_back(builder.getInt8Ty());    // ctorId
  typeMapTyFields.push_back(builder.getInt8Ty());    // isCoro
  typeMapTyFields.push_back(builder.getInt8Ty());    // isArray
  typeMapTyFields.push_back(builder.getInt8Ty());    // ptrMap
  typeMapTyFields.push_back(offsetsTy);              // i32[n]

  return StructType::get(builder.getContext(), typeMapTyFields);
}

uint8_t computePtrMap(llvm::Module* mod, const OffsetSet& pointerOffsets) {
  unsigned ptrsize = mod->getDataLayout().getPointerSize();
  uint8_t descriptor = 0;
  for (auto c : pointerOffsets) {
    auto ptroff = c / ptrsize;
    if (ptroff >= 4) {
      return 128;
    }
    descriptor |= (1 << ptroff);
  }
  if (descriptor == 1 || descriptor == 3 || descriptor == 7 || descriptor == 0) {
    return descriptor;
  }
  return 128;
}

// Return a global corresponding to layout of getTypeMapType()
// The returned global is also stored in the typeMapForType[] map.
GlobalVariable* constructTypeMap(llvm::Type*  ty,
                                 const std::string& name,
                                 const OffsetSet&   pointerOffsets,
                                 ArrayOrNot         arrayStatus,
                                 int8_t             ctorId,
                                 llvm::Module*      mod) {
  //llvm::outs() << "Constructing type map with name " << name << " and ctor id " << int(ctorId) << "\n";

  int numPointers = pointerOffsets.size();
  StructType* typeMapTy = getTypeMapType(numPointers, mod);

  GlobalVariable* typeMapVar = new GlobalVariable(
    /*Module=*/     *mod,
    /*Type=*/       typeMapTy,
    /*isConstant=*/ false,
    /*Linkage=*/    GlobalValue::ExternalLinkage,
    /*Initializer=*/ 0,
    /*Name=*/        "__foster_typemap_" + name,
    /*InsertBefore=*/NULL,
    /*ThreadLocal=*/ GlobalVariable::NotThreadLocal);
  typeMapVar->setAlignment(llvm::MaybeAlign(16));

  std::string wrapped;
  raw_string_ostream ss(wrapped); ss << name << " = " << *ty;
  Constant* cname = getConstantArrayOfString(ss.str());

  GlobalVariable* typeNameVar = new GlobalVariable(
      /*Module=*/      *mod,
      /*Type=*/        cname->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     GlobalValue::PrivateLinkage,
      /*Initializer=*/ cname,
      /*Name=*/        ".typename." + name);
  typeNameVar->setAlignment(llvm::MaybeAlign(1));


  std::vector<Constant*> typeMapOffsets;
  for (auto it : pointerOffsets) {
    typeMapOffsets.push_back(builder.getInt32(it));
  }

  // TODO fix this
  bool isCoro = llvm::StringRef(name).startswith("coro_");
  bool isArray = arrayStatus == YesArray;
  ArrayType* offsetsTy = ArrayType::get(getTypeMapOffsetType(), numPointers);

  // Construct the type map itself
  std::vector<Constant*> typeMapFields;
  typeMapFields.push_back(isArray ? slotSizeOf(ty)
                                  : cellSizeOf(ty, mod));
  typeMapFields.push_back(arrayVariableToPointer(typeNameVar));
  typeMapFields.push_back(builder.getInt32(numPointers));
  typeMapFields.push_back(builder.getInt8(ctorId));
  typeMapFields.push_back(builder.getInt8(isCoro  ? 1 : 0));
  typeMapFields.push_back(builder.getInt8(isArray ? 1 : 0));
  typeMapFields.push_back(builder.getInt8(computePtrMap(mod, pointerOffsets)));
  typeMapFields.push_back(ConstantArray::get(offsetsTy, typeMapOffsets));

  typeMapVar->setInitializer(ConstantStruct::get(typeMapTy, typeMapFields));
  return typeMapVar;
}

// Computes the offsets of all pointers in the given type,
// and constructs a type map using those offsets.
GlobalVariable* emitTypeMap(
    const TypeAST* typ,
    llvm::Type*   ty,
    std::string   name,
    ArrayOrNot    arrayStatus,
    CtorRepr      ctorRepr,
    llvm::Module* mod,
    std::vector<int> skippedIndexVector) {
  // Careful! The indices here are relative to the values
  // returned by countPointersInType(), not the indices
  // in the type of those pointers.
  std::set<int> skippedOffsets(skippedIndexVector.begin(),
                               skippedIndexVector.end());
  OffsetSet filteredOffsets;
  OffsetSet pointerOffsets = countPointersInType(typ, ty, mod);
  for(size_t i = 0; i < pointerOffsets.size(); ++i) {
    if (skippedOffsets.count(i) == 0) {
      filteredOffsets.push_back(pointerOffsets[i]);
    }
  }

  TypeSig sig = mkTypeSig(ty, arrayStatus, ctorRepr.smallId);
  typeMapCache[sig] = constructTypeMap(ty, name, filteredOffsets, arrayStatus, ctorRepr.smallId, mod/*, datalayout*/);
  return typeMapCache[sig];
}

// The struct type is
// { { { i8** }, void (i8*)*, i8*, \2*, i32 }, i32 }
// {
//   { <coro_context>           0
//   , fn              <---     1
//   , env             <---    (2)
//   , parent          <---    [3]
//   , indirect_self            4
//   , status
//   }
//   argty
// }
// See also libfoster_gc_roots.h
GlobalVariable* emitCoroTypeMap(const StructTypeAST* typ, StructType* sty,
                                llvm::Module* mod) {
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
  CtorRepr bogusCtor; bogusCtor.smallId = -1;
  std::vector<int> v; v.push_back(0); v.push_back(1); v.push_back(4);
  return emitTypeMap(typ, sty, ss.str(), NotArray, bogusCtor, mod, /*datalayout,*/ v);
}

void registerStructType(const StructTypeAST* structty,
                        std::string desiredName,
                        CtorRepr       ctorRepr,
                        llvm::Module* mod) {
  ASSERT(structty != nullptr) << "registerStructType() needs a non-null type to work with.";

  static std::map<TypeSig, bool> registeredTypes;

  llvm::Type* ty = structty->getLLVMType();
  TypeSig sig = mkTypeSig(ty, NotArray, ctorRepr.smallId);
  if (registeredTypes[sig]) return;

  registeredTypes[sig] = true;

  std::string name = ParsingContext::freshName(desiredName);
  //mod->addTypeName(name, ty);
  //DDiag() << "TODO: registered type " << name << " = " << str(ty) << "; ctor id " << ctorRepr.smallId;
  emitTypeMap(structty, ty, name, NotArray, ctorRepr, mod, /*datalayout,*/ std::vector<int>());
}

const StructTypeAST*
castCoroStructType(TypeAST* typ) {
  if (typ == foster::ParsingContext::lookupType("Foster$GenericCoro")) {
    return typ->castStructTypeAST();
  }

  if (typ->getLLVMType() == foster_generic_coro_t) {
    return typ->castStructTypeAST();
  }
  //llvm::outs() << "isCoroStructType? " << str(typ) << "\n";
  //llvm::outs() << "    foster_generic_coro_t = " << str(foster_generic_coro_t) << "\n";

  if (StructTypeAST* sty = const_cast<StructTypeAST*>(typ->castStructTypeAST())) {
    if (sty == foster_generic_coro_ast
     ||  ( sty->getNumContainedTypes() > 0
        && sty->getContainedType(0) == foster_generic_coro_ast)) {
      return sty;
    }
  }
  return nullptr;
}

// Checks that ty == { ___ (i8*, ...)*, i8* }
bool isGenericClosureType(const llvm::Type* ty) {
  using foster::builder;
  llvm::Type* env = getGenericClosureEnvType()->getLLVMType();
  if (const llvm::StructType* sty= llvm::dyn_cast<const llvm::StructType>(ty)) {
    if (sty->getContainedType(1) != env) return false;
    if (!sty->getContainedType(0)->isPointerTy()) return false;

    const llvm::Type* fnty = sty->getContainedType(0)->getContainedType(0);
    if (!fnty->isFunctionTy()) return false;
    if (fnty->getNumContainedTypes() < 2) return false;
    if (fnty->getContainedType(1) != env) return false;
    return true;
  }
  return false;
}

llvm::GlobalVariable* CodegenPass::getTypeMapForType(TypeAST* typ,
                                        CtorRepr ctorRepr,
                                        llvm::Module* mod,
                                        ArrayOrNot arrayStatus) {
  llvm::Type* ty = typ->getLLVMType();
  llvm::GlobalVariable* gv = typeMapCache[mkTypeSig(ty, arrayStatus, ctorRepr.smallId)];
  if (gv) return gv;

  if (auto cty = castCoroStructType(typ)) {
    //llvm::outs() << "Emitting coro type map for " << str(typ) << "\n";
    gv = emitCoroTypeMap(cty, llvm::dyn_cast<StructType>(ty), mod);
  } else if (/*!ty->isAbstract() &&*/ !ty->isAggregateType()) {
    gv = emitTypeMap(typ, ty, ParsingContext::freshName("gcatom"), arrayStatus,
                     ctorRepr, mod, std::vector<int>());
    // emitTypeMap also sticks gv in typeMapForType
  } else if (isGenericClosureType(ty)) {
    gv = emitTypeMap(typ, ty, ParsingContext::freshName("genericClosure"), arrayStatus,
                     ctorRepr, mod, std::vector<int>());
  }

  if (!gv) {
    EDiag() << "No type map for type " << str(ty) << "\nMaybe you need to call registerStructType()?\n";
    exit(1);
  } else {
    
  }

  return gv;
}

void CodegenPass::emitTypeMapListGlobal() {
  auto ptr = builder.getPtrTy();
  std::vector<Constant*> vals;
  for (auto p : typeMapCache) {
    vals.push_back(p.second);
  }
  vals.push_back(llvm::ConstantPointerNull::getNullValue(ptr));

  llvm::ArrayType* arrTy = llvm::ArrayType::get(ptr, vals.size());
  Constant* carr = llvm::ConstantArray::get(arrTy, vals);

  GlobalVariable* typeMapListGlobal = new GlobalVariable(
      /*Module=*/      *mod,
      /*Type=*/        carr->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     GlobalValue::ExternalLinkage,
      /*Initializer=*/ carr,
      /*Name=*/        "foster__typeMapList");
  typeMapListGlobal->setAlignment(llvm::MaybeAlign(8));
}

