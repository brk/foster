// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_H
#define FOSTER_TYPE_AST_H

#include "llvm/CallingConv.h"
#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"

#include "base/Assert.h"
#include "base/SourceRange.h"
#include "parse/TypeASTVisitor.h"

#include <map>
#include <string>
#include <vector>
#include <ostream>

using std::string;

using foster::SourceRange;

class IntAST;

class TypeAST;
class FnTypeAST;
class RefTypeAST;
class TupleTypeAST;
class ClosureTypeAST;

class DumpTypeToProtobufPass;

inline std::ostream& operator<<(std::ostream& out, const llvm::Type& ty) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << ty;
  return out << ss.str();
}

inline std::string str(const llvm::Type* ty) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  if (ty) { ss << *ty; } else { ss << "<NULL ty>"; }
  return ss.str();
}

bool hasEqualRepr(TypeAST* src, TypeAST* dst);
bool arePhysicallyCompatible(const llvm::Type* src,
                             const llvm::Type* dst);

// TODO namespace foster { }

class TypeAST {
protected:
  // Equivalent (equal or convertible) representation types
  // is a necessary but not sufficient precondition for two
  // types to be compatible. For example, nullable and non-
  // nullable reference to T are both represented by type
  // T*, but they are not always compatible.
  const llvm::Type* repr;
  const SourceRange sourceRange;

  static std::map<const llvm::Type*, TypeAST*> thinWrappers;

  explicit TypeAST(const llvm::Type* underlyingType,
                   const SourceRange& sourceRange)
    : repr(underlyingType), sourceRange(sourceRange) {}
  virtual ~TypeAST();
public:
  const SourceRange& getSourceRange() const { return sourceRange; }
  virtual const llvm::Type* getLLVMType() const { return repr; }

  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  virtual bool canConvertTo(TypeAST* otherType);

  static TypeAST* i(int n);
  static TypeAST* getVoid();
  // get() should be used for primitive LLVM types;
  // reconstruct() should be used for derived llvm types.
  static TypeAST* get(const llvm::Type* loweredType);
  
  // In some situations, such as (for now)
  // when a llvm::Module gives us a function type, we need
  // to make a best effort at reconstruting a specific
  // TypeAST tree based on the provided llvm::Type.
  // The correct "long-term" approach is to design and
  // emit interface definitions in parallel with compiled
  // Modules, so that we don't lose e.g. nullability info
  // in the first place.
  static TypeAST* reconstruct(const llvm::Type* loweredType);
};

class IndexableTypeAST : public TypeAST {
protected:
  explicit IndexableTypeAST(const llvm::Type* underlyingType,
                   const SourceRange& sourceRange)
    : TypeAST(underlyingType, sourceRange) {}
  virtual ~IndexableTypeAST() {}
  
public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  virtual TypeAST* getContainedType(size_t idx) const = 0;
  virtual int64_t  getNumElements() const = 0; 
  virtual bool     indexValid(int idx) const { return idx < getNumElements(); } 
};


class RefTypeAST : public TypeAST {
  bool nullable;
  TypeAST* underlyingType;

  explicit RefTypeAST(TypeAST* underlyingType, bool nullable,
                      const SourceRange& sourceRange)
    : TypeAST(llvm::PointerType::getUnqual(underlyingType->getLLVMType()),
              sourceRange),
      nullable(nullable),
      underlyingType(underlyingType) {
    ASSERT(getLLVMType()->isPointerTy());
  }

  typedef std::pair<TypeAST*, bool> RefTypeArgs;
  static std::map<RefTypeArgs, RefTypeAST*> refCache;
public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  bool isNullable() const { return nullable; }
  virtual bool canConvertTo(TypeAST* otherType);
  TypeAST* getElementType() { return underlyingType; }

  // given (T), returns (ref T)
  static RefTypeAST* get(TypeAST* baseType, bool nullable = false);

  // given (T*), returns (?ref T)
  static RefTypeAST* getNullableVersionOf(TypeAST* ptrType); 
};


class FnTypeAST : public TypeAST {
  TypeAST* returnType;
  std::vector<TypeAST*> argTypes;
  std::string callingConvention;

  explicit FnTypeAST(const llvm::FunctionType* fnty,
                    TypeAST* returnType,
                    const std::vector<TypeAST*>& argTypes,
                    const std::string& callingConvention,
                    const SourceRange& sourceRange)
    : TypeAST(fnty, sourceRange),
      returnType(returnType),
      argTypes(argTypes),
      callingConvention(callingConvention) {}

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  static FnTypeAST* get(TypeAST* retTy,
                        const std::vector<TypeAST*>& argTypes,
                        const std::string& callingConvName);

  TypeAST* getParamType(int i) const { return argTypes[i]; }

  TypeAST* getReturnType() const { return returnType; }

  int getNumParams() const { return argTypes.size(); }

  llvm::CallingConv::ID getCallingConventionID();
  friend class DumpTypeToProtobufPass;
};


class TupleTypeAST : public IndexableTypeAST {
  std::vector<TypeAST*> parts;

  explicit TupleTypeAST(const llvm::StructType* sty,
                    const std::vector<TypeAST*>& parts,
                    const SourceRange& sourceRange)
    : IndexableTypeAST(sty, sourceRange),
      parts(parts) {}

  typedef std::vector<TypeAST*> Args;
  static std::map<Args, TupleTypeAST*> tupleTypeCache;
public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  virtual int getNumContainedTypes() const { return parts.size(); }
  virtual int64_t getNumElements()   const { return parts.size(); }
  virtual TypeAST* getContainedType(size_t i) const;
  
  static TupleTypeAST* get(const std::vector<TypeAST*>& parts);
};

class PrototypeAST;

class ClosureTypeAST : public TypeAST {
public:
  PrototypeAST* proto;
  mutable FnTypeAST* fntype;
  mutable TupleTypeAST* clotype;
  explicit ClosureTypeAST(PrototypeAST* proto, const llvm::Type* underlyingType,
                          const SourceRange& sourceRange)
     : TypeAST(underlyingType, sourceRange),
       proto(proto), fntype(NULL), clotype(NULL) {}

  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  virtual const llvm::Type* getLLVMType() const;
  FnTypeAST* getFnType() const;
};


class LiteralIntValueTypeAST : public TypeAST {
  IntAST* intAST;
  uint64_t value;
protected:
  explicit LiteralIntValueTypeAST(IntAST* intAST,
                      const SourceRange& sourceRange)
    : TypeAST(llvm::IntegerType::get(llvm::getGlobalContext(), 64),
              sourceRange),
      intAST(intAST), value(0) { }
  explicit LiteralIntValueTypeAST(uint64_t value,
                      const SourceRange& sourceRange)
    : TypeAST(llvm::IntegerType::get(llvm::getGlobalContext(), 64),
              sourceRange),
      intAST(NULL), value(value) { }

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  uint64_t getNumericalValue() const;
  
  static LiteralIntValueTypeAST* get(IntAST* intAST);
  static LiteralIntValueTypeAST* get(uint64_t value, const SourceRange& range);
};


class SimdVectorTypeAST : public IndexableTypeAST {
  LiteralIntValueTypeAST* size;
  TypeAST*                elementType;

  explicit SimdVectorTypeAST(const llvm::Type* simdVectorTy,
                             LiteralIntValueTypeAST* size,
                             TypeAST*                elementType,
                             const SourceRange& sourceRange)
     : IndexableTypeAST(simdVectorTy, sourceRange),
       size(size), elementType(elementType) {}

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }

  virtual TypeAST* getContainedType(size_t i) const { return elementType; }
  virtual int64_t  getNumElements() const { return size->getNumericalValue(); }
  
  static SimdVectorTypeAST* get(LiteralIntValueTypeAST* size, TypeAST* type,
                                const SourceRange& sourceRange);
  friend class DumpTypeToProtobufPass;
};

#endif // header guard

