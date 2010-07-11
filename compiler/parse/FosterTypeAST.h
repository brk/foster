// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_H
#define FOSTER_TYPE_AST_H


#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"

#include "base/Assert.h"
#include "base/SourceRange.h"

#include <map>
#include <string>
#include <vector>
#include <ostream>

using foster::SourceRange;

class TypeAST;
class FnTypeAST;
class RefTypeAST;
class TupleTypeAST;
class ClosureTypeAST;

std::ostream& operator<<(std::ostream& out, TypeAST& expr);

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
  // nullable reference to T are both representated by type
  // T*, but they are not always compatible.
  const llvm::Type* repr;
  const foster::SourceRange sourceRange;

  static std::map<const llvm::Type*, TypeAST*> thinWrappers;

  explicit TypeAST(const llvm::Type* underlyingType,
                   const foster::SourceRange& sourceRange)
    : repr(underlyingType), sourceRange(sourceRange) {}
  virtual ~TypeAST();
public:
  virtual const llvm::Type* getLLVMType() const { return repr; }

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << str(repr);
  };

  virtual bool canConvertTo(TypeAST* otherType);

  static TypeAST* get(const llvm::Type* loweredType);
  // TODO in some situations, such as (for now)
  // when a llvm::Module gives us a function type, we need
  // to make a best effort at reconstruting a specific
  // TypeAST tree based on the provided llvm::Type.
  // The correct "long-term" approach is to design and
  // emit interface definitions in parallel with compiled
  // Modules, so that we don't lose e.g. nullability info
  // in the first place.
};


class RefTypeAST : public TypeAST {
  bool nullable;
  TypeAST* underlyingType;

  explicit RefTypeAST(TypeAST* underlyingType, bool nullable,
                      const foster::SourceRange& sourceRange)
    : TypeAST(llvm::PointerType::getUnqual(underlyingType->getLLVMType()),
              sourceRange),
      nullable(nullable),
      underlyingType(underlyingType) {
    ASSERT(getLLVMType()->isPointerTy());
  }

  typedef std::pair<TypeAST*, bool> RefTypeArgs;
  static std::map<RefTypeArgs, RefTypeAST*> refCache;
public:
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (isNullable()) {
      return out << "(nullable " << str(getLLVMType()) << ")";
    } else {
      return out << str(getLLVMType());
    }
  };

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

  explicit FnTypeAST(const llvm::FunctionType* fnty,
                    TypeAST* returnType,
                    const std::vector<TypeAST*>& argTypes,
                    const foster::SourceRange& sourceRange)
    : TypeAST(fnty, sourceRange),
      returnType(returnType),
      argTypes(argTypes) {}

  typedef std::pair<TypeAST*, std::vector<TypeAST*> > FnTypeArgs;
  static std::map<FnTypeArgs, FnTypeAST*> fnTypeCache;
public:
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "FnTypeAST(";
    for (int i = 0; i < getNumParams(); ++i) {
      out << "arg["<<i<<"] = " << *(getParamType(i)) << ", ";
    }
    out << "--> " << *getReturnType();
    out << ")";
    return out;
  };

  static FnTypeAST* get(TypeAST* retTy,
                        const std::vector<TypeAST*>& argTypes);

  TypeAST* getParamType(int i) const { return argTypes[i]; }

  TypeAST* getReturnType() const { return returnType; }

  int getNumParams() const { return argTypes.size(); }
};


class TupleTypeAST : public TypeAST {
  std::vector<TypeAST*> parts;

  explicit TupleTypeAST(const llvm::StructType* sty,
                    const std::vector<TypeAST*>& parts,
                    const foster::SourceRange& sourceRange)
    : TypeAST(sty, sourceRange),
      parts(parts) {}

  typedef std::vector<TypeAST*> Args;
  static std::map<Args, TupleTypeAST*> tupleTypeCache;
public:
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "tuple { ";
    for (size_t i = 0; i < parts.size(); ++i) {
      out << *(parts[i]) << ", ";
    }
    out << " }";
    return out;
  }
  virtual int getNumContainedTypes() { return parts.size(); }
  virtual TypeAST* getContainedType(int i) { return parts[i]; }
  static TupleTypeAST* get(const std::vector<TypeAST*>& parts);
};

class PrototypeAST;

class ClosureTypeAST : public TypeAST {
public:
  PrototypeAST* proto;
  mutable FnTypeAST* fntype;
  mutable TupleTypeAST* clotype;
  explicit ClosureTypeAST(PrototypeAST* proto, const llvm::Type* underlyingType,
                          const foster::SourceRange& sourceRange)
     : TypeAST(underlyingType, sourceRange), proto(proto), fntype(NULL), clotype(NULL) {}

  virtual std::ostream& operator<<(std::ostream& out) const;
  virtual const llvm::Type* getLLVMType() const;
  FnTypeAST* getFnType() const;
};


class LiteralIntTypeAST : public TypeAST {
  uint64_t value;
public:
  explicit LiteralIntTypeAST(uint64_t value,
                      const foster::SourceRange& sourceRange)
    : TypeAST(llvm::IntegerType::get(llvm::getGlobalContext(), 64),
              sourceRange),
      value(value) { }

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << value;
  }

  uint64_t getNumericalValue() { return value; }
};


class SimdVectorTypeAST : public TypeAST {
public:
  explicit SimdVectorTypeAST(const llvm::Type* simdVectorTy,
                             const foster::SourceRange& sourceRange)
     : TypeAST(simdVectorTy, sourceRange) {}

  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "SimdVectorTypeAST(" << str(repr) << ")";
    return out;
  }

  static SimdVectorTypeAST* get(LiteralIntTypeAST* size, TypeAST* type,
                                const foster::SourceRange& sourceRange);
};

#endif // header guard

