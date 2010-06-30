// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_H
#define FOSTER_TYPE_AST_H

#include "llvm/DerivedTypes.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <string>
#include <vector>
#include <ostream>

class TypeAST;
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

class TypeAST {
  // Equivalent (equal or convertible) representation types
  // is a necessary but not sufficient precondition for two
  // types to be compatible. For example, nullable and non-
  // nullable reference to T are both representated by type
  // T*, but they are not always compatible.
  const llvm::Type* repr;


  static std::map<const llvm::Type*, TypeAST*> thinWrappers;

protected:
  explicit TypeAST(const llvm::Type* underlyingType)
    : repr(underlyingType) {}

public:
  const llvm::Type* getLLVMType() const { return repr; }

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << str(repr);
  };

  virtual bool canConvertTo(TypeAST* otherType);

  static TypeAST* get(const llvm::Type* loweredType);
};


class RefTypeAST : public TypeAST {
  bool isNullable;
  TypeAST* underlyingType;

  explicit RefTypeAST(TypeAST* underlyingType, bool nullable)
    : TypeAST(llvm::PointerType::getUnqual(underlyingType->getLLVMType())),
      isNullable(nullable),
      underlyingType(underlyingType) {
    assert(getLLVMType()->isPointerTy());
  }

  typedef std::pair<TypeAST*, bool> RefTypeArgs;
  static std::map<RefTypeArgs, RefTypeAST*> refCache;
public:
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (isNullable) {
      return out << "(nullable " << str(getLLVMType()) << ")";
    } else {
      return out << str(getLLVMType());
    }
  };

  virtual bool canConvertTo(TypeAST* otherType);

  TypeAST* getElementType() { return underlyingType; }

  // given (T), returns (ref T)
  static RefTypeAST* get(TypeAST* baseType, bool nullable);

  // given (T*), returns (?ref T)
  static RefTypeAST* getNullableVersionOf(TypeAST* ptrType); 
};


class FnTypeAST : public TypeAST {
  TypeAST* returnType;
  std::vector<TypeAST*> argTypes;

  explicit FnTypeAST(const llvm::FunctionType* fnty,
                    TypeAST* returnType,
                    const std::vector<TypeAST*>& argTypes)
    : TypeAST(fnty),
      returnType(returnType),
      argTypes(argTypes) {}

  typedef std::pair<TypeAST*, std::vector<TypeAST*> > FnTypeArgs;
  static std::map<FnTypeArgs, FnTypeAST*> fnTypeCache;
public:
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << str(getLLVMType());
  };

  static FnTypeAST* get(TypeAST* retTy,
                        const std::vector<TypeAST*>& argTypes);

  TypeAST* getParamType(int i) { return argTypes[i]; }

  TypeAST* getReturnType() { return returnType; }

  bool getNumParams() { return argTypes.size(); }
};


class TupleTypeAST : public TypeAST {
  std::vector<TypeAST*> parts;

  explicit TupleTypeAST(const llvm::StructType* sty,
                    const std::vector<TypeAST*>& parts)
    : TypeAST(sty),
      parts(parts) {}

  typedef std::pair<TypeAST*, std::vector<TypeAST*> > TupleTypeArgs;
  static std::map<TupleTypeArgs, TupleTypeAST*> tupleTypeCache;
public:
  static TupleTypeAST* get(const std::vector<TypeAST*>& parts);
};


#endif // header guard

