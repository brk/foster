// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_H
#define FOSTER_TYPE_AST_H

#include "llvm/DerivedTypes.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <string>

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
  const llvm::Type* getLLVMType() { return repr; }

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << str(repr);
  };

  static TypeAST* get(const llvm::Type* loweredType);
};

class RefTypeAST : public TypeAST {
  bool isNullable;
  explicit RefTypeAST(const llvm::Type* ptrType, bool nullable)
    : TypeAST(ptrType), isNullable(nullable) {}

  static std::map<std::pair<const llvm::Type*, bool>, RefTypeAST*> refCache;
public:
  // given (T), returns (ref T)
  static RefTypeAST* get(const llvm::Type* baseType, bool nullable);

  // given (T*), returns (?ref T)
  static RefTypeAST* getNullableVersionOf(const llvm::Type* ptrType); 
};

#endif // header guard

