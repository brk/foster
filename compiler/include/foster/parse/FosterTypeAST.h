// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_H
#define FOSTER_TYPE_AST_H

#include "base/Assert.h"
#include "parse/TypeASTVisitor.h"

#include "parse/FosterASTKinds-inl.h"

#include "llvm/CallingConv.h"
#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"

// implicit includes
//#include "base/SourceRange.h"
//#include "llvm/Support/raw_ostream.h"
//#include <string>
//#include <iosfwd>

#include <map>
#include <list>
#include <vector>

using std::string;

using foster::SourceRange;

class IntAST;

class TypeAST;
class FnTypeAST;
class RefTypeAST;
class TupleTypeAST;

class DumpTypeToProtobufPass;

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
  mutable const llvm::Type* repr;
  const SourceRange sourceRange;

  explicit TypeAST(const char* tag,
                   const llvm::Type* underlyingType,
                   const SourceRange& sourceRange)
    : repr(underlyingType), sourceRange(sourceRange), tag(tag) {}
  virtual ~TypeAST();
public:
  const char* const tag;
  const SourceRange& getSourceRange() const { return sourceRange; }
  virtual const llvm::Type* getLLVMType() const { return repr; }

  virtual void accept(TypeASTVisitor* visitor) = 0;
  virtual bool isTypeVariable() { return false; }
  virtual bool canConvertTo(TypeAST* otherType);

  static TypeAST* i(int n);
  static TypeAST* getVoid();

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

class TypeVariableAST : public TypeAST {
  std::string typeVarName;
  foster::Kind* kind;

  llvm::PATypeHolder opaqueType;
  explicit TypeVariableAST(const llvm::OpaqueType* opaqueType,
                           const std::string& typeVarName,
                           const SourceRange& sourceRange)
    : TypeAST("TyVar", opaqueType, sourceRange),
      typeVarName(typeVarName), opaqueType(opaqueType) {}

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }
  virtual bool isTypeVariable() { return true; }

  const std::string& getTypeVariableName() { return typeVarName; }

  static TypeVariableAST* get(const std::string& name, const SourceRange& sourceRange);
};

class NamedTypeAST : public TypeAST {
  const std::string name;
  TypeAST* nonLLVMType;

  explicit NamedTypeAST(const std::string& typeName, TypeAST* underlyingType,
                        const SourceRange& sourceRange)
     : TypeAST("NamedType", NULL, sourceRange),
       name(typeName), nonLLVMType(underlyingType) {}

  explicit NamedTypeAST(const std::string& typeName, const llvm::Type* underlyingType,
                          const SourceRange& sourceRange)
       : TypeAST("NamedType", underlyingType, sourceRange),
         name(typeName), nonLLVMType(NULL) {}

  static std::map<const llvm::Type*, TypeAST*> thinWrappers;

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }
  virtual const llvm::Type* getLLVMType() const;
  const std::string getName() { return name; }

  // get() should be used for primitive LLVM types;
  // reconstruct() should be used for derived llvm types.
  static TypeAST* get(const std::string& name, const llvm::Type* loweredType);
};

class IndexableTypeAST : public TypeAST {
protected:
  explicit IndexableTypeAST(const char* tag,
                            const llvm::Type* underlyingType,
                            const SourceRange& sourceRange)
    : TypeAST(tag, underlyingType, sourceRange) {}
  virtual ~IndexableTypeAST() {}

public:
  virtual void accept(TypeASTVisitor* visitor) = 0;

  virtual TypeAST*& getContainedType(size_t idx) = 0;
  virtual int64_t   getNumElements() const = 0;
  virtual bool      indexValid(int idx) const { return idx < getNumElements(); }
};


class RefTypeAST : public TypeAST {
  TypeAST* underlyingType;

  explicit RefTypeAST(TypeAST* underlyingType,
                      const SourceRange& sourceRange)
    : TypeAST("RefType", NULL, sourceRange),
      underlyingType(underlyingType) {}

  typedef TypeAST* RefTypeArgs;
  static std::map<RefTypeArgs, RefTypeAST*> refCache;
public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }
  virtual const llvm::Type* getLLVMType() const;

  virtual bool canConvertTo(TypeAST* otherType);
  TypeAST*& getElementType() { return underlyingType; }

  // given (T), returns (ref T)
  static RefTypeAST* get(TypeAST* baseType);
};


class FnTypeAST : public TypeAST {
  TypeAST* returnType;
  std::vector<TypeAST*> argTypes;
  std::string callingConvention;
  bool markedAsClosure;

  explicit FnTypeAST(TypeAST* returnType,
                     const std::vector<TypeAST*>& argTypes,
                     const std::string& callingConvention,
                     const SourceRange& sourceRange)
    : TypeAST("FnType", NULL, sourceRange),
      returnType(returnType),
      argTypes(argTypes),
      callingConvention(callingConvention),
      markedAsClosure(false) {}

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }
  virtual const llvm::Type* getLLVMType() const;

  static FnTypeAST* get(TypeAST* retTy,
                        const std::vector<TypeAST*>& argTypes,
                        const std::string& callingConvName);

  TypeAST*& getParamType(int i) { return argTypes[i]; }
  TypeAST* getParamType(int i) const { return argTypes[i]; }
  TypeAST*& getReturnType() { return returnType; }
  TypeAST* getReturnType() const { return returnType; }
  int getNumParams() const { return argTypes.size(); }

  const llvm::FunctionType* getLLVMFnType() const;

  void markAsClosure() { markedAsClosure = true; }
  bool isMarkedAsClosure() const { return markedAsClosure; }

  llvm::CallingConv::ID getCallingConventionID();
  friend class DumpTypeToProtobufPass;
};


class TupleTypeAST : public IndexableTypeAST {
  std::vector<TypeAST*> parts;

  explicit TupleTypeAST(const std::vector<TypeAST*>& parts,
                        const SourceRange& sourceRange)
    : IndexableTypeAST("TupleType", NULL, sourceRange),
      parts(parts) {}

  typedef std::vector<TypeAST*> Args;
  static std::map<Args, TupleTypeAST*> tupleTypeCache;
public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }
  virtual const llvm::Type* getLLVMType() const;

  virtual int getNumContainedTypes() const { return parts.size(); }
  virtual int64_t getNumElements()   const { return parts.size(); }
  virtual TypeAST*& getContainedType(size_t i);

  static TupleTypeAST* get(const std::vector<TypeAST*>& parts);
};


class CoroTypeAST : public TypeAST {
  TypeAST* a;
  TypeAST* b;

  explicit CoroTypeAST(TypeAST* targ, TypeAST* tret, const SourceRange& sr)
    : TypeAST("CoroType", NULL, sr),
      a(targ), b(tret) {}

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }
  virtual const llvm::Type* getLLVMType() const;

  virtual bool canConvertTo(TypeAST* otherType);
  virtual int getNumContainedTypes() const { return 2; }
  virtual TypeAST*& getContainedType(size_t i);

  static CoroTypeAST* get(TypeAST* targ, TypeAST* tret);
};

class CArrayTypeAST : public TypeAST {
  TypeAST* cell;
  uint64_t size;

  explicit CArrayTypeAST(TypeAST* tcell, int64_t size, const SourceRange& sr)
    : TypeAST("CArrayType", NULL, sr),
      cell(tcell), size(size) {}

public:
  virtual void accept(TypeASTVisitor* visitor) { visitor->visit(this); }
  virtual const llvm::Type* getLLVMType() const;

  uint64_t getSize() { return size; }
  virtual bool canConvertTo(TypeAST* otherType);
  virtual int getNumContainedTypes() const { return 1; }
  virtual TypeAST*& getContainedType(size_t i);

  static CArrayTypeAST* get(TypeAST* tcell, uint64_t size);
};

#endif // header guard

