// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_H
#define FOSTER_TYPE_AST_H

#include "base/Assert.h"

#include "llvm/CallingConv.h"
#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"

#include <map>
#include <list>
#include <vector>

using foster::SourceRange;

class TypeAST;
class PrettyPrintTypePass;
class DumpTypeToProtobufPass;

std::string str(const TypeAST* type);

class TypeAST {
protected:
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

  virtual void show(PrettyPrintTypePass*    pass) = 0;
  virtual void dump(DumpTypeToProtobufPass* pass) = 0;

  static TypeAST* i(int n);
};

class TypeVariableAST : public TypeAST {
  std::string typeVarName;

  llvm::PATypeHolder opaqueType;
  explicit TypeVariableAST(const llvm::OpaqueType* opaqueType,
                           const std::string& typeVarName,
                           const SourceRange& sourceRange)
    : TypeAST("TyVar", opaqueType, sourceRange),
      typeVarName(typeVarName), opaqueType(opaqueType) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);

  const std::string& getTypeVariableName() { return typeVarName; }

  static TypeVariableAST* get(const std::string& name, const SourceRange& sourceRange);
};

class PrimitiveTypeAST : public TypeAST {
  const std::string name; // Used for pretty printing
  static std::map<const llvm::Type*, TypeAST*> thinWrappers;
public:
  explicit PrimitiveTypeAST(const std::string& typeName,
                            const llvm::Type* underlyingType,
                            const SourceRange& sourceRange)
  : TypeAST("PrimitiveType", underlyingType, sourceRange), name(typeName) {}

  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const { return this->repr; }
  const std::string getName() { return name; }
  static TypeAST* get(const std::string& name, const llvm::Type* loweredType);
};

class NamedTypeAST : public TypeAST {
  const std::string name;
  mutable TypeAST* namedType;

public:
  bool is_placeholder; // TODO remove this hack :(
  explicit NamedTypeAST(const std::string& typeName,
                        TypeAST* underlyingType,
                        const SourceRange& sourceRange)
     : TypeAST("NamedType", NULL, sourceRange),
       name(typeName), namedType(underlyingType), is_placeholder(false) {}
  void setNamedType(TypeAST* t) { namedType = t; }
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const;
  const std::string getName() { return name; }
};

struct DataCtor {
  std::string name;
  std::vector<TypeAST*> types;
};

class DataTypeAST : public TypeAST {
  const std::string name;
  const std::vector<DataCtor*> ctors;
  mutable llvm::OpaqueType* opaq;

public:
  explicit DataTypeAST(const std::string& typeName,
                       std::vector<DataCtor*> ctors,
                       const SourceRange& sourceRange)
     : TypeAST("DataTypeAST", NULL, sourceRange),
       name(typeName), ctors(ctors), opaq(NULL) {}

  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const; // don't use this one!
  //const llvm::PointerType* getOpaquePointerTy(llvm::Module* mod) const;
  size_t getNumCtors() const { return ctors.size(); }
  DataCtor* getCtor(size_t x) const { return ctors[x]; }
  const std::string getName() { return name; }
};

class IndexableTypeAST : public TypeAST {
protected:
  explicit IndexableTypeAST(const char* tag,
                            const llvm::Type* underlyingType,
                            const SourceRange& sourceRange)
    : TypeAST(tag, underlyingType, sourceRange) {}
  virtual ~IndexableTypeAST() {}

public:
  virtual void show(PrettyPrintTypePass* pass) = 0;
  virtual void dump(DumpTypeToProtobufPass* pass) = 0;

  virtual TypeAST*& getContainedType(int idx) = 0;
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
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const;

  TypeAST*& getElementType() { return underlyingType; }

  // given (T), returns (ref T)
  static RefTypeAST* get(TypeAST* baseType);
};

class FnTypeAST : public TypeAST {
  TypeAST* returnType;
  std::vector<TypeAST*> argTypes;
  std::map<std::string, std::string> annots;

public:
  explicit FnTypeAST(TypeAST* returnType,
                     const std::vector<TypeAST*>& argTypes,
                     std::map<std::string, std::string> annots);

  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const;

  TypeAST*& getParamType(int i) { return argTypes[i]; }
  TypeAST* getParamType(int i) const { return argTypes[i]; }
  TypeAST*& getReturnType() { return returnType; }
  TypeAST* getReturnType() const { return returnType; }
  int getNumParams() const { return argTypes.size(); }

  std::map<std::string, std::string>
        getAnnots() const { return annots; }
  const llvm::FunctionType* getLLVMFnType() const;

  void markAsClosure() { annots["proc"] = "false"; }
  void markAsProc()    { annots["proc"] = "true"; }
  bool isMarkedAsClosure() const;

  llvm::CallingConv::ID getCallingConventionID() const;
  std::string           getCallingConventionName() const;
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
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMTypeUnboxed() const;
  virtual const llvm::Type* getLLVMType() const;

  virtual int getNumContainedTypes() const { return parts.size(); }
  virtual int64_t getNumElements()   const { return parts.size(); }
  virtual TypeAST*& getContainedType(int i);

  static TupleTypeAST* get(const std::vector<TypeAST*>& parts);
};

class TypeTypeAppAST : public IndexableTypeAST {
  std::vector<TypeAST*> parts;

  explicit TypeTypeAppAST(const std::vector<TypeAST*>& parts,
                          const SourceRange& sourceRange)
    : IndexableTypeAST("TypeTypeApp", NULL, sourceRange),
      parts(parts) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const;

  virtual int getNumContainedTypes() const { return parts.size(); }
  virtual int64_t getNumElements()   const { return parts.size(); }
  virtual TypeAST*& getContainedType(int i);

  static TypeTypeAppAST* get(const std::vector<TypeAST*>& parts);
};


class CoroTypeAST : public TypeAST {
  TypeAST* a;
  TypeAST* b;

  explicit CoroTypeAST(TypeAST* targ, TypeAST* tret, const SourceRange& sr)
    : TypeAST("CoroType", NULL, sr),
      a(targ), b(tret) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const;

  virtual int getNumContainedTypes() const { return 2; }
  virtual TypeAST*& getContainedType(int i);

  static CoroTypeAST* get(TypeAST* targ, TypeAST* tret);
};

class CArrayTypeAST : public TypeAST {
  TypeAST* cell;
  uint64_t size;

  explicit CArrayTypeAST(TypeAST* tcell, int64_t size, const SourceRange& sr)
    : TypeAST("CArrayType", NULL, sr),
      cell(tcell), size(size) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const;

  uint64_t getSize() { return size; }
  virtual int getNumContainedTypes() const { return 1; }
  virtual TypeAST*& getContainedType(int i);

  static CArrayTypeAST* get(TypeAST* tcell, uint64_t size);
};


class ArrayTypeAST : public TypeAST {
  TypeAST* cell;
  uint64_t size;

  explicit ArrayTypeAST(TypeAST* tcell, const SourceRange& sr)
    : TypeAST("ArrayType", NULL, sr),
      cell(tcell) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual void dump(DumpTypeToProtobufPass* pass);
  virtual const llvm::Type* getLLVMType() const;
  static  const llvm::Type* getZeroLengthTypeRef(const llvm::Type* t);
  static  const llvm::Type* getSizedArrayTypeRef(const llvm::Type* t, int64_t n);

  virtual int getNumContainedTypes() const { return 1; }
  virtual TypeAST*& getContainedType(int i);

  static ArrayTypeAST* get(TypeAST* tcell);
};

#endif // header guard

