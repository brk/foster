// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_H
#define FOSTER_TYPE_AST_H

#include "parse/FosterKindAST.h"

#include "llvm/IR/CallingConv.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"

#include <map>
#include <vector>

using foster::SourceRange;

struct ExprAST;
class  TypeAST;
class  FnTypeAST;
class  RefTypeAST;
class  StructTypeAST;

struct ValAbs;

// This is the (prefix) struct type for a foster coro.
extern llvm::Type* foster_generic_coro_t;
extern llvm::Type* foster_generic_split_coro_ty;
extern StructTypeAST* foster_generic_coro_ast;

struct PrettyPrintTypePass;

std::string str(const TypeAST* type);

TypeAST* getGenericClosureEnvType();
RefTypeAST* getUnitType();

class TypeAST {
protected:
  mutable llvm::Type* repr;
  const SourceRange sourceRange;

  explicit TypeAST(const char* tag,
                   llvm::Type* underlyingType,
                   const SourceRange& sourceRange)
    : repr(underlyingType), sourceRange(sourceRange), tag(tag) {}
  virtual ~TypeAST();
public:
  const char* const tag;
  const SourceRange& getSourceRange() const { return sourceRange; }
  virtual llvm::Type* getLLVMType() const { return repr; }

  virtual const FnTypeAST*     castFnTypeAST() const { return NULL; }
  virtual const StructTypeAST* castStructTypeAST() const { return NULL; }
  virtual const RefTypeAST*    castPtrTypeAST() const { return NULL; }
  virtual bool isGarbageCollectible() const { return false; }

  virtual void show(PrettyPrintTypePass*    pass) = 0;

  static TypeAST* i(int n);
};

class PrimitiveTypeAST : public TypeAST {
  const std::string name; // Used for pretty printing
  static std::map<llvm::Type*, TypeAST*> thinWrappers;
public:
  explicit PrimitiveTypeAST(const std::string& typeName,
                            llvm::Type* underlyingType,
                            const SourceRange& sourceRange)
  : TypeAST("PrimitiveType", underlyingType, sourceRange), name(typeName) {}

  virtual void show(PrettyPrintTypePass* pass);
  const std::string getName() { return name; }
  virtual llvm::Type* getLLVMType() const { return this->repr; }
  static TypeAST* get(const std::string& name, llvm::Type* loweredType);
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
  const std::string getName() { return name; }
  virtual llvm::Type* getLLVMType() const;
  TypeAST* getType() const { return namedType; }
  virtual bool isGarbageCollectible() const { return getType()->isGarbageCollectible(); }
};

struct DataCtor {
  std::string name;
  std::vector<TypeAST*> types;
};

class DataTypeAST : public TypeAST {
  const std::string name;
  const std::vector<DataCtor*> ctors;
  //mutable llvm::OpaqueType* opaq;

public:
  explicit DataTypeAST(const std::string& typeName,
                       std::vector<DataCtor*> ctors,
                       const SourceRange& sourceRange)
     : TypeAST("DataTypeAST", NULL, sourceRange),
       name(typeName), ctors(ctors) /*, opaq(NULL)*/ {}

  virtual void show(PrettyPrintTypePass* pass);
  const std::string getName() { return name; }
  virtual llvm::Type* getLLVMType() const; // don't use this one!
  virtual bool isGarbageCollectible() const { return true; }
};

class IndexableTypeAST : public TypeAST {
protected:
  explicit IndexableTypeAST(const char* tag,
                            llvm::Type* underlyingType,
                            const SourceRange& sourceRange)
    : TypeAST(tag, underlyingType, sourceRange) {}
  virtual ~IndexableTypeAST() {}

public:
  virtual void show(PrettyPrintTypePass* pass) = 0;

  virtual TypeAST*& getContainedType(int idx) = 0;
};

class RefTypeAST : public TypeAST {
  TypeAST* underlyingType;

  explicit RefTypeAST(TypeAST* underlyingType,
                      const SourceRange& sourceRange)
    : TypeAST("RefType", NULL, sourceRange),
      underlyingType(underlyingType) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual llvm::Type* getLLVMType() const;
  virtual const RefTypeAST*    castPtrTypeAST() const { return this; }

  TypeAST*& getElementType() { return underlyingType; }
  const TypeAST* getElementTypeC() const { return underlyingType; }

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
  virtual llvm::Type* getLLVMType() const;

  virtual const FnTypeAST*     castFnTypeAST() const { return this; }

  TypeAST*& getParamType(int i) { return argTypes[i]; }
  TypeAST* getParamType(int i) const { return argTypes[i]; }
  TypeAST*& getReturnType() { return returnType; }
  TypeAST* getReturnType() const { return returnType; }
  int getNumParams() const { return argTypes.size(); }

  std::map<std::string, std::string>
        getAnnots() const { return annots; }
  llvm::FunctionType* getLLVMFnType() const;

  void markAsProc()    { annots["proc"] = "true"; }
  bool isMarkedAsClosure() const;

  llvm::CallingConv::ID getCallingConventionID() const;
  std::string           getCallingConventionName() const;
};

class StructTypeAST : public IndexableTypeAST {
  std::vector<TypeAST*> parts;
  std::vector<llvm::Type*> getLoweredTypes() const;
public:
  explicit StructTypeAST(const std::vector<TypeAST*>& parts,
                         const SourceRange& sourceRange)
    : IndexableTypeAST("StructType", NULL, sourceRange), parts(parts) {}

  explicit StructTypeAST(std::string name, const SourceRange& sourceRange);

  virtual void show(PrettyPrintTypePass* pass);
  virtual llvm::Type* getLLVMType() const;
  llvm::StructType* getLLVMStructType() const;

  virtual const StructTypeAST* castStructTypeAST() const { return this; }

  virtual int getNumContainedTypes() const { return parts.size(); }
  virtual TypeAST*& getContainedType(int i);
  TypeAST* getContainedType(int i) const { return parts.at(i); }

  static StructTypeAST* get(const std::vector<TypeAST*>& parts);

  // Different interface, mirroring LLVM 3.0's named structs, for creating
  // recursive named structs without using an intervening NamedType.
  static StructTypeAST* getRecursive(std::string name);
  void setBody(const std::vector<TypeAST*>& argTypes);
};

class CoroTypeAST : public TypeAST {
  TypeAST* a;
  TypeAST* b;

  explicit CoroTypeAST(TypeAST* targ, TypeAST* tret, const SourceRange& sr)
    : TypeAST("CoroType", NULL, sr),
      a(targ), b(tret) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual llvm::Type* getLLVMType() const;

  virtual int getNumContainedTypes() const { return 2; }
  virtual TypeAST*& getContainedType(int i);

  static CoroTypeAST* get(TypeAST* targ, TypeAST* tret);
};

class ArrayTypeAST : public TypeAST {
  TypeAST* cell;
  uint64_t size;

  explicit ArrayTypeAST(TypeAST* tcell, const SourceRange& sr)
    : TypeAST("ArrayType", NULL, sr),
      cell(tcell) {}

public:
  virtual void show(PrettyPrintTypePass* pass);
  virtual llvm::Type* getLLVMType() const;
  
  virtual int getNumContainedTypes() const { return 1; }
  virtual TypeAST*& getContainedType(int i);

  static  llvm::StructType* getZeroLengthType(TypeAST* t);
  static  llvm::StructType* getSizedArrayType(llvm::Type* t, int64_t n);

  static ArrayTypeAST* get(TypeAST* tcell);
};

#endif // header guard

