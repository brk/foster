// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/DerivedTypes.h"

#include "parse/FosterSymbolTable.h"
#include "parse/FosterAST.h"

#include "passes/TypecheckPass.h"

#include "pystring/pystring.h"

namespace foster {

std::set<string> globalNames;

// Add module m's C-linkage functions in the global scopes,
// and also add prototypes to the linkee module.
void putModuleMembersInScope(Module* m, Module* linkee) {
  if (!m) return;

  for (Module::iterator it = m->begin(); it != m->end(); ++it) {
    const Function& f = *it;

    const string& name = f.getNameStr();
    bool isCxxLinkage = pystring::startswith(name, "_Z", 0);

    bool hasDef = !f.isDeclaration();
    if (hasDef && !isCxxLinkage
               && !pystring::startswith(name, "__cxx_", 0)) {
      globalNames.insert(name);

      // Ensure that, when parsing, function calls to this name will find it
      const Type* ty = f.getType();
      // We get a pointer-to-whatever-function type, because f is a global
      // value (therefore ptr), but we want just the function type.
      if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
        ty = pty->getElementType();
      }

      if (const llvm::FunctionType* fnty =
                                      llvm::dyn_cast<llvm::FunctionType>(ty)) {
        // Ensure that codegen for the given function finds the 'declare'
        // TODO make lazy prototype?
        Value* decl = linkee->getOrInsertFunction(
            llvm::StringRef(name),
            fnty,
            f.getAttributes());
        /*
        llvm::outs() << "inserting variable in global scope: " << name << " : "
                  << str(fnty) << "\n";
        */
        gScope.insert(name, new foster::SymbolInfo(
                              new VariableAST(name, TypeAST::reconstruct(fnty),
                                              SourceRange::getEmptyRange()),
                              decl));
      } else {
        ASSERT(false) << "how could a function not have function type?!?";
      }
    }
  }
}

VariableAST* checkAndGetLazyRefTo(PrototypeAST* p) {
  { TypecheckPass typ; p->accept(&typ); }
  VariableAST* fnRef = new VariableAST(p->name, p->type,
                              SourceRange::getEmptyRange());
  fnRef->lazilyInsertedPrototype = p;

  return fnRef;
}

VariableAST* proto(TypeAST* retTy, const string& fqName) {
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName,
                                    SourceRange::getEmptyRange()));
}

VariableAST* proto(TypeAST* retTy, const string& fqName,
    TypeAST* ty1) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1, SourceRange::getEmptyRange()));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs,
                                    SourceRange::getEmptyRange()));
}

VariableAST* proto(TypeAST* retTy, const string& fqName,
    TypeAST* ty1, TypeAST* ty2) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1, SourceRange::getEmptyRange()));
  inArgs.push_back(new VariableAST("p2", ty2, SourceRange::getEmptyRange()));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs,
                                    SourceRange::getEmptyRange()));
}

VariableAST* proto(TypeAST* retTy, const string& fqName,
    TypeAST* ty1, TypeAST* ty2, TypeAST* ty3) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1, SourceRange::getEmptyRange()));
  inArgs.push_back(new VariableAST("p2", ty2, SourceRange::getEmptyRange()));
  inArgs.push_back(new VariableAST("p3", ty3, SourceRange::getEmptyRange()));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs,
                                    SourceRange::getEmptyRange()));
}

ExprAST* lookupOrCreateNamespace(ExprAST* ns, const string& part) {
  ExprAST* nsPart = ns->lookup(part, "");
  if (nsPart) {
    return nsPart;
  }

  if (NamespaceAST* nr = dynamic_cast<NamespaceAST*>(ns)) {
    return nr->newNamespace(part);
  } else {
    EDiag() << "Error: lookupOrCreateNamespace failed because "
            << " ns did not contain an entry for '" << part << "'"
            << " and ns was not a NamespaceAST*";
  }
  return NULL;
}

void addToProperNamespace(VariableAST* var) {
  const string& fqName = var->name;
  globalNames.insert(fqName);

  std::vector<string> parts;
  pystring::split(fqName, parts, ".");

  ExprAST* ns = gScopeLookupAST(parts[0]);
  if (!ns) {
    llvm::errs() << "Error: could not find root namespace for fqName "
              << fqName << "\n";
    return;
  }

  // Note, we ignore the last component when creating namespaces.
  int nIntermediates = parts.size() - 1;
  for (int i = 1; i < nIntermediates; ++i) {
    ns = lookupOrCreateNamespace(ns, parts[i]);
  }

  // For the leaf name, insert variable ref rather than new namespace
  if (NamespaceAST* parentNS = dynamic_cast<NamespaceAST*>(ns)) {
    parentNS->insert(parts.back(), var);
  } else {
    llvm::errs() << "Error: final parent namespace for fqName '"
              << fqName << "' was not a NamespaceAST" << "\n";
  }
}

void createLLVMBitIntrinsics() {
  // Make the module hierarchy available to code referencing llvm.blah.blah.
  // (The NamespaceAST name is mostly a convenience for examining the AST).
  gScope.insert("llvm", new foster::SymbolInfo(
                           new NamespaceAST("llvm intrinsics",
                                            gScope.getRootScope(),
                                       foster::SourceRange::getEmptyRange())));

  const unsigned i16_to_i64 = ((1<<4)|(1<<5)|(1<<6));
  const unsigned i8_to_i64 = ((1<<3)|i16_to_i64);
  enum intrinsic_kind { kTransform, kOverflow, kAtomicStub };
  struct bit_intrinsic_spec {
    // e.g. "bswap" becomes "llvm.bswap.i16", "llvm.bswap.i32" etc
    const char* intrinsicName;
    const intrinsic_kind kind;
    const unsigned sizeFlags;
  };

  bit_intrinsic_spec spec_table[]  = {
      { "bswap", kTransform, i16_to_i64 },
      { "ctpop", kTransform, i8_to_i64 },
      { "ctlz",  kTransform, i8_to_i64 },
      { "cttz",  kTransform, i8_to_i64 },

      { "uadd.with.overflow", kOverflow, i16_to_i64 },
      { "sadd.with.overflow", kOverflow, i16_to_i64 },
      { "usub.with.overflow", kOverflow, i16_to_i64 },
      { "ssub.with.overflow", kOverflow, i16_to_i64 },
      { "umul.with.overflow", kOverflow, i16_to_i64 },
      { "smul.with.overflow", kOverflow, i16_to_i64 },

      // atomic.cmp.swap gets two int arguments instead of one
      { "atomic.cmp.swap", kAtomicStub, i8_to_i64 },

      // All the other atomic functions get just one int argument
      { "atomic.swap", kAtomicStub, i8_to_i64 },
      { "atomic.load.add", kAtomicStub, i8_to_i64 },
      { "atomic.load.sub", kAtomicStub, i8_to_i64 },
      { "atomic.load.and", kAtomicStub, i8_to_i64 },
      // LLVM's nand intrinsic is misleadingly named for backwards
      // compatibility with GCC 4.2;
      // it computes A & ~B instead of ~(A & B)
      //{ "atomic.load.nand", kAtomicStub, i8_to_i64 },
      { "atomic.load.or", kAtomicStub, i8_to_i64 },
      { "atomic.load.xor", kAtomicStub, i8_to_i64 },
      { "atomic.load.max", kAtomicStub, i8_to_i64 },
      { "atomic.load.min", kAtomicStub, i8_to_i64 },
      { "atomic.load.umax", kAtomicStub, i8_to_i64 },
      { NULL, kTransform, 0}
  };

  addToProperNamespace( proto(TypeAST::i(64), "llvm.readcyclecounter") );

  bit_intrinsic_spec* spec = spec_table;
  while (spec->intrinsicName) {
    unsigned size = 8;
    while (size <= 64) {
      if (size & spec->sizeFlags) {
        TypeAST* ty = TypeAST::i(size);

        std::stringstream ss;
        ss << "llvm." << spec->intrinsicName << ".i" << size;

        if (spec->kind == kTransform) {
          // e.g for declaring i16 @llvm.bswap.i16(i16)
          addToProperNamespace( proto(ty, ss.str(), ty) );
        } else if (spec->kind == kOverflow) {
          std::vector<TypeAST*> params;
          params.push_back(ty);
          params.push_back(TypeAST::i(1));
          TypeAST* retTy = TupleTypeAST::get(params);

          // e.g. for declaring {16,i1} @llvm.sadd.with.overflow.i16(i16, i16)
          addToProperNamespace( proto(retTy, ss.str(), ty, ty) );
        } else if (spec->kind == kAtomicStub) {
          // ss contains something like "llvm.atomic.cmp.swap.i32"
          ss << ".p0i" << size; // now "llvm.atomic.cmp.swap.i32.p0i32"

          if (spec->intrinsicName == string("atomic.cmp.swap")) {
            // e.g. for declaring i32 @llvm.atomic.cmp.swap.i32.p0i32(i32*, i32, i32)
            addToProperNamespace( proto(ty, ss.str(),
                RefTypeAST::get(ty, false), ty, ty) );
          } else {
            // e.g. for declaring i32 @llvm.atomic.load.xor.i32.p0i32(i32*, i32)
            addToProperNamespace( proto(ty, ss.str(),
                RefTypeAST::get(ty, false), ty) );
          }
        }
      }
      size *= 2;
    }
    ++spec;
  }
}

} // namespace foster

