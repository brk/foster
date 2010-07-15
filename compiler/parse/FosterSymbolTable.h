// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_SYMBOL_TABLE_H
#define FOSTER_SYMBOL_TABLE_H

#include "llvm/Value.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/GraphWriter.h"

#include <string>
#include <map>
#include <vector>

using std::string;

struct TypeAST;
struct ExprAST;

namespace foster {

template <typename T>
struct NameResolver {
  virtual T* lookup(const string& name, const string& meta) = 0;
  virtual ~NameResolver() {}
};

// Implements persistent lexical scopes using a cactus stack arrangement
template <typename T>
class SymbolTable : public NameResolver<T> {
public:
  class LexicalScope : public NameResolver<T> {
    string name;
    typedef std::map<string, T*> Map;
    Map val_of;
  public:
    LexicalScope* parent;
    
    LexicalScope(string name, LexicalScope* parent) : name(name), parent(parent) {}
    virtual ~LexicalScope() {}
    
    T* insert(const string& ident, T* V) { val_of[ident] = V; return V; }
    T* lookup(const string& ident, const string& wantedScopeName) {
      if (name == "*" || wantedScopeName == "" || name == wantedScopeName) {
        typename Map::iterator it = val_of.find(ident);
        if (it != val_of.end()) {
          return (*it).second;
        }
      }
      if (parent) {
        return parent->lookup(ident, wantedScopeName);
      } else {
        return NULL;
      }
    }
    void dump(std::ostream& out) {
      out << "\t" << name << "(@ " << this << ")" << std::endl;
      for (const_iterator it = begin(); it != end(); ++it) {
        out << "\t\t" << (*it).first << ": " << (*it).second << std::endl;
      }
      if (parent) { parent->dump(out); }
    }

    // These methods allow lexical scopes to be treated as LLVM graph nodes:
    size_t getNumSuccessors() { return 1; }
    LexicalScope* getSuccessor(size_t i) { return parent; }
    LexicalScope* getParent() { return parent; }
    const std::string& getName() const { return name; }

    // These allow graphs to include detailed information about scope contents
    typedef typename Map::const_iterator const_iterator;
    const_iterator begin() const { return val_of.begin(); }
    const_iterator end  () const { return val_of.end(); }
  };

  SymbolTable() {
    pushExistingScope(new LexicalScope("*", NULL));
    _private_allScopes.push_back(currentScope());
  }

  virtual ~SymbolTable() {}

  T* lookup(const string& ident, const string& wantedScopeName) {
    return currentScope()->lookup(ident, wantedScopeName);
  }

  T* insert(string ident, T* V) { return currentScope()->insert(ident, V); }

  LexicalScope* pushScope(string scopeName) {
    currentScope() = new LexicalScope(scopeName, currentScope());
    _private_allScopes.push_back(currentScope());
    return currentScope();
  }

  LexicalScope* popScope() {
    currentScope() = currentScope()->parent;
    return currentScope();
  }


  void pushExistingScope(LexicalScope* scope) {
    scopeStack.push_back(scope);
  }
  void popExistingScope(LexicalScope* expectedCurrentScope) {
    ASSERT(currentScope() == expectedCurrentScope);
    scopeStack.pop_back();
  }

  void dump(std::ostream& out) { currentScope()->dump(out); }

  // need to expose these as public for GraphTraits and friends
  LexicalScope* _private_getCurrentScope() { return currentScope(); }
  std::vector<LexicalScope*> _private_allScopes;

  private:
  LexicalScope*& currentScope() { return scopeStack.back(); }
  std::vector<LexicalScope*> scopeStack;
};

// {{{ |scope| maps names (var/fn) to llvm::Value*/llvm::Function*
extern SymbolTable<llvm::Value> scope;
extern SymbolTable<TypeAST> typeScope;
extern SymbolTable<ExprAST> varScope;
// }}}

} // namespace foster

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

#include "FosterSymbolTableTraits-inl.h"

using foster::scope;
using foster::typeScope;
using foster::varScope;

#endif // header guard
