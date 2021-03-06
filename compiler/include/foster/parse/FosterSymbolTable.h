// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_SYMBOL_TABLE_H
#define FOSTER_SYMBOL_TABLE_H

#include "base/Assert.h"

#include <string>
#include <map>
#include <set>
#include <vector>

using std::string;

class TypeAST;

namespace llvm {
  class Value;
  class raw_ostream;
}

namespace foster {

// Implements persistent lexical scopes using a cactus stack arrangement
template <typename T>
class SymbolTable {
public:
  class LexicalScope {
    string name;
    // This reference is threaded through all newly-created scopes.
    std::set<LexicalScope*>& parentSymbolTableScopes;
    typedef std::map<string, T*> Map;
    Map val_of;

    LexicalScope(string name, LexicalScope* parent)
      : name(name),
        parentSymbolTableScopes(parent->parentSymbolTableScopes),
        parent(parent) {
      if (parentSymbolTableScopes.count(parent) == 1
          && name != "llvm intrinsics") {
        // Don't include LLVM intrinsics in DOT graphs of our
        // symbol table, since they make it large and unwieldy.
        parentSymbolTableScopes.insert(this);
      }
    }
  public:
    // This constructor is needed to create the root scope,
    // where we have no non-NULL parent scope to initialize from.
    LexicalScope(string name, std::set<LexicalScope*>& scopes)
      : name(name), parentSymbolTableScopes(scopes), parent(NULL) {
      parentSymbolTableScopes.insert(this);
    }

    LexicalScope* newNestedScope(const string& name) {
      return new LexicalScope(name, this);
    }

    LexicalScope* parent;

    virtual ~LexicalScope() {}

    void remove(const string& ident) {
      val_of.erase(ident);
    }

    T* insert(const string& ident, T* V, const std::string& msg) {
      T* old = val_of[ident];
      ASSERT(!old) << "Alpha conversion failed: should never insert"
                      " the same name (" << ident << ") in the same scope twice!"
                   << "\n" << msg;
      val_of[ident] = V;
      return V;
    }

    bool thisLevelContains(const string& ident) {
      return val_of.find(ident) != val_of.end();
    }

    virtual T* lookup(const string& ident) {
      auto it = val_of.find(ident);
      if (it != val_of.end()) {
        return it->second;
      }

      if (parent) {
        return parent->lookup(ident);
      } else {
        return NULL;
      }
    }

    void dump(llvm::raw_ostream& out) {
      out << "\t" << name << "(@ " << this << ")" << "\n";
      for (auto it : val_of) {
        out << "\t\t" << it.first << ": " << it.second << "\n";
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
    pushExistingScope(new LexicalScope("*", _private_allScopes));
  }

  virtual ~SymbolTable() {}

  virtual T* lookup(const string& ident) {
    return currentScope()->lookup(ident);
  }

  void remove(const string& ident) {
    currentScope()->remove(ident);
  }

  /// Inserts the given value into the current scope.
  T* insert(string ident, T* V, const std::string& errmsg) {
      return currentScope()->insert(ident, V, errmsg);
  }

  /// Creates and returns a new scope within the current scope.
  LexicalScope* pushScope(string scopeName) {
    return currentScope() = currentScope()->newNestedScope(scopeName);
  }

  /// Returns to the current scope's parent,
  /// undoing the effect of pushScope().
  LexicalScope* popScope() {
    return currentScope() = currentScope()->parent;
  }

  /// Creates a new scope chain, with the root scope node as its parent.
  /// NOTE: the inverse operation is popExistingScope(), not popScope()!
  LexicalScope* newScope(string scopeName) {
    scopeStack.push_back(getRootScope()->newNestedScope(scopeName));
    return currentScope();
  }

  /// Updates the current scope to be the given scope;
  /// the previous current scope is remembered, not overwritten.
  void pushExistingScope(LexicalScope* scope) {
    scopeStack.push_back(scope);
  }

  /// Undoes the effect of a pushExistingScope(), sanity-checking
  /// that we're popping the same scope the caller thinks we are.
  void popExistingScope(LexicalScope* expectedCurrentScope) {
    ASSERT(currentScope() == expectedCurrentScope);
    scopeStack.pop_back();
  }

  LexicalScope* getRootScope() { return scopeStack[0]; }

  void dump(llvm::raw_ostream& out) { currentScope()->dump(out); }

  // need to expose these as public for GraphTraits and friends
  LexicalScope* _private_getCurrentScope() { return currentScope(); }
  std::set<LexicalScope*> _private_allScopes;

  private:
  LexicalScope*& currentScope() { return scopeStack.back(); }
  std::vector<LexicalScope*> scopeStack;
};

// }}}

} // namespace foster

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////


#endif // header guard
