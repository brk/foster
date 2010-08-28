// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"

#include "passes/CaptureAvoidingSubstitution.h"
#include "passes/ClosureConversionPass.h"
#include "passes/ReplaceExprTransform.h"
#include "passes/PrettyPrintPass.h"
#include "passes/TypecheckPass.h"
#include "passes/CodegenPass.h"

#include "parse/FosterAST.h"
#include "parse/CompilationContext.h"

#include "parse/FosterUtils.h"

using foster::show;
using foster::EDiag;

#include <vector>
#include <map>
#include <set>
#include <string>

using namespace std;


#include "parse/ExprASTVisitor.h"

struct ClosureConversionPass : public ExprASTVisitor {
  #include "parse/ExprASTVisitor.decls.inc.h"
  std::set<std::string> globalNames;
  ModuleAST* toplevel;

  std::vector<FnAST*> newlyHoistedFunctions;
  ClosureConversionPass(const std::set<std::string>& globalNames,
                        ModuleAST* toplevel)
     : globalNames(globalNames), toplevel(toplevel) {}

  ~ClosureConversionPass() {
    // Hoist newly-closed function definitions to the top level
    for (size_t i = 0; i < newlyHoistedFunctions.size(); ++i) {
      toplevel->parts.push_back( newlyHoistedFunctions[i] );
    }
  }
  
  // If an anonymous function is in a closure, we don't want to
  // perform lambda-lifting, because closure conversion subsumes
  // the non-hoisting part of the lifting conversion.
  set<FnAST*> fnInClosure;
};

namespace foster {
  void performClosureConversion(const std::set<std::string>& globalNames,
                                ModuleAST* mod) {
    ClosureConversionPass p(globalNames, mod);
    mod->accept(&p); 
  }
}

// Which function are we currently examining?
vector<FnAST*> callStack;
map<FnAST*, set<string> > boundVariables;
map<FnAST*, set<string> > freeVariables;
typedef set<CallAST*> CallSet;
map<FnAST*, CallSet> callsOf;



void replaceOldWithNew(ExprAST* inExpr, ExprAST* oldExpr, ExprAST* newExpr) {
  ReplaceExprTransform rex;
  rex.staticReplacements[oldExpr] = newExpr;
  inExpr->accept(&rex);
}

FnAST* parentFnOf(FnAST* fn) {
  ExprAST* parent = fn->parent;
  while (parent) {
    if (FnAST* fp = dynamic_cast<FnAST*>(parent)) { return fp; }
    parent = parent->parent;
  }
  return NULL;
}

void foundFreeVariableIn(VariableAST* var, FnAST* scope) {
  // Mark the variable as being free in all parent scopes in which the
  // variable has not been marked as bound. This handles the case in which
  // a variable is free in a parent scope but only appears in a nested scope.
  do {
    freeVariables[scope].insert(var->getName());

    scope = parentFnOf(scope);
  } while (scope != NULL && boundVariables[scope].count(var->getName()) == 0);
}

void performClosureConversion(ClosureAST* ast, ClosureConversionPass* ccp);
void lambdaLiftAnonymousFunction(FnAST* ast, ClosureConversionPass* ccp);
bool isAnonymousFunction(FnAST* ast);

void ClosureConversionPass::visit(BoolAST* ast)                { return; }
void ClosureConversionPass::visit(IntAST* ast)                 { return; }
void ClosureConversionPass::visit(VariableAST* ast)            {
  if (callStack.empty()) {
    return;
  }

  if (boundVariables[callStack.back()].count(ast->getName()) == 0
    && this->globalNames.count(ast->getName()) == 0) {
    foundFreeVariableIn(ast, callStack.back());
  }
  
  return;
}
void ClosureConversionPass::visit(UnaryOpExprAST* ast)         { return; }
void ClosureConversionPass::visit(BinaryOpExprAST* ast)        { return; }
void ClosureConversionPass::visit(PrototypeAST* ast)           {
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    boundVariables[callStack.back()].insert(ast->inArgs[i]->getName());
    onVisitChild(ast, ast->inArgs[i]);
  }
}

void ClosureConversionPass::visit(FnAST* ast)                  {
  callStack.push_back(ast);
    onVisitChild(ast, ast->getProto());
    // Ensure that this function is not a free variable in its own body
    this->globalNames.insert(ast->getProto()->name);
    onVisitChild(ast, ast->getBody());
  callStack.pop_back();

  if (isAnonymousFunction(ast)) {
    // Rename anonymous functions to reflect their lexical scoping
    FnAST* parentFn = dynamic_cast<FnAST*>(ast->parent);
    if (parentFn != NULL) {
      ast->getProto()->name.replace(0, 1, "<" + parentFn->getProto()->name + ".");
    }

    if (fnInClosure.count(ast) > 0) {
      // don't lambda lift if we're doing closure conversion!
    } else {
      lambdaLiftAnonymousFunction(ast, this);
    }
  }
}

void ClosureConversionPass::visit(ClosureAST* ast) {
  if (ast->hasKnownEnvironment) {
    visitChildren(ast);
  } else {
    fnInClosure.insert(ast->fn);
    ast->fn->accept(this);
    performClosureConversion(ast, this);
  }
}
void ClosureConversionPass::visit(ModuleAST* ast)              {
  for (ModuleAST::FnAST_iterator
       it  = ast->fn_begin();
       it != ast->fn_end(); ++it) {
    (*it)->accept(this);
  }
}
void ClosureConversionPass::visit(NamedTypeDeclAST* ast) {
  return;
}
void ClosureConversionPass::visit(IfExprAST* ast)              {
  visitChildren(ast);
}
void ClosureConversionPass::visit(ForRangeExprAST* ast) {
  onVisitChild(ast, ast->getStartExpr());
  onVisitChild(ast, ast->getEndExpr());
  onVisitChild(ast, ast->getIncrExpr());

  // TODO this isn't very elegant...
  const string& varName = ast->var->getName();
  bool wasAlreadyBound = 1 == boundVariables[callStack.back()].count(varName);
  boundVariables[callStack.back()].insert(varName);
  onVisitChild(ast, ast->getBodyExpr());
  if (!wasAlreadyBound) {
    boundVariables[callStack.back()].erase(varName);
  }
}
void ClosureConversionPass::visit(NilExprAST* ast)             { return; }
void ClosureConversionPass::visit(RefExprAST* ast)             { return; }
void ClosureConversionPass::visit(DerefExprAST* ast)           { return; }
void ClosureConversionPass::visit(AssignExprAST* ast)          { return; }
void ClosureConversionPass::visit(SubscriptAST* ast)           { return; }
void ClosureConversionPass::visit(SimdVectorAST* ast)          { return; }
void ClosureConversionPass::visit(SeqAST* ast)                 { return; }
void ClosureConversionPass::visit(CallAST* ast)                {
  ExprAST* base = ast->parts[0];
  if (ClosureAST* cloBase = dynamic_cast<ClosureAST*>(base)) {
    std::cout << "visited direct call of closure, replacing with fn... "
              << *base << std::endl;
    replaceOldWithNew(cloBase->parent, cloBase, cloBase->fn);
    std::cout << *(cloBase->parent) << std::endl;
    base = ast->parts[0] = cloBase->fn;
  }
  if (FnAST* fnBase = dynamic_cast<FnAST*>(base)) {
    std::cout << "visited direct call of fn " << fnBase->getProto()->name << std::endl;
    callsOf[fnBase].insert(ast);
  }
  visitChildren(ast);
}
//void ClosureConversionPass::visit(ArrayExprAST* ast)           { return; }
void ClosureConversionPass::visit(TupleExprAST* ast)           { return; }
void ClosureConversionPass::visit(BuiltinCompilesExprAST* ast) { return; }

void prependParameter(PrototypeAST* ast, VariableAST* var) {
  ast->inArgs.insert(ast->inArgs.begin(), var);
}

VariableAST* appendParameter(PrototypeAST* ast, VariableAST* var) {
  // This is a bad-lazy hack; closure-converted functions only codegen properly
  // because the variable referenced inside the function happens to have the same
  // name we give it here. Properly, we should probably add a new variable with a
  // distinct name to the prototype, and rewrite references to the old var in the fn body.
  ast->inArgs.push_back(var);
  return var;
}

void appendParameter(CallAST* call, VariableAST* var) {
  call->parts.push_back(var);
}

bool isAnonymousFunction(FnAST* ast) {
  string& name = ast->getProto()->name;
  if (name.find("<anon_fn") == 0) {
    return true;
  } else { return false; }
}

// Looks up the bindings for the free variable names in the given function.
set<VariableAST*> freeVariablesOf(FnAST* ast) {
  set<VariableAST*> rv;
  const set<string>& freeVars = freeVariables[ast];
  for (set<string>::iterator it = freeVars.begin(); it != freeVars.end(); ++it) {
    const string& varName = *it;
    foster::SymbolInfo* info = ast->getProto()->scope->lookup(varName, "");
    VariableAST* var = dynamic_cast<VariableAST*>(info->ast);
    ASSERT(var) << "free variables must be variables! But " << varName
                 << " was " << show(info->ast);
    rv.insert(var);
  }
  return rv;
}

void hoistAnonymousFunction(FnAST* ast, ClosureConversionPass* ccp) {
  // TODO support mutually recursive function...
  ccp->newlyHoistedFunctions.push_back(ast);

  ast->parent = NULL;
  
  {
    // Alter the symbol table structure to reflect the fact that we're
    // hoisting the function to the root scope.
    ast->getProto()->scope->parent = gScope.getRootScope();

    // Ensure that the fn proto gets added to the module, so that it can
    // be referenced from other functions.
    CodegenPass cp; ast->getProto()->accept(&cp);

    gScopeInsert(ast->getProto()->name, ast->getProto()->value);
  }
}

void performClosureConversion(ClosureAST* closure,
                              ClosureConversionPass* ccp) {
  FnAST* ast = closure->fn;
  //llvm::outs() << "Closure converting function" << ast->getProto()->name
  //             << " @ " << ast << "\n";

  // Find the set of free variables for the function
  set<VariableAST*> freeVars = freeVariablesOf(ast);

  // Create a record to contain the free variables
  std::vector<TypeAST*> envTypes;
  Exprs envExprs;

  // The first entry in the environment is just a placeholder for the typemap.
  // We must embed a typemap in the environment so the garbage collector
  // will be able to handle the closure in functions that can be passed
  // closures with multiple different environments.
  NilExprAST* nilptr = new NilExprAST(foster::SourceRange::getEmptyRange());
  nilptr->type = RefTypeAST::get(TypeAST::i(8));
  envTypes.push_back(nilptr->type);
  envExprs.push_back(nilptr);

  set<VariableAST*>::iterator it;
  for (it = freeVars.begin(); it != freeVars.end(); ++it) {
    envTypes.push_back((*it)->type);
    envExprs.push_back(*it);
  }

  TupleTypeAST* envTy = TupleTypeAST::get(envTypes);

  // Make (a pointer to) this record be the function's first parameter.
  VariableAST* envVar = new VariableAST(freshName("env"),
                              RefTypeAST::get(envTy),
                              ast->sourceRange);

  prependParameter(ast->getProto(), envVar);
  
  ExprAST* derefedEnvPtr = new DerefExprAST(envVar, envVar->sourceRange);
  derefedEnvPtr->type = envTy;

  // Rewrite the function body to make all references to free vars
  // instead go through the passed env pointer.
  {
    ReplaceExprTransform rex;
    int envOffset = 1; // offset 0 is reserved for typemamp
    for (it = freeVars.begin(); it != freeVars.end(); ++it) {
      std::cout << "Rewriting " << *(*it) << " to go through env" << std::endl;
      captureAvoidingSubstitution(ast->getBody(),
                                  (*it)->name,
                                  new SubscriptAST(
                                        derefedEnvPtr,
                                        literalIntAST(envOffset, (*it)->sourceRange),
                                        (*it)->sourceRange),
                                  boundVariables);
      ++envOffset;
    }
  }

  // Rewrite all calls to indirect through the code pointer
  // ... is handled directly at CallAST nodes during codegen

  if (ast->getProto()->type) {
    // and updates the types of the prototype and function itself,
    // if they already have types.
    {
      typecheck(ast->getProto());
      std::cout << "ClosureConversionPass: updating type from "
                 << str(ast->type->getLLVMType())
                 << " to\n\t" << str(ast->getProto()->type->getLLVMType()) << std::endl;
      ast->type = ast->getProto()->type;
    }
  }

  closure->parts = envExprs;
  closure->hasKnownEnvironment = true;
  hoistAnonymousFunction(ast, ccp);
}

void lambdaLiftAnonymousFunction(FnAST* ast, ClosureConversionPass* ccp) { 
  //llvm::outs() << "Lambda lifting function" << ast->getProto()->name
  //             << " @ " << ast << "\n";
             
  set<VariableAST*> freeVars = freeVariablesOf(ast);
  CallSet& calls = callsOf[ast];

  set<VariableAST*>::iterator it;
  for (it = freeVars.begin(); it != freeVars.end(); ++it) {
    // For each free variable in the function:
    VariableAST* parentScopeVar = *it;
    VariableAST* var = new VariableAST(
                             parentScopeVar->name,
                             parentScopeVar->type,
                             foster::SourceRange::getEmptyRange());

    // add a parameter to the function prototype
    appendParameter(ast->getProto(), var);

    // and rewrite all usages inside the function
    {
      ReplaceExprTransform rex;
      rex.staticReplacements[parentScopeVar] = var;
      ast->getBody()->accept(&rex);
      // This rewriting must be done even if the variable maintains
      // the same name so that llvm::Values from the inner function
      // don't leak out via the 'scope' table to calling functions.
    }

    // and rewrite all external call sites to pass the extra parameter
    for (CallSet::iterator it = calls.begin(); it != calls.end(); ++it) {
      appendParameter(*it, parentScopeVar);
    }
  }

  if (ast->getProto()->type) {
    // and updates the types of the prototype and function itself,
    // if they already have types
    {
      typecheck(ast->getProto());

      // We just typecheck the prototype and not the function
      // to avoid re-typechecking the function body, which should not
      // have been affected by this change.
      ast->type = ast->getProto()->type;
    }
  }

  VariableAST* varReferringToFunction = new VariableAST(
                                    ast->getProto()->name,
                                    ast->getProto()->type,
                                    foster::SourceRange::getEmptyRange());

  // Rewrite external calls to refer to the function by name.
  for (CallSet::iterator it = calls.begin(); it != calls.end(); ++it) {
    CallAST* call = *it;
    ASSERT(call->parts[0] = ast);
    call->parts[0] = varReferringToFunction;
  }

  // And move the now-rootless function to the top level, where it belongs.
  hoistAnonymousFunction(ast, ccp);
}
