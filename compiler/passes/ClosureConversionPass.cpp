// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"

#include "passes/CaptureAvoidingSubstitution.h"
#include "passes/ClosureConversionPass.h"
#include "passes/ReplaceExprTransform.h"
#include "passes/PrettyPrintPass.h"
#include "passes/TypecheckPass.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/CompilationContext.h"

#include "parse/FosterUtils.h"

#include <vector>
#include <map>
#include <set>
#include <string>

using namespace std;

using foster::show;
using foster::currentOuts;
using foster::currentErrs;
using foster::CompilationContext;

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
  ExprAST* parent = CompilationContext::getParent(fn);
  while (parent) {
    if (FnAST* fp = dynamic_cast<FnAST*>(parent)) { return fp; }
    parent = CompilationContext::getParent(parent);
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

void performClosureConversion(FnAST* ast, ClosureConversionPass* ccp);
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
    this->globalNames.insert(ast->getName());
    onVisitChild(ast, ast->getBody());
  callStack.pop_back();

  llvm::outs() << "isAnonymousFunction " << ast->getName() << " : " << isAnonymousFunction(ast) << "\n";
  llvm::outs() << "isClosure " << ast->getName() << " : " << ast->isClosure() << "\n";

  if (isAnonymousFunction(ast)) {
    // Rename anonymous functions to reflect their lexical scoping
    FnAST* parentFn = dynamic_cast<FnAST*>(CompilationContext::getParent(ast));
    if (parentFn != NULL) {
      ast->getName().replace(0, 1, "<" + parentFn->getName() + ".");
    }

    if (ast->isClosure()) {
      performClosureConversion(ast, this);
    } else {
      lambdaLiftAnonymousFunction(ast, this);
    }
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
void ClosureConversionPass::visit(NilExprAST* ast)             { return; }
void ClosureConversionPass::visit(SubscriptAST* ast)           { return; }
//void ClosureConversionPass::visit(SimdVectorAST* ast)          { return; }
void ClosureConversionPass::visit(SeqAST* ast)                 { return; }
void ClosureConversionPass::visit(CallAST* ast)                {
  ExprAST* base = ast->parts[0];
  if (FnAST* fnBase = dynamic_cast<FnAST*>(base)) {
    currentOuts() << "visited direct call of fn " << fnBase->getName() << "\n";
    // If we have a direct call of a function, then we know
    // for sure that we don't need to form a closure for it,
    // because all of the variables that it might capture are
    // variables that we have access to, and can add as parameters
    // (which is OK, because we know that the function can't be
    //  called from anywhere else).
    // So, we force closure conversion to lambda-lift and hoist it,
    // rather than closure converting it.
    fnBase->removeClosureEnvironment();
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
  string& name = ast->getName();
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
    ExprAST* evar = ast->getProto()->scope->lookup(varName);
    VariableAST* var = dynamic_cast<VariableAST*>(evar);
    ASSERT(var) << "free variables must be variables! But " << varName
                 << " was " << show(evar);
    rv.insert(var);
  }
  return rv;
}

void hoistAnonymousFunction(FnAST* ast, ClosureConversionPass* ccp) {
  ccp->newlyHoistedFunctions.push_back(ast);
  CompilationContext::setParent(ast, NULL);

  // Alter the symbol table structure to reflect the fact that we're
  // hoisting the function to the root scope.
  ast->getProto()->scope->parent = gScope.getRootScope();
}

void performClosureConversion(FnAST* ast,
                              ClosureConversionPass* ccp) {
  llvm::outs() << "Closure converting function" << str(ast);

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

  //ExprAST* derefedEnvPtr = new DerefExprAST(envVar, envVar->sourceRange);
  //derefedEnvPtr->type = envTy;

  // Rewrite the function body to make all references to free vars
  // instead go through the passed env pointer.
  {
    ReplaceExprTransform rex;
    int envOffset = 1; // offset 0 is reserved for typemap
    for (it = freeVars.begin(); it != freeVars.end(); ++it) {
      currentOuts() << "Rewriting " << str(*it) << " to go through env" << "\n";
      captureAvoidingSubstitution(ast->getBody(),
                                  (*it)->name,
                                  new SubscriptAST(
                                        envVar, //derefedEnvPtr,
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
    foster::typecheck(ast->getProto());
    currentOuts() << "ClosureConversionPass: updating type from "
               << str(ast->type->getLLVMType())
               << " to\n\t" << str(ast->getProto()->type->getLLVMType()) << "\n";
    ast->type = ast->getProto()->type;
  }

  *(ast->environmentParts) = envExprs;
  //hoistAnonymousFunction(ast, ccp);
}

void lambdaLiftAnonymousFunction(FnAST* ast, ClosureConversionPass* ccp) {
  llvm::outs() << "Lambda lifting function" << str(ast);

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
      foster::typecheck(ast->getProto());

      // We just typecheck the prototype and not the function
      // to avoid re-typechecking the function body, which should not
      // have been affected by this change.
      ast->type = ast->getProto()->type;
    }
  }

  VariableAST* varReferringToFunction = new VariableAST(
                                    ast->getName(),
                                    ast->getProto()->type,
                                    foster::SourceRange::getEmptyRange());

  // Rewrite external calls to refer to the function by name.
  for (CallSet::iterator it = calls.begin(); it != calls.end(); ++it) {
    CallAST* call = *it;
    ASSERT(call->parts[0] = ast);
    call->parts[0] = varReferringToFunction;
  }

  // And move the now-rootless function to the top level, where it belongs.
  ast->removeClosureEnvironment();
  hoistAnonymousFunction(ast, ccp);
}
