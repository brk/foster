// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "ClosureConversionPass.h"
#include "ReplaceExprTransform.h"
#include "TypecheckPass.h"
#include "CodegenPass.h"
#include "FosterAST.h"

#include <vector>
#include <map>
#include <set>
#include <cassert>

using namespace std;

// Which function are we currently examining?
vector<FnAST*> callStack;
map<FnAST*, set<VariableAST*> > boundVariables;
map<FnAST*, set<VariableAST*> > freeVariables;
map<FnAST*, vector<CallAST*> > callsOf;

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
    //std::cout << "Marking variable " << var->name << " as free in fn " << scope->proto->name << std::endl;
    freeVariables[scope].insert(var);

    scope = parentFnOf(scope);
  } while (scope != NULL && boundVariables[scope].count(var) == 0);
}

ClosureAST* closureConvertAnonymousFunction(FnAST* ast);
void lambdaLiftAnonymousFunction(FnAST* ast);
bool isAnonymousFunction(FnAST* ast);

void ClosureConversionPass::visit(BoolAST* ast)                { return; }
void ClosureConversionPass::visit(IntAST* ast)                 { return; }
void ClosureConversionPass::visit(VariableAST* ast)            {
  if (callStack.empty()) {
    return;
  }

  if (boundVariables[callStack.back()].count(ast) == 0
    && this->globalNames.count(ast->name) == 0) {
    foundFreeVariableIn(ast, callStack.back());
  }
  return;
}
void ClosureConversionPass::visit(UnaryOpExprAST* ast)         { return; }
void ClosureConversionPass::visit(BinaryOpExprAST* ast)        { return; }
void ClosureConversionPass::visit(PrototypeAST* ast)           {
  for (int i = 0; i < ast->inArgs.size(); ++i) {
    boundVariables[callStack.back()].insert(ast->inArgs[i]);
    //std::cout << "Marking variable " << ast->inArgs[i]->name << " as bound in fn " << callStack.back()->proto->name << std::endl;
    onVisitChild(ast, ast->inArgs[i]);
  }
}

void ClosureConversionPass::visit(FnAST* ast)                  {
  std::cout << "ClosureConversionPass visiting FnAST" << std::endl;

  callStack.push_back(ast);
    onVisitChild(ast, ast->proto);
    // Ensure that this function is not a free variable in its own body
    this->globalNames.insert(ast->proto->name);
    onVisitChild(ast, ast->body);
  callStack.pop_back();

  std::cout << "ClosureConversionPass leaving FnAST" << std::endl;
  
  if (isAnonymousFunction(ast)) {
    // Rename anonymous functions to reflect their lexical scoping
    FnAST* parentFn = dynamic_cast<FnAST*>(ast->parent);
    if (parentFn != NULL) {
      ast->proto->name.replace(0, 1, "<" + parentFn->proto->name + ".");
    }
    
    //std::cout << "Anonymous function, lift (1) or convert (0)?  : " << ast->lambdaLiftOnly << std::endl;
    if (ast->lambdaLiftOnly) {
      lambdaLiftAnonymousFunction(ast);
    } else {
      std::cout << "Anon function not wanting lambda lifting: " << ast->proto->name << std::endl;
      //closureConvertAnonymousFunction(ast);
    }
  }
}



void ClosureConversionPass::visit(ClosureTypeAST* ast) {
  std::cout << "ClosureConversionPass::visit(ClosureTypeAST* ast" << std::endl;
  onVisitChild(ast, ast->proto);
}

ClosureAST* closureConvertFunction(ClosureConversionPass* pass, FnAST* ast) {
  callStack.push_back(ast);
    pass->onVisitChild(ast, ast->proto);
    // Ensure that this function is not a free variable in its own body
    pass->globalNames.insert(ast->proto->name);
    pass->onVisitChild(ast, ast->body);
  callStack.pop_back();

  ClosureAST* cl = closureConvertAnonymousFunction(ast);
  return cl;
}

void ClosureConversionPass::visit(ClosureAST* ast) {
  std::cout << "ClosureConversionPass visiting ClosureAST" << std::endl;
  if (ast->hasKnownEnvironment) {
    visitChildren(ast);
  } else {
    std::cout << "ClosureConversionPass::visit(ClosureAST* ast fn..." << std::endl;
    std::cout << "\tproto: " << *(ast->fn->proto) << std::endl;
    ClosureAST* nu = closureConvertFunction(this, ast->fn);
    ast->parts = nu->parts;
    ast->fn    = nu->fn;
    ast->hasKnownEnvironment = true;
    std::cout << "ClosureConversionPass::visit(ClosureAST fn ..." << std::endl;
  }
  std::cout << "ClosureConversionPass leaving ClosureAST" << std::endl;
}
void ClosureConversionPass::visit(IfExprAST* ast)              {
  onVisitChild(ast, ast->testExpr);
  onVisitChild(ast, ast->thenExpr);
  onVisitChild(ast, ast->elseExpr);
}
void ClosureConversionPass::visit(SubscriptAST* ast)           { return; }
void ClosureConversionPass::visit(SimdVectorAST* ast)          { return; }
void ClosureConversionPass::visit(SeqAST* ast)                 { return; }
void ClosureConversionPass::visit(CallAST* ast)                {
  ExprAST* base = ast->parts[0];
  if (ClosureAST* cloBase = dynamic_cast<ClosureAST*>(base)) {
    std::cout << "visited direct call of closure, replacing with fn... " << *base << std::endl;
    replaceOldWithNew(cloBase->parent, cloBase, cloBase->fn);
    std::cout << *(cloBase->parent) << std::endl;
    base = ast->parts[0] = cloBase->fn;
  }
  if (FnAST* fnBase = dynamic_cast<FnAST*>(base)) {
    std::cout << "visited direct call of fn " << fnBase->proto->name << ", nested? " << fnBase->wasNested << std::endl;
    fnBase->lambdaLiftOnly = true;
    callsOf[fnBase].push_back(ast);
  } else {
    if (VariableAST* varBase = dynamic_cast<VariableAST*>(base)) {
      //std::cout << "visited call of var named " << varBase->name << std::endl;
    }
  }
  visitChildren(ast); return;
}
void ClosureConversionPass::visit(ArrayExprAST* ast)           { return; }
void ClosureConversionPass::visit(TupleExprAST* ast)           { return; }
void ClosureConversionPass::visit(UnpackExprAST* ast)          { return; }
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
  string& name = ast->proto->name;
  if (name.find("<anon_fn") == 0) {
    std::cout << "\t\tClosure conversion found an anonymous function: " << name << std::endl;
    ast->wasNested = true;
    return true;
  } else { return false; }
}

ExprAST* getTopLevel(ExprAST* ast) {
  while (ast->parent) ast = ast->parent;
  return ast;
}

void hoistAnonymousFunction(FnAST* ast, ExprAST* replacement) {
  // Hoist newly-closed function definitions to the top level
  ExprAST* toplevel = getTopLevel(ast);
  if (SeqAST* topseq = dynamic_cast<SeqAST*>(toplevel)) {
    // TODO support mutually recursive function...
    topseq->parts.push_back(ast);
    //scope.insert(ast->proto->name, ast->value);
  } else {
    std::cerr << "ClosureConversionPass: Uh oh, root expression wasn't a seq!" << std::endl;
  }

  // and replace their old definitions with a variable reference
  //std::cout << "Hoisting/replacing " << ast->proto->name << std::endl;
  replaceOldWithNew(ast->parent, ast, replacement);
  ast->parent = toplevel;

  { // Ensure that the fn proto gets added to the module, so that it can
    // be referenced from other functions.
    CodegenPass cp; ast->proto->accept(&cp);
  }
}

ClosureAST* closureConvertAnonymousFunction(FnAST* ast) {
  std::cout << "Closure converting function" << *ast << std::endl;
  std::cout << "Type: " << *(ast->type) << std::endl;

  // Find the set of free variables for the function
  set<VariableAST*>& freeVars = freeVariables[ast];

  // Create a record to contain the free variables
  std::vector<const Type*> envTypes;
  Exprs envExprs;

  set<VariableAST*>::iterator it;
  for (it = freeVars.begin(); it != freeVars.end(); ++it) {
    std::cout << "Free var: " <<     *(*it) << std::endl;
    std::cout << "Free var ty: " << *((*it)->type) << std::endl;
    std::cout << std::endl;
    envTypes.push_back((*it)->type);
    envExprs.push_back(*it);
  }

  llvm::StructType* envTy = llvm::StructType::get(getGlobalContext(), envTypes, /*isPacked=*/ false);
  llvm::PointerType* envPtrTy = llvm::PointerType::get(envTy, 0);

  std::cout << "Env ptr ty: " << *envPtrTy << std::endl;
  
  // Make (a pointer to) this record be the function's first parameter.
  VariableAST* envVar = new VariableAST("env", envPtrTy);
  prependParameter(ast->proto, envVar);

  // Rewrite the function body to make all references to freeVar
  // instead go through the passed env
  {
    ReplaceExprTransform rex;
    int offset = 0;
    for (it = freeVars.begin(); it != freeVars.end(); ++it) {
      std::cout << "Rewriting " << *(*it) << " to go through env" << std::endl;
      rex.staticReplacements[*it] = new SubscriptAST(envVar, literalIntAST(offset));
      ++offset;
    }
    ast->body->accept(&rex);
  }

  // Rewrite all calls to indirect through the code pointer
  // ... is handled directly at CallAST nodes during codegen

  if (ast->proto->type) {
    // and updates the types of the prototype and function itself, if they already have types
    {
       TypecheckPass p; ast->proto->accept(&p);
       std::cout << "ClosureConversionPass: updating type from " << *(ast->type)
                  << " to\n\t" << *(ast->proto->type) << std::endl;
       ast->type = ast->proto->type;
    }
  }

  ClosureAST* closure = new ClosureAST(ast, envExprs);
  hoistAnonymousFunction(ast, closure);
  { TypecheckPass tp; closure->accept(&tp); }
  return closure;
}

void lambdaLiftAnonymousFunction(FnAST* ast) {
  set<VariableAST*>& freeVars = freeVariables[ast];
  vector<CallAST*>& calls = callsOf[ast];

  set<VariableAST*>::iterator it;
  for (it = freeVars.begin(); it != freeVars.end(); ++it) {
    // For each free variable in the function:

    // add a parameter to the function prototype
    appendParameter(ast->proto, *it);

    // and rewrite all usages inside the function?

    // and rewrite all call sites to pass the extra parameter
    for (int i = 0; i < calls.size(); ++i) {
      appendParameter(calls[i], *it);
    }
  }

  if (ast->proto->type) {
    // and updates the types of the prototype and function itself, if they already have types
    {
       TypecheckPass p; ast->proto->accept(&p);
       // We just typecheck the prototype and not the function
       // to avoid re-typechecking the function body, which should not
       // have been affected by this change.
       ast->type = ast->proto->type;
    }
  }

  //hoistAnonymousFunctionAndReplaceWith(ast, new VariableAST(ast->proto->name, ast->type));
}
