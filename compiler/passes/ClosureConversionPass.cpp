// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "ClosureConversionPass.h"
#include "TypecheckPass.h"
#include "FosterAST.h"

#include <vector>
#include <map>
#include <set>

using namespace std;

// Which function are we currently examining?
vector<FnAST*> callStack;
map<FnAST*, set<VariableAST*> > boundVariables;
map<FnAST*, set<VariableAST*> > freeVariables;
map<FnAST*, vector<CallAST*> > callsOf;

void closureConvertAnonymousFunctions(FnAST* ast);

void ClosureConversionPass::visit(BoolAST* ast)                { return; }
void ClosureConversionPass::visit(IntAST* ast)                 { return; }
void ClosureConversionPass::visit(VariableAST* ast)            {
  if (boundVariables[callStack.back()].count(ast) == 0) {
    //std::cout << "Marking variable " <<ast->Name << " as free in fn " << callStack.back()->Proto->Name << std::endl;
    freeVariables[callStack.back()].insert(ast);
  }
  return;
}
void ClosureConversionPass::visit(UnaryOpExprAST* ast)         { return; }
void ClosureConversionPass::visit(BinaryOpExprAST* ast)        { return; }
void ClosureConversionPass::visit(PrototypeAST* ast)           {

  for (int i = 0; i < ast->inArgs.size(); ++i) {
    boundVariables[callStack.back()].insert(ast->inArgs[i]);
    //std::cout << "Marking variable " << ast->inArgs[i]->Name << " as bound in fn " << callStack.back()->Proto->Name << std::endl;
    onVisitChild(ast, ast->inArgs[i]);
  }
  for (int i = 0; i < ast->outArgs.size(); ++i) {
    boundVariables[callStack.back()].insert(ast->outArgs[i]);
    // named out variables aren't mutable so kinda useless...
    // ... but they are "free" if we don't claim them here
    onVisitChild(ast, ast->outArgs[i]);

  }

}
void ClosureConversionPass::visit(FnAST* ast)                  {
  callStack.push_back(ast);
  onVisitChild(ast, ast->Proto);
  onVisitChild(ast, ast->Body);
  closureConvertAnonymousFunctions(ast);
  callStack.pop_back();
}
void ClosureConversionPass::visit(IfExprAST* ast)              {
  onVisitChild(ast, ast->ifExpr);
  onVisitChild(ast, ast->thenExpr);
  onVisitChild(ast, ast->elseExpr);
}
void ClosureConversionPass::visit(SubscriptAST* ast)           { return; }
void ClosureConversionPass::visit(SimdVectorAST* ast)          { return; }
void ClosureConversionPass::visit(SeqAST* ast)                 { return; }
void ClosureConversionPass::visit(CallAST* ast)                {
  ExprAST* base = ast->parts[0];
  FnAST* fnBase = dynamic_cast<FnAST*>(base);
  if (fnBase) {
    std::cout << "visited direct call of fn " << fnBase->Proto->Name << ", nested? " << fnBase->wasNested << std::endl;
    callsOf[fnBase].push_back(ast);
  } else {
    VariableAST* varBase = dynamic_cast<VariableAST*>(base);
    if (varBase) {
      std::cout << "visited call of var named " << varBase->Name << std::endl;
    }
  }
  visitChildren(ast); return;
}
void ClosureConversionPass::visit(ArrayExprAST* ast)           { return; }
void ClosureConversionPass::visit(TupleExprAST* ast)           { return; }
void ClosureConversionPass::visit(UnpackExprAST* ast)          { return; }
void ClosureConversionPass::visit(BuiltinCompilesExprAST* ast) { return; }

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

void closureConvertAnonymousFunctions(FnAST* ast) {
  string& name = ast->Proto->Name;

  if (name.find("<anon_fn") == 0) {
    std::cout << "\t\tClosure conversion found an anonymous function: " << name << std::endl;
    ast->wasNested = true;
  } else { return; }

  set<VariableAST*>::iterator it;
  // Find the set of free variables for this function
  set<VariableAST*>& freeVars = freeVariables[ast];
  vector<CallAST*>& calls = callsOf[ast];

  for (it = freeVars.begin(); it != freeVars.end(); ++it) {
    // For each free variable in the function,
    std::cout << "Free var in " << name << ": " << (*it)->Name << std::endl;

    // add a parameter to the function prototype
    appendParameter(ast->Proto, *it);

    if (ast->Proto->type) {
      // and updates the types of the prototype and function itself, if they already have types
      {
         TypecheckPass p; ast->Proto->accept(&p);
         // We just typecheck the prototype and not the function
         // to avoid re-typechecking the function body, which should not
         // have been affected by this change.
         ast->type = ast->Proto->type;
      }
    }


    // and rewrite all usages inside the function?

    // and rewrite all call sites to pass the extra parameter
    for (int i = 0; i < calls.size(); ++i) {
      appendParameter(calls[i], *it);
    }
  }

  FnAST* parentFn = dynamic_cast<FnAST*>(ast->parent);
  name.replace(0, 1, "<" + parentFn->Proto->Name + "__");
}
