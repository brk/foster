// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "TypecheckPass.h"
#include "FosterAST.h"

#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"

using llvm::Type;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;

#include <vector>

using std::vector;

void TypecheckPass::visit(BoolAST* ast) {
  ast->type = LLVMTypeFor("i1");
}

void TypecheckPass::visit(IntAST* ast) {
  ast->type = LLVMTypeFor("i32");
}

void TypecheckPass::visit(VariableAST* ast) {
  // TODO
}

void TypecheckPass::visit(BinaryExprAST* ast) {
  ast->LHS->accept(this); const llvm::Type* TL = ast->LHS->type;
  ast->RHS->accept(this); const llvm::Type* TR = ast->RHS->type;

  const std::string& op = ast->op;
  
  if (TL != TR) {
    std::cerr << "Error: binary expr " << op << " had differently typed sides!" << std::endl;
  } else if (!TL) {
    std::cerr << "Error: binary expr " << op << " failed to typecheck subexprs!" << std::endl;
  } else {
    if (op == "<" || op == "==" || op == "!=") {
      ast->type = LLVMTypeFor("i1");
    } else {
      ast->type = TL;
    }
  }
}

void TypecheckPass::visit(PrototypeAST* ast) {
  // Make the function type
  const IntegerType* returnType = Type::getInt32Ty(getGlobalContext()); // TODO
  
  vector<const Type*> argTypes;
  for (int i = 0; i < ast->inArgs.size(); ++i) {
    ast->inArgs[i]->accept(this);
    const Type* ty =  ast->inArgs[i]->type;
    if (ty == NULL) {
      std::cerr << "Error: fn proto's Type creation failed due to "
        << "null type for arg '" << ast->inArgs[i]->Name << "'" << std::endl;
    }
    argTypes.push_back(ty);
  }
  
  ast->type = FunctionType::get(returnType, argTypes, false);
}


void TypecheckPass::visit(FnAST* ast) {
  ast->Proto->accept(this); bool p = ast->Proto->type != NULL;
  ast->Body->accept(this);  bool b = ast->Body->type  != NULL;
  
  if (p && b) {
    ast->type = ast->Proto->type;
  }
}

void TypecheckPass::visit(IfExprAST* ast) {
  ast->ifExpr->accept(this);
  const Type* ifType = ast->ifExpr->type;
  if (!ifType) {
    std::cerr << "if condition '" << *(ast->ifExpr) << "' had null type!" << std::endl;
    return;  
  }
  
  if (ifType != LLVMTypeFor("i1")) {
    std::cerr << "if condition '"      << *(ast->ifExpr) << "' "
              << "had non-bool type "  << *ifType << std::endl;
    return;
  }
  
  ast->thenExpr->accept(this); const Type* thenType = ast->thenExpr->type;
  ast->elseExpr->accept(this); const Type* elseType = ast->elseExpr->type;
  
  if (thenType == NULL) {
    std::cerr << "IfExprAST had null type for 'then' expression" << std::endl;
    return;
  } else if (elseType == NULL) {
    std::cerr << "IfExprAST had null type for 'else' expression" << std::endl;
    return;
  } else if (thenType != elseType) {
    std::cerr << "IfExprAST had different (incompatible?) types for then/else exprs" << std::endl;
    return;
  } else if (thenType == elseType) {
    ast->type = thenType;
  }
}

void TypecheckPass::visit(SubscriptAST* ast) {
  IntAST* idx = dynamic_cast<IntAST*>(ast->index);
  if (!idx) {
    std::cerr << "Error: SubscriptAST had non-constant index." << std::endl;
    return;
  }
  
  ast->base->accept(this);
  
  const Type* baseType = ast->base->type;
  if (!baseType) {
    std::cerr << "Error: Cannot index into object of null type " << std::endl;
    return;
  }
  
  if (!baseType->isAggregateType()) {
    std::cerr << "Error: Cannot index into non-aggregate type " << *baseType << std::endl;
    return;
  }
  const llvm::StructType* structTy = llvm::dyn_cast<llvm::StructType>(baseType);
  if (!structTy) {
    std::cerr << "Error: attempt to index into a non-struct type " << *baseType << std::endl;
    return;
  }
  
  idx->accept(this);
  Value* vidx = idx->getConstantValue();
  if (!structTy->indexValid(vidx)) {
    std::cerr << "Error: attempt to index struct with invalid index '" << *vidx << "'" << std::endl;
    return;
  }
  std::cout << "\t\t\t\t150* " << std::endl;
  ast->type = structTy->getTypeAtIndex(vidx);
}

void TypecheckPass::visit(SeqAST* ast) {
  bool success = true;
  for (int i = 0; i < ast->exprs.size(); ++i) {
    if (ast->exprs[i]) {
      ast->exprs[i]->accept(this);
      if (!ast->exprs[i]->type) { success = false; }
    } else {
      std::cerr << "Null expr in SeqAST" << std::endl;
      return;
    }
  }

  if (!success || ast->exprs.empty()) { return; }

  ast->type = ast->exprs[ast->exprs.size() - 1]->type;
}

void TypecheckPass::visit(CallAST* ast) {
  ast->base->accept(this);
  const Type* baseType = ast->base->type;
  if (baseType == NULL) {
    std::cerr << "Error: CallAST base expr had null type:\n\t" << *(ast->base) << std::endl;
    return;
  }
  
  const llvm::FunctionType* baseFT = llvm::dyn_cast<const llvm::FunctionType>(baseType);
  if (baseFT == NULL) {
    std::cerr << "Error: CallAST base expr had non-function type " << *baseType << std::endl;
    return;
  }
  
  int numParams = baseFT->getNumParams();
  if (numParams != ast->args.size()) {
    std::cerr << "Error: arity mismatch; " << ast->args.size() << " args provided"
      << " for function taking " << numParams << " args." << std::endl;
    return;
  }
  
  bool success = true;
  for (int i = 0; i < numParams; ++i) {
    if (!ast->args[i]) {
      std::cerr << "Null arg " << i << " for CallAST" << std::endl;
      success = false;
    } else {
      ast->args[i]->accept(this);
      if (!ast->args[i]->type) {
        std::cerr << "Error: arg " << i << " (" << *(ast->args[i]) << ") had null type" << std::endl;
        success = false;
      }
    }
  }
  
  if (!success) { return; }
  
  for (int i = 0; i < numParams; ++i) {
    const Type* formalType = baseFT->getParamType(i);
    const Type* actualType = ast->args[i]->type;
    if (formalType != actualType) {
      success = false;
      std::cerr << "Type mismatch between actual and formal arg " << i << std::endl;
      std::cerr << "\tformal: " << *formalType << "; actual: " << *actualType << std::endl;
    }
  }
 
  if (success) {
    ast->type = llvm::dyn_cast<const llvm::FunctionType>(baseType)->getReturnType();
  }
}

void TypecheckPass::visit(TupleExprAST* ast) {
  if (!ast->body) {
    std::cerr << "Tuple expr has null body!" << std::endl;
    return;
  }
  
  ast->body->accept(this);
  
  bool success = true;
  std::vector<const Type*> tupleFieldTypes;
  for (int i = 0; i < ast->body->exprs.size(); ++i) {
    const Type* ty =  ast->body->exprs[i]->type;
    if (!ty) {
      std::cerr << "Tuple expr had null constituent type for subexpr " << i << std::endl;
      success = false;
      break;
    }
    tupleFieldTypes.push_back(ty);
  }
  if (success) {
    const Type* structTy = llvm::StructType::get(getGlobalContext(), tupleFieldTypes, /*isPacked=*/false);
    ast->type = structTy;
  }
}

void TypecheckPass::visit(BuiltinCompilesExprAST* ast) {
  ast->expr->accept(this);
  ast->status = (ast->expr->type != NULL) ? ast->kWouldCompile : ast->kWouldNotCompile;
  ast->type = LLVMTypeFor("i1");
}

