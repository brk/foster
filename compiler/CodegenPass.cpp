// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "CodegenPass.h"
#include "FosterAST.h"

#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Analysis/Verifier.h"

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;
using llvm::APInt;
using llvm::PHINode;

void CodegenPass::visit(IntAST* ast) {
  ast->value = ast->getConstantValue();
}

void CodegenPass::visit(BoolAST* ast) {
 ast->value = (ast->boolValue)
      ? ConstantInt::getTrue(getGlobalContext())
      : ConstantInt::getFalse(getGlobalContext());
}

void CodegenPass::visit(VariableAST* ast) {
  if (!ast->value) {
    ast->value = scope.lookup(ast->Name, "");
    if (!ast->value) {
      std::cerr << "Error: Unknown variable name " << ast->Name << std::endl;
    }
  }
}

void CodegenPass::visit(BinaryExprAST* ast) {
  ast->LHS->accept(this); Value* VL = ast->LHS->value;
  ast->RHS->accept(this); Value* VR = ast->RHS->value;
  
  const std::string& op = ast->op;
  
  if (!VL || !VR) {
    std::cerr << "Error: binary expr " << op << " had null subexpr" << std::endl;
    return;
  }
       if (op == "+") { ast->value = builder.CreateAdd(VL, VR, "addtmp"); }
  else if (op == "-") { ast->value = builder.CreateSub(VL, VR, "subtmp"); }
  else if (op == "/") { ast->value = builder.CreateSDiv(VL, VR, "divtmp"); }
  else if (op == "*") { ast->value = builder.CreateMul(VL, VR, "multmp"); }
  
  else if (op == "<") { ast->value = builder.CreateICmpSLT(VL, VR, "slttmp"); }
  else if (op == "==") { ast->value = builder.CreateICmpEQ(VL, VR, "eqtmp"); }
  else if (op == "!=") { ast->value = builder.CreateICmpNE(VL, VR, "netmp"); }
  
  else if (op == "bitand") { ast->value = builder.CreateAnd(VL, VR, "bitandtmp"); }
  else if (op == "bitor") {  ast->value = builder.CreateOr( VL, VR, "bitortmp"); }
  else if (op == "bitxor") { ast->value = builder.CreateXor(VL, VR, "bitxortmp"); }
  //else if (op == "bitneg") { ast->value = builder.CreateNeg(VL, VR, "bitneg"); }
  //else if (op == "not") { ast->value = builder.CreateNot(VL, VR, "bitneg"); }

  else if (op == "shl") { ast->value = builder.CreateShl(VL, VR, "shltmp"); }
  else if (op == "shr") { ast->value = builder.CreateLShr(VL, VR, "shrtmp"); }
  else {
    std::cerr << "Couldn't gen code for op " << op << endl;
  }
}

void CodegenPass::visit(PrototypeAST* ast) {
  std::cout << "\t" << "Codegen proto "  << ast->Name << std::endl;
  const llvm::FunctionType* FT = llvm::dyn_cast<FunctionType>(ast->type);
  Function* F = Function::Create(FT, Function::ExternalLinkage, ast->Name, module);

  if (!F) {
    std::cout << "Function creation failed!" << std::endl;
    return;
  }

  // If F conflicted, there was already something named "Name"
  if (F->getName() != ast->Name) {
    std::cout << "Error: redefinition of function " << ast->Name << std::endl;
    return;
  }

  // Set names for all arguments
  Function::arg_iterator AI = F->arg_begin();
  for (int i = 0; i != ast->inArgs.size(); ++i, ++AI) {
    AI->setName(ast->inArgs[i]->Name);
    scope.insert(ast->inArgs[i]->Name, AI);
  }

  ast->value = F;
}

void CodegenPass::visit(SeqAST* ast) {
  Value* V = NULL;
  for (int i = 0; i < ast->exprs.size(); ++i) {
    if (ast->exprs[i]) {
      (ast->exprs[i])->accept(this);
      V = ast->exprs[i]->value;
    } else {
      std::cerr << "SeqAST::Codegen() saw null seq expression " << i << std::endl;
      break;
    }
  }
  ast->value = V;
}

void CodegenPass::visit(FnAST* ast) {
  std::cout << "Pushing scope ... " << ast->Proto->Name  << std::endl;
  scope.pushScope("fn " + ast->Proto->Name);
  (ast->Proto)->accept(this);
  Function* F = llvm::dyn_cast<Function>(ast->Proto->value);
  if (!F) { return; }
  
  // Insert in function-local scope for recursive calls to work
  scope.insert(ast->Proto->Name, F);

  BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "entry", F);
  builder.SetInsertPoint(BB);

  (ast->Body)->accept(this);
  Value* RetVal = ast->Body->value;
  
  std::cout << "Popping scope ... " << ast->Proto->Name  << std::endl;
  scope.popScope();
  
  // Insert in parent scope for references from later functions to work
  scope.insert(ast->Proto->Name, F);
  std::cerr << "Function '" << ast->Proto->Name << "' rv = " << RetVal << std::endl;
  
  if (RetVal) {
    builder.CreateRet(RetVal);
    llvm::verifyFunction(*F);
    ast->value = F;
  } else {
    F->eraseFromParent();
    std::cout << "Function '" << ast->Proto->Name << "' retval creation failed" << std::endl;
  }
}

void CodegenPass::visit(IfExprAST* ast) {
  (ast->ifExpr)->accept(this); Value* cond = ast->ifExpr->value;
  if (!cond) return;
  
  Function *F = builder.GetInsertBlock()->getParent();

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then", F);
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);
  builder.SetInsertPoint(thenBB);

  (ast->thenExpr)->accept(this);
  Value* then = ast->thenExpr->value;
  if (!then) {
    std::cerr << "Codegen for if condition failed due to missing Value for 'then' part";
    return;
  }

  builder.CreateBr(mergeBB);
  thenBB = builder.GetInsertBlock();

  F->getBasicBlockList().push_back(elseBB);
  builder.SetInsertPoint(elseBB);

  (ast->elseExpr)->accept(this);
  Value* _else = ast->elseExpr->value;
  if (!_else) {
    std::cerr << "Codegen for if condition failed due to missing Value for 'else' part";
    return;
  }

  builder.CreateBr(mergeBB);
  elseBB = builder.GetInsertBlock();

  F->getBasicBlockList().push_back(mergeBB);
  builder.SetInsertPoint(mergeBB);
  
  PHINode *PN = builder.CreatePHI(ast->type, "iftmp");
  PN->addIncoming(then, thenBB);
  PN->addIncoming(_else, elseBB);
  ast->value = PN;
}

void CodegenPass::visit(SubscriptAST* ast) {
  if (true) { // ty(base) == struct && ty(index) == int
    (ast->index)->accept(this);
    
    std::vector<Value*> idx;
    idx.push_back(ConstantInt::get(Type::getInt32Ty(getGlobalContext()), 0));
    idx.push_back(ast->index->value);
    (ast->base)->accept(this);
    Value* gep = builder.CreateGEP(ast->base->value, idx.begin(), idx.end(), "subgep");
    ast->value = builder.CreateLoad(gep, "subgep_ld");
  } else {
    std::cerr << "Don't know how to index a <ty(base)> with a <ty(index)>" << std::endl;
  }
}

void CodegenPass::visit(CallAST* ast) {
  std::cout << "\t" << "Codegen CallAST "  << *(ast->base) << std::endl;
  
  (ast->base)->accept(this);
  Value* FV = ast->base->value;
  
  Function* F = llvm::dyn_cast_or_null<Function>(FV);
  if (!F) {
    std::cerr << "base: " << *(ast->base) << "; FV: " << FV << std::endl;
    std::cerr << "Unknown function referenced";
    return;
  }
  
  if (F->arg_size() != ast->args.size()) {
    std::cerr << "Function " << (*(ast->base)) <<  " got " << ast->args.size() << " args, expected "<< F->arg_size();
    return;
  }
  
  std::vector<Value*> valArgs;
  for (int i = 0; i < ast->args.size(); ++i) {
    (ast->args[i])->accept(this);
    
    Value* V = ast->args[i]->value;
    if (!V) return;
    valArgs.push_back(V);
  }
  
  ast->value = builder.CreateCall(F, valArgs.begin(), valArgs.end(), "calltmp");
}

void CodegenPass::visit(ArrayExprAST* ast) {
  if (ast->value != NULL) return;
  
  // Create array type
  const llvm::ArrayType* arrayType = llvm::dyn_cast<llvm::ArrayType>(ast->type);
  
  module->addTypeName(freshName("arrayTy"), arrayType);
#if 0
  // Allocate tuple space
  llvm::AllocaInst* pt = builder.CreateAlloca(arrayType, 0, "s");
  
  for (int i = 0; i < ast->body->exprs.size(); ++i) {
    std::cout << "Tuple GEP init i = " << i << "/" << ast->body->exprs.size() << std::endl;
    
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    (ast->body->exprs[i])->accept(this);
    builder.CreateStore(ast->body->exprs[i]->value, dst, /*isVolatile=*/ false);
  }
#endif

  using llvm::GlobalVariable;
  GlobalVariable* gvar = new GlobalVariable(*module,
    /*Type=*/         arrayType,
    /*isConstant=*/   true,
    /*Linkage=*/      llvm::GlobalValue::PrivateLinkage,
    /*Initializer=*/  0, // has initializer, specified below
    /*Name=*/         freshName("arrayGv"));

  // Constant Definitions
  std::vector<llvm::Constant*> arrayElements;
  for (int i = 0; i < ast->body->exprs.size(); ++i) {
    IntAST* v = dynamic_cast<IntAST*>(ast->body->exprs[i]);
    if (!v) {
      std::cerr << "Array initializer was not IntAST but instead " << *v << std::endl;
      return;
    }
    
    ConstantInt* ci = llvm::dyn_cast<ConstantInt>(v->getConstantValue());
    if (!ci) {
      std::cerr << "Failed to cast array initializer value to ConstantInt" << std::endl;
      return;
    }
    arrayElements.push_back(ci);
  }
  
  llvm::Constant* constArray = llvm::ConstantArray::get(arrayType, arrayElements);
  gvar->setInitializer(constArray);
  /*
    ConstantInt* i32_1 = ConstantInt::get(APInt(32,  "1", 1, 10));
    ConstantInt* i32_0 = ConstantInt::get(APInt(32,  "0", 1, 10));
    ConstantInt* i32_2 = ConstantInt::get(APInt(32,  "2", 1, 10));
    
    std::vector<Constant*> const_ptr_13_indices;
    const_ptr_13_indices.push_back(i32_0);
    const_ptr_13_indices.push_back(i32_0);
    Constant* const_ptr_13 = ConstantExpr::getGetElementPtr(gvar, &const_ptr_13_indices[0], const_ptr_13_indices.size() );
  
    std::vector<Constant*> const_ptr_14_indices;
    const_ptr_14_indices.push_back(i32_0);
    const_ptr_14_indices.push_back(i32_1);
    Constant* const_ptr_14 = ConstantExpr::getGetElementPtr(gvar, &const_ptr_14_indices[0], const_ptr_14_indices.size() );
    
  
    std::vector<Constant*> const_ptr_16_indices;
    const_ptr_16_indices.push_back(i32_0);
    const_ptr_16_indices.push_back(i32_2);
    Constant* const_ptr_16 = ConstantExpr::getGetElementPtr(gvar, &const_ptr_16_indices[0], const_ptr_16_indices.size() );
  */
  
  ast->value = gvar;
}

void CodegenPass::visit(TupleExprAST* ast) {
  if (ast->value != NULL) return;
  
  // Create struct type underlying tuple
  const Type* tupleType = ast->type;
  module->addTypeName(freshName("tuple"), tupleType);
  
  // Allocate tuple space
  llvm::AllocaInst* pt = builder.CreateAlloca(tupleType, 0, "s");
  
  for (int i = 0; i < ast->body->exprs.size(); ++i) {
    std::cout << "Tuple GEP init i = " << i << "/" << ast->body->exprs.size() << std::endl;
    
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    (ast->body->exprs[i])->accept(this);
    builder.CreateStore(ast->body->exprs[i]->value, dst, /*isVolatile=*/ false);
  }
  
  ast->value = pt;
}

void CodegenPass::visit(BuiltinCompilesExprAST* ast) {
  if (ast->status == ast->kWouldCompile) {
    ast->value = ConstantInt::getTrue(getGlobalContext());
  } else if (ast->status == ast->kWouldNotCompile) {
    ast->value = ConstantInt::getFalse(getGlobalContext());
  } else {
    std::cerr << "Error: __COMPILES__ expr not checked!" << std::endl; 
    //ast->value = ConstantInt::getFalse(getGlobalContext());
  }
}
