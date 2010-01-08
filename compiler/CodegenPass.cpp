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

template <typename T>
T getSaturating(llvm::Value* v) {
  // If the value requires more bits than T can represent, we want
  // to return ~0, not 0. Otherwise, we should leave the value alone.
  T allOnes = ~T(0);
  if (!v) {
    std::cerr << "numericOf() got a null value, returning " << allOnes << std::endl;
    return allOnes;
  }
  
  if (ConstantInt* ci = llvm::dyn_cast<ConstantInt>(v)) {
    return static_cast<T>(ci->getLimitedValue(allOnes));
  } else {
    std::cerr << "numericOf() got a non-constant-int value " << *v << ", returning " << allOnes << std::endl;
    return allOnes;
  }
}

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
    std::cout << "Fn param " << ast->inArgs[i]->Name << " ; " 
              << ast->inArgs[i] << " has val " << ast->inArgs[i]->value 
              << ", associated with " << AI << std::endl;
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
    //llvm::verifyFunction(*F);
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

Value* getElementFromStruct(Value* structValue, Value* idxValue) {
  const Type* structType = structValue->getType();
  if (llvm::isa<llvm::PointerType>(structType)) {
    // Pointers to composites are indexed via getelementptr
    // TODO: "When indexing into a (optionally packed) structure,
    //        only i32 integer constants are allowed. When indexing
    //        into an array, pointer or vector, integers of any width
    //        are allowed, and they are not required to be constant."
    //   -- http://llvm.org/docs/LangRef.html#i_getelementptr
    std::vector<Value*> idx;
    idx.push_back(ConstantInt::get(Type::getInt32Ty(getGlobalContext()), 0));
    idx.push_back(idxValue);
  
    Value* gep = builder.CreateGEP(structValue, idx.begin(), idx.end(), "subgep");
    return builder.CreateLoad(gep, "subgep_ld");
  } else if (llvm::isa<llvm::StructType>(structType)
          && llvm::isa<llvm::Constant>(idxValue)) {
    // Struct values may be indexed by constant expressions
    unsigned uidx = getSaturating<unsigned>(idxValue);
    return builder.CreateExtractValue(structValue, uidx, "subexv");
  } else {
    std::cerr << "Cannot index into value type " << *structType << " with non-constant index " << *idxValue << std::endl;
    return NULL;
  }
}

void CodegenPass::visit(SubscriptAST* ast) {
  std::cerr << "codegen subscript ast " << (ast->base) << "  [ " << (ast->index) << " ] " << std::endl;
  std::cerr <<                "\t\t\t" << *(ast->base) <<   "[" << *(ast->index) << "]" << std::endl;
  
  (ast->index)->accept(this);
  std::cerr << "codegen subscript value is " << ast->index->value << std::endl;
  
  (ast->base)->accept(this);
  std::cerr << "codgen base value is " << ast->base->value << " = " << *(ast->base->value) << " : " << *(ast->base->value->getType()) << std::endl;
  
  ast->value = getElementFromStruct(ast->base->value, ast->index->value);
  
  std::cerr << "done codegen subscript " << std::endl;
}

////////////////////////////////////////////////////////////////////

void appendArg(std::vector<Value*>& valArgs, Value* V, const FunctionType* FT) {
  std::cout << "actual arg " << valArgs.size() << " = " << *V << " has type " << *(V->getType()) << std::endl;
  std::cout << "formal arg " << valArgs.size() << " has type " << *(FT->getParamType(valArgs.size())) << std::endl;
  
  const Type* formalType = FT->getParamType(valArgs.size());
  if (llvm::isa<llvm::StructType>(formalType)) {
    // Is the formal parameter a pass-by-value struct and the provided argument
    // a pointer to the same kind of struct? If so, load the struct into a virtual
    // register in order to pass it to the function...
    if (llvm::PointerType::get(formalType, 0) == V->getType()) {
      V = builder.CreateLoad(V, "loadStructParam");
    }
  }
  
  valArgs.push_back(V);
}

void unpackArgs(std::vector<Value*>& valArgs, Value* V, const FunctionType* FT) {
  const llvm::StructType* st = llvm::dyn_cast<llvm::StructType>(V->getType());
  if (!st) {
    const llvm::PointerType* pt = llvm::dyn_cast<llvm::PointerType>(V->getType());
    if (pt) {
      st = llvm::dyn_cast<llvm::StructType>(pt->getTypeAtIndex(0U));
    }
  }
  
  if (!st) {
    // Recursively called; base case for non-structs is direct insertion
    appendArg(valArgs, V, FT);
  } else for (int j = 0; j < st->getNumElements(); ++j) {
    // appendArg(...) for non-recursive unpack
    unpackArgs(valArgs, getElementFromStruct(V, ConstantInt::get(Type::getInt32Ty(getGlobalContext()), j)), FT);
  }
}

void CodegenPass::visit(CallAST* ast) {
  std::cout << "\t" << "Codegen CallAST "  << (ast->base) << std::endl;
  std::cout << "\t\t\t"  << *(ast->base) << std::endl;
  
  (ast->base)->accept(this);
  Value* FV = ast->base->value;
  
  Function* F = llvm::dyn_cast_or_null<Function>(FV);
  if (!F) {
    std::cerr << "base: " << *(ast->base) << "; FV: " << FV << std::endl;
    std::cerr << "Unknown function referenced";
    return;
  }
  
  const FunctionType* FT = F->getFunctionType();
  
  std::vector<Value*> valArgs;
  for (int i = 0, argNum = 0; i < ast->args.size(); ++i) {
    // Args checked for nulls during typechecking
    UnpackExprAST* u = dynamic_cast<UnpackExprAST*>(ast->args[i]);
    
    ExprAST* base = (u != NULL) ? u->body : ast->args[i];
    std::cout << "CallAST arg " << i << " u? " << u << std::endl;
    
    base->accept(this);
    Value* V = base->value;
    if (!V) {
      std::cerr << "Error: null value for argument " << i << " found in CallAST codegen!" << std::endl;
      return;
    }
    
    if (u != NULL) {
      unpackArgs(valArgs, V, FT); // Unpack (recursively) nested structs
    } else {
      appendArg(valArgs, V, FT); // Don't unpack even if it's a struct
    }
  }
  
  if (F->arg_size() != valArgs.size()) {
    std::cerr << "Function " << (*(ast->base)) <<  " got " << valArgs.size() << " args, expected "<< F->arg_size();
    return;
  }
  
  ast->value = builder.CreateCall(F, valArgs.begin(), valArgs.end(), "calltmp");
}

void CodegenPass::visit(ArrayExprAST* ast) {
  if (ast->value != NULL) return;
  
  // Create array type
  const llvm::ArrayType* arrayType = llvm::dyn_cast<llvm::ArrayType>(ast->type);
  
  module->addTypeName(freshName("arrayTy"), arrayType);
  using llvm::GlobalVariable;
  GlobalVariable* gvar = new GlobalVariable(*module,
    /*Type=*/         arrayType,
    /*isConstant=*/   true,
    /*Linkage=*/      llvm::GlobalValue::PrivateLinkage,
    /*Initializer=*/  0, // has initializer, specified below
    /*Name=*/         freshName("arrayGv"));

  // Constant Definitions
  std::vector<llvm::Constant*> arrayElements;
  SeqAST* body = dynamic_cast<SeqAST*>(ast->body);
  for (int i = 0; i < body->exprs.size(); ++i) {
    IntAST* v = dynamic_cast<IntAST*>(body->exprs[i]);
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
  
  ast->value = gvar;
}

void CodegenPass::visit(TupleExprAST* ast) {
  if (ast->value != NULL) return;
  
  // Create struct type underlying tuple
  const Type* tupleType = ast->type;
  module->addTypeName(freshName("tuple"), tupleType);
  
  // Allocate tuple space
  llvm::AllocaInst* pt = builder.CreateAlloca(tupleType, 0, "s");
  
  SeqAST* body = dynamic_cast<SeqAST*>(ast->body);
  for (int i = 0; i < body->exprs.size(); ++i) {
    std::cout << "Tuple GEP init i = " << i << "/" << body->exprs.size() << std::endl;
    
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    body->exprs[i]->accept(this);
    builder.CreateStore(body->exprs[i]->value, dst, /*isVolatile=*/ false);
  }
  
  ast->value = pt;
}

// TODO: need tests for unpack outside of call
void CodegenPass::visit(UnpackExprAST* ast) {
  std::cerr << "Error: Cannot codegen an UnpackExprAST outside of a function call!" << std::endl;
}

void CodegenPass::visit(BuiltinCompilesExprAST* ast) {
  if (ast->status == ast->kWouldCompile) {
    ast->value = ConstantInt::getTrue(getGlobalContext());
  } else if (ast->status == ast->kWouldNotCompile) {
    ast->value = ConstantInt::getFalse(getGlobalContext());
  } else {
    std::cerr << "Error: __COMPILES__ expr not checked!" << std::endl; 
    ast->value = ConstantInt::getFalse(getGlobalContext());
  }
}
