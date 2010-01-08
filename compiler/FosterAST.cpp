// vim: set foldmethod=marker :
// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "FosterAST.h"
#include "llvm/Target/TargetSelect.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Module.h"

#include <map>
#include <vector>
#include <sstream>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;
using llvm::APInt;
using llvm::PHINode;

using std::vector;
using std::string;

llvm::ExecutionEngine* ee;
llvm::IRBuilder<> builder(getGlobalContext());
llvm::Module* module;

FosterSymbolTable scope;
std::map<string, const Type*> NamedTypes;

std::ostream& operator<<(std::ostream& out, ExprAST& expr) {
  return expr.operator<<(out);
}

/** Macros in TargetSelect.h conflict with those from ANTLR... */
void fosterLLVMInitializeNativeTarget() {
  llvm::InitializeNativeTarget();
}

/// Generates a unique name given a template; each template gets a separate
/// sequence of uniquifying numbers either embedded or appended.
string freshName(string like) {
  static std::map<string, int> counts;
  std::stringstream ss;
  int pos = like.find("%d", 0);
  int curr = counts[like]++;
  if (string::npos == pos) { // append uniquifier, if any
    if (curr == 0) {
      ss << like; // Only append integer when we see second copy of symbol
    } else {
      ss << like << curr;
    }
  } else { // If it's a template, make the subtitution, even the first time
    ss << curr; // int>string
    like.replace(pos, pos+2, ss.str());
    ss.str("");
    ss.clear(); // reset
    ss << like;
  }
  return ss.str();
}

Value* ErrorV(const char* Str) {
  fprintf(stderr, "%s\n", Str);
  return NULL;
}

const Type* LLVMType_from(string s) {
  std::clog << "Getting LLVM type for " << s << std::endl;
  if (NamedTypes[s]) return NamedTypes[s];
  fprintf(stderr, "Unknown type in LLVMType_from(%s)\n", s.c_str());
  return NULL;
}

string join(string glue, Exprs args) {
  std::stringstream ss;
  if (args.size() > 0) {
    if (args[0]) {
      ss << *args[0];
    } else {
      ss << "<nil>";
    }
    for (int i = 1; i < args.size(); ++i) {
      ss << glue;
      if (args[i]) {
        ss << *args[i];
      } else {
        ss << "<nil>";
      }
    }
  }
  return ss.str();
}

///////////////////////////////////////////////////////////

Value* IntAST::Codegen() {
  return ConstantInt::get(Type::getInt32Ty(getGlobalContext()),
                          APInt(32u, Clean, Base));
}

Value* BinaryExprAST::Codegen() {
  Value* VL = LHS->Codegen();
  Value* VR = RHS->Codegen();
  if (!VL || !VR) return NULL;

  if (op == "+") { return builder.CreateAdd(VL, VR, "addtmp"); }
  if (op == "-") { return builder.CreateSub(VL, VR, "subtmp"); }
  if (op == "/") { return builder.CreateSDiv(VL, VR, "divtmp"); }
  if (op == "*") { return builder.CreateMul(VL, VR, "multmp"); }
  
  if (op == "<") { return builder.CreateICmpSLT(VL, VR, "slttmp"); }
  if (op == "==") { return builder.CreateICmpEQ(VL, VR, "eqtmp"); }
  if (op == "!=") { return builder.CreateICmpNE(VL, VR, "netmp"); }
  
  if (op == "bitand") { return builder.CreateAnd(VL, VR, "bitandtmp"); }
  if (op == "bitor") {  return builder.CreateOr( VL, VR, "bitortmp"); }
  if (op == "bitxor") { return builder.CreateXor(VL, VR, "bitxortmp"); }
  //if (op == "bitneg") { return builder.CreateNeg(VL, VR, "bitneg"); }
  //if (op == "not") { return builder.CreateNot(VL, VR, "bitneg"); }

  if (op == "shl") { return builder.CreateShl(VL, VR, "shltmp"); }
  if (op == "shr") { return builder.CreateLShr(VL, VR, "shrtmp"); }
  
  std::cerr << "Couldn't gen code for op " << op << endl;
  return NULL;
}

Function* PrototypeAST::Codegen() {
  std::cout << "\t" << "Codegen proto "  << Name << std::endl;
  
  // Make the function type: int(int, ..., int) for now
  const IntegerType* i32_t = Type::getInt32Ty(getGlobalContext());
  vector<const Type*> Ints(inArgs.size(), i32_t);
  FunctionType* FT = FunctionType::get(i32_t, Ints, false);

  Function* F = Function::Create(FT, Function::ExternalLinkage, Name, module);

  if (!F) {
    std::cout << "Function creation failed!" << std::endl;
    return NULL;
  }

  // If F conflicted, there was already something named "Name"
  if (F->getName() != Name) {
    std::cout << "Error: redefinition of function " << Name << std::endl;
    return NULL;
  }

  // Set names for all arguments
  Function::arg_iterator AI = F->arg_begin();
  for (int i = 0; i != inArgs.size(); ++i, ++AI) {
    AI->setName(inArgs[i]);
    //NamedValues[inArgs[i]] = AI;
    std::cout << "Inserting " << inArgs[i] << " in scope" << std::endl;
    scope.insert(inArgs[i], AI);
  }

  return F;
}

#define DEFAULT_ADDRESS_SPACE 0u
Function* FnAST::Codegen() {
  //NamedValues.clear();
  std::cout << "Pushing scope ... " << this->Proto->Name  << std::endl;
  scope.pushScope("fn " + this->Proto->Name);
  Function* F = this->Proto->Codegen();
  if (!F) return F;
  
  // Insert in function-local scope for recursive calls to work
  scope.insert(this->Proto->Name, F);

  BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "entry", F);
  builder.SetInsertPoint(BB);

  Value* RetVal = this->Body->Codegen(); // TODO
  
  std::cout << "Popping scope ... " << this->Proto->Name  << std::endl;
  scope.popScope();
  
  // Insert in parent scope for references from later functions to work
  scope.insert(this->Proto->Name, F);
  std::cerr << "Function '" << this->Proto->Name << "' rv = " << RetVal << std::endl;
  
  if (RetVal) {
    builder.CreateRet(RetVal);
    llvm::verifyFunction(*F);
    return F;
  } else {
    F->eraseFromParent();
    std::cout << "Function '" << this->Proto->Name << "' retval creation failed" << std::endl;
    return NULL;
  }
}

Value* IfExprAST::Codegen() {
  Value* cond = ifExpr->Codegen();
  if (!cond) return NULL;
/*
  cond = builder.CreateICmpNE(cond,
                              ConstantInt::get(getGlobalContext(), APInt(32, 0)),
                              "ifcond");
                              */
  Function *F = builder.GetInsertBlock()->getParent();

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then", F);
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);
  builder.SetInsertPoint(thenBB);

  Value* then = thenExpr->Codegen();
  if (!then) {
    return ErrorV("Codegen for if condition failed due to missing Value for 'then' part");
  }

  builder.CreateBr(mergeBB);
  thenBB = builder.GetInsertBlock();

  F->getBasicBlockList().push_back(elseBB);
  builder.SetInsertPoint(elseBB);

  Value* _else = elseExpr->Codegen();
  if (!_else) {
    return ErrorV("Codegen for if condition failed due to missing Value for 'else' part");
  }

  builder.CreateBr(mergeBB);
  elseBB = builder.GetInsertBlock();

  F->getBasicBlockList().push_back(mergeBB);
  builder.SetInsertPoint(mergeBB);
  //const Type* resultType = LLVMType_from(GetResultTypeName());
  const Type* resultType = Type::getInt32Ty(getGlobalContext());
  PHINode *PN = builder.CreatePHI(resultType, "iftmp");

  PN->addIncoming(then, thenBB);
  PN->addIncoming(_else, elseBB);
  return PN;
}

Value* TupleExprAST::Codegen() {
  if (cachedValue != NULL) return cachedValue;
  
  // Create struct type underlying tuple
  std::vector<const Type*> tupleFieldTypes;
  for (int i = 0; i < body->exprs.size(); ++i) {
    tupleFieldTypes.push_back(Type::getInt32Ty(getGlobalContext()));
  }
  llvm::StructType* tupleType = llvm::StructType::get(getGlobalContext(),
                                                      tupleFieldTypes,
                                                      /*isPacked=*/false);
  module->addTypeName(freshName("tuple"), tupleType);
  
  // Allocate tuple space
  llvm::AllocaInst* pt = builder.CreateAlloca(tupleType, 0, "s");
  
  for (int i = 0; i < body->exprs.size(); ++i) {
    std::cout << "Tuple GEP init i = " << i << "/" << body->exprs.size() << std::endl;
    
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    builder.CreateStore(body->exprs[i]->Codegen(), dst, /*isVolatile=*/ false);
  }
  
  cachedValue = pt;
  return pt;
  //return ConstantInt::get(Type::getInt32Ty(getGlobalContext()), APInt(32u, "123", 10));
}


Value* SubscriptAST::Codegen() {
  if (true) { // ty(base) == struct && ty(index) == int
    std::vector<Value*> idx;
    idx.push_back(ConstantInt::get(Type::getInt32Ty(getGlobalContext()), 0));
    idx.push_back(index->Codegen());
    Value* gep = builder.CreateGEP(base->Codegen(), idx.begin(), idx.end(), "subgep");
    return builder.CreateLoad(gep, "subgep_ld");
  } else {
    std::cerr << "Don't know how to index a <ty(base)> with a <ty(index)>" << std::endl;
  }
}
