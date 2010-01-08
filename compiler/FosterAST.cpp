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

FosterSymbolTable<Value> scope;
FosterSymbolTable<const Type> typeScope;
FosterSymbolTable<ExprAST> varScope;

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

const Type* LLVMTypeFor(const string& name) { return module->getTypeByName(name); }

void initModuleTypeNames() {
  module->addTypeName("i32", llvm::IntegerType::get(getGlobalContext(), 32));
  module->addTypeName("i1", llvm::IntegerType::get(getGlobalContext(), 1));
  
  /*
  std::vector<const Type*> StringParts;
  StringParts.push_back(Type::Int32Ty);
  StringParts.push_back(PointerType::get(Type::Int8Ty, DEFAULT_ADDRESS_SPACE));
  module->addTypeName("String", StructType::get(StringParts));
  */

  //const unsigned DEFAULT_ADDRESS_SPACE = 0u;
  //module->addTypeName("String",
  //  llvm::PointerType::get(Type::getInt8Ty(gcon), DEFAULT_ADDRESS_SPACE));
}

///////////////////////////////////////////////////////////

const llvm::Type* IntAST::GetType() {
  return llvm::IntegerType::get(getGlobalContext(), 32);
}

Value* IntAST::Codegen() {
  return ConstantInt::get(this->GetType(), APInt(32u, Clean, Base));
}

//////////////////////////////////////////////////////////

Value* BoolAST::Codegen() {
  return (value)
    ? ConstantInt::getTrue(getGlobalContext())
    : ConstantInt::getFalse(getGlobalContext());
}

//////////////////////////////////////////////////////////

bool BinaryExprAST::Sema() {
  return this->GetType()->isInteger();
}

const llvm::Type* BinaryExprAST::GetType() {
  const llvm::Type* TL = LHS->GetType();
  const llvm::Type* TR = RHS->GetType();
  if (TL != TR) {
    std::cerr << "Error: binary expr " << op << " had differently typed sides!" << std::endl;
    return NULL;
  } else if (!TL) {
    std::cerr << "Error: binary expr " << op << " failed to typecheck subexprs!" << std::endl;
    return NULL;
  } else {
    if (op == "<" || op == "==" || op == "!=") {
      return LLVMTypeFor("i1");
    } else {
      return TL;
    }
  }
}

Value* BinaryExprAST::Codegen() {
  Value* VL = LHS->Codegen();
  Value* VR = RHS->Codegen();
  
  if (!VL || !VR) {
    std::cerr << "Error: binary expr " << op << " had null subexpr" << std::endl;
    return NULL;
  }

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

//////////////////////////////////////////////////////////

bool PrototypeAST::Sema() {
  std::cout << "PrototypeAST::Sema() -> true" << std::endl;
  return true;
} // TODO

const llvm::FunctionType* PrototypeAST::GetType() {
  // Make the function type
  const IntegerType* returnType = Type::getInt32Ty(getGlobalContext());
  vector<const Type*> argTypes;
  for (int i = 0; i < inArgs.size(); ++i) {
    const Type* ty = inArgs[i]->GetType();
    if (ty == NULL) {
      std::cerr << "Error: fn proto's Type creation failed due to "
        << "null type for arg '" << inArgs[i]->Name << "'" << std::endl;
    }
    argTypes.push_back(ty);
  }
  
  return FunctionType::get(returnType, argTypes, false);
}

Function* PrototypeAST::Codegen() {
  std::cout << "\t" << "Codegen proto "  << Name << std::endl;
  const llvm::FunctionType* FT = this->GetType();
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
    AI->setName(inArgs[i]->Name);
    //NamedValues[inArgs[i]] = AI;
    //std::cout << "Inserting " << inArgs[i] << " in scope" << std::endl;
    scope.insert(inArgs[i]->Name, AI);
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

////////////////////////////////////////////////////////////////////

const llvm::Type* TupleExprAST::GetType() {
  std::vector<const Type*> tupleFieldTypes;
  for (int i = 0; i < body->exprs.size(); ++i) {
    const Type* ty = body->exprs[i]->GetType();
    if (!ty) {
      std::cerr << "Tuple expr had null constituent type for subexpr " << i << std::endl;
    }
    tupleFieldTypes.push_back(ty);
  }
  return llvm::StructType::get(getGlobalContext(), tupleFieldTypes, /*isPacked=*/false);
}

Value* TupleExprAST::Codegen() {
  if (cachedValue != NULL) return cachedValue;
  
  // Create struct type underlying tuple
  const Type* tupleType = this->GetType();
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
}

////////////////////////////////////////////////////////////////////

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

////////////////////////////////////////////////////////////////////

Value* BuiltinCompilesExprAST::Codegen() {
  if (this->status == kWouldCompile) {
    return ConstantInt::getTrue(getGlobalContext());
  } else if (this->status == kWouldNotCompile) {
    return ConstantInt::getFalse(getGlobalContext());
  } else {
    std::cerr << "Error: __COMPILES__ expr not checked!" << std::endl; 
    return NULL;
    //ConstantInt::getFalse(getGlobalContext());
  }
}

////////////////////////////////////////////////////////////////////

