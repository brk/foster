// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "CodegenPass.h"
#include "TypecheckPass.h"
#include "FosterAST.h"
#include "FosterUtils.h"

#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Analysis/Verifier.h"

#include <cassert>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;
using llvm::APInt;
using llvm::PHINode;

llvm::Value* emitMalloc(const llvm::Type* ty);

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

Value* tempHackExtendInt(Value* val, const Type* toTy) {
  const Type* valTy = val->getType();
  // The type checker should ensure that size(expTy) is >= size(argTy)
  if (valTy != toTy && valTy->isInteger() && toTy->isInteger()) {
    return builder.CreateZExt(val, toTy, "zextimplicit");
  } else {
    return val;
  }
}

void CodegenPass::visit(IntAST* ast) {
  if (ast->value) return;
  ast->value = ast->getConstantValue();
}

void CodegenPass::visit(BoolAST* ast) {
  if (ast->value) return;
 ast->value = (ast->boolValue)
      ? ConstantInt::getTrue(getGlobalContext())
      : ConstantInt::getFalse(getGlobalContext());
}

void CodegenPass::visit(VariableAST* ast) {
  if (ast->value) return;

  // This looks up the lexically closest definition for the given variable
  // name, as provided by a function parameter or some such binding construct.
  if (ast->lazilyInsertedPrototype) {
    ast->lazilyInsertedPrototype->accept(this);
    ast->value = ast->lazilyInsertedPrototype->value;
  } else {
    ast->value = scope.lookup(ast->name, "");
  }

  if (!ast->value) {
    std::cerr << "Error: Unknown variable name " << ast->name << std::endl;
  }
}

void CodegenPass::visit(UnaryOpExprAST* ast) {
  if (ast->value) return;

  Value* V = ast->parts[0]->value;
  const std::string& op = ast->op;

  if (!V) {
    std::cerr << "Error: unary expr " << op << " had null operand" << std::endl;
    return;
  }

       if (op == "-")   { ast->value = builder.CreateNeg(V, "negtmp"); }
  else if (op == "not") { ast->value = builder.CreateNot(V, "nottmp"); }
  else {
    std::cerr << "Error: unknown unary op '" << op << "' encountered during codegen" << std::endl;
  }
}

bool isArithOp(string op) { return op == "+" || op == "-" || op == "/" || op == "*"; }
bool isCmpOp(string op) { return op == "<" || op == "==" || op == "!="; }
bool leftTypeBiggerInt(const Type* left, const Type* right) {
  return left->getScalarSizeInBits() > right->getScalarSizeInBits();
}

void CodegenPass::visit(BinaryOpExprAST* ast) {
  if (ast->value) return;

  Value* VL = ast->parts[ast->kLHS]->value;
  Value* VR = ast->parts[ast->kRHS]->value;

  const std::string& op = ast->op;
  
  if (!VL || !VR) {
    std::cerr << "Error: binary expr " << op << " had null subexpr" << std::endl;
    return;
  }

  if (VL->getType() != VR->getType() && (isArithOp(op) || isCmpOp(op))) {
    if (leftTypeBiggerInt(VL->getType(), VR->getType())) {
      VR = tempHackExtendInt(VR, VL->getType());
    } else {
      VL = tempHackExtendInt(VL, VR->getType());
    }
  }

       if (op == "+") { ast->value = builder.CreateAdd(VL, VR, "addtmp"); }
  else if (op == "-") { ast->value = builder.CreateSub(VL, VR, "subtmp"); }
  else if (op == "/") { ast->value = builder.CreateSDiv(VL, VR, "divtmp"); }
  else if (op == "*") { ast->value = builder.CreateMul(VL, VR, "multmp"); }
  
  else if (op == "<") { ast->value = builder.CreateICmpSLT(VL, VR, "slttmp"); }
  else if (op == "<=") { ast->value = builder.CreateICmpSLE(VL, VR, "sletmp"); }
  else if (op == "==") { ast->value = builder.CreateICmpEQ(VL, VR, "eqtmp"); }
  else if (op == "!=") { ast->value = builder.CreateICmpNE(VL, VR, "netmp"); }
  
  else if (op == "bitand") { ast->value = builder.CreateAnd(VL, VR, "bitandtmp"); }
  else if (op == "bitor") {  ast->value = builder.CreateOr( VL, VR, "bitortmp"); }
  else if (op == "bitxor") { ast->value = builder.CreateXor(VL, VR, "bitxortmp"); }

  else if (op == "bitshl") { ast->value = builder.CreateShl(VL, VR, "shltmp"); }
  else if (op == "bitlshr") { ast->value = builder.CreateLShr(VL, VR, "lshrtmp"); }
  else if (op == "bitashr") { ast->value = builder.CreateAShr(VL, VR, "ashrtmp"); }
  else {
    std::cerr << "Couldn't gen code for op " << op << endl;
  }
}

void CodegenPass::visit(PrototypeAST* ast) {
  if (ast->value) return;

  //std::cout << "\t" << "Codegen proto "  << ast->name << std::endl;
  const llvm::FunctionType* FT = llvm::dyn_cast<FunctionType>(ast->type);
  Function* F = Function::Create(FT, Function::ExternalLinkage, ast->name, module);

  if (!F) {
    std::cout << "Function creation failed!" << std::endl;
    return;
  }

  // If F conflicted, there was already something named "Name"
  if (F->getName() != ast->name) {
    std::cout << "Error: redefinition of function " << ast->name << std::endl;
    return;
  }

  // Set names for all arguments
  Function::arg_iterator AI = F->arg_begin();
  for (int i = 0; i != ast->inArgs.size(); ++i, ++AI) {
    AI->setName(ast->inArgs[i]->name);
    scope.insert(ast->inArgs[i]->name, AI);
#if 0
    std::cout << "Fn param " << ast->inArgs[i]->name << " ; " 
              << ast->inArgs[i] << " has val " << ast->inArgs[i]->value 
              << ", associated with " << AI << std::endl;
#endif
  }

  //std::cout << "\tdone codegen proto " << ast->name << std::endl;
  ast->value = F;

  scope.insert(ast->name, F);
}

void CodegenPass::visit(SeqAST* ast) {
  if (ast->value) return;

  if (ast->parts.empty()) {
    // Give the sequence a default value for now; eventually, this
    // should probably be assigned a value of unit.
    ast->value = llvm::ConstantInt::get(LLVMTypeFor("i32"), 0);
  } else {
    ast->value = ast->parts.back()->value;
  }
}

void CodegenPass::visit(FnAST* ast) {
  if (ast->value) return;

  assert(ast->body != NULL);

  (ast->proto)->accept(this);
  Function* F = llvm::dyn_cast<Function>(ast->proto->value);
  if (!F) { return; }

  scope.pushScope("fn " + ast->proto->name);

  this->insertPointStack.push(builder.GetInsertBlock());

  BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "entry", F);
  builder.SetInsertPoint(BB);

  (ast->body)->accept(this);
  Value* RetVal = ast->body->value;
  if (RetVal == NULL) std::cerr << "Oops, null body value in fn " << ast->proto->name << std::endl;
  assert (RetVal != NULL);
  
  // If we try to return a tuple* when the fn specifies a tuple, manually insert a load
  if (RetVal->getType()->isDerivedType()
      && RetVal->getType() == llvm::PointerType::get(ast->proto->resultTy, 0)) {
    RetVal = builder.CreateLoad(RetVal, false, "structPtrToStruct");
  }

  scope.popScope();

  if (RetVal) {
    builder.CreateRet(RetVal);
    //llvm::verifyFunction(*F);
    ast->value = F;
  } else {
    F->eraseFromParent();
    std::cout << "Function '" << ast->proto->name << "' retval creation failed" << std::endl;
  }

  // Restore the insertion point from the previous function, if there was one.
  BasicBlock* prevBlock = this->insertPointStack.top(); this->insertPointStack.pop();
  if (prevBlock) {
    builder.SetInsertPoint(prevBlock);
  }
}

void CodegenPass::visit(ClosureTypeAST* ast) {
  std::cerr << "CodegenPass ClosureTypeAST: " << *ast << std::endl;
}

// converts   t1, (envptrty, t2, t3)   to   { rt (envptrty, t2, t3)*, envptrty }
// TODO handle functions of native arity >= 1
const Type* closureTypeFromClosedFnType(const FunctionType* fnty) {
  const Type* envPtrTy = fnty->getParamType(0);

  std::vector<const Type*> cloTypes;
  cloTypes.push_back(llvm::PointerType::get(fnty, 0));
  cloTypes.push_back(envPtrTy);
  const llvm::StructType* cloTy = llvm::StructType::get(getGlobalContext(), cloTypes, /*isPacked=*/ false);

  std::cout << "Specific closure, fn ty: " << *fnty << std::endl;
  std::cout << "Specific closure, env ty: " << *envPtrTy << std::endl;
  std::cout << "Specific closure, cloty: " << *cloTy << std::endl;
  return cloTy;
}

void CodegenPass::visit(ClosureAST* ast) {
  if (ast->value) return;

  if (!ast->hasKnownEnvironment) {
    std::cerr << "Error! Closure made it past closure conversion without getting an environment type!" << std::endl;  
  }
  
  for (int i = 0; i < ast->parts.size(); ++i) {
    std::cout << "Codegen ClosureAST, part: " << *ast->parts[i] << std::endl;
    std::cout << "Codegen ClosureAST, part: " << *ast->parts[i]->type << std::endl;
    std::cout << std::endl;
  }
  
  
  ExprAST* env = new TupleExprAST(new SeqAST(ast->parts));
  ExprAST* fnPtr = new VariableAST(ast->fn->proto->name, llvm::PointerType::get(ast->fn->type, 0));
  { TypecheckPass tp;
    env->accept(&tp);
    env->accept(this);

    fnPtr->accept(&tp);
    fnPtr->accept(this);
  }

  if (const FunctionType* fnTy = llvm::dyn_cast<const FunctionType>(ast->fn->type)) {
    // Manually build struct for now, since we don't have PtrAST nodes
    const Type* specificCloTy = closureTypeFromClosedFnType(fnTy);
    const llvm::StructType* cloTy = genericVersionOfClosureType(fnTy);

    std::cout << std::endl;
    std::cout << "Fn type: " << *fnTy << std::endl;
    std::cout << "Specific closure type: " << *specificCloTy << std::endl;
    std::cout << "Generic closure type: " << *cloTy << std::endl;

    addClosureTypeName(module, cloTy);

    llvm::AllocaInst* clo = builder.CreateAlloca(cloTy, 0, "closure");

    Value* clo_code = builder.CreateConstGEP2_32(clo, 0, 0, "clo_code");
    Value* bc_fnptr = builder.CreateBitCast(fnPtr->value, cloTy->getContainedType(0), "hideclofnty");
    builder.CreateStore(bc_fnptr, clo_code, /*isVolatile=*/ false);

    Value* clo_env = builder.CreateConstGEP2_32(clo, 0, 1, "clo_env");
    Value* bc_envptr = builder.CreateBitCast(env->value, cloTy->getContainedType(1), "hidecloenvty");
    builder.CreateStore(bc_envptr, clo_env, /*isVolatile=*/ false);

    ast->value = builder.CreateLoad(clo, /*isVolatile=*/ false, "loadClosure");
  }

  if (!ast->value) {
    std::cerr << "Closure fn ref had non-function pointer type?!? " << *(ast->fn->type) << std::endl;
  }
}

struct LazyValue { virtual Value* get() const = 0; };
struct LazyVisitedValue : public LazyValue {
  FosterASTVisitor* visitor; ExprAST* expr;
  LazyVisitedValue(FosterASTVisitor* v, ExprAST* e) : visitor(v), expr(e) {}
  Value* get() const { expr->accept(visitor); return expr->value; }
};
struct MemoValue : public LazyValue {
  Value* v; MemoValue(Value* v) : v(v) {}; Value* get() const { return v; }; };

PHINode* codegenIfExpr(Value* cond, const LazyValue& lazyThen, const LazyValue& lazyElse, const Type* valTy) {
  Function *F = builder.GetInsertBlock()->getParent();

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then", F);
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);
  builder.SetInsertPoint(thenBB);
  Value* then = lazyThen.get();
  if (!then) {
    std::cerr << "Codegen for if condition failed due to missing Value for 'then' part";
  }
  builder.CreateBr(mergeBB);
  thenBB = builder.GetInsertBlock();

  F->getBasicBlockList().push_back(elseBB);
  builder.SetInsertPoint(elseBB);
  Value* else_ = lazyElse.get();
  if (!else_) {
    std::cerr << "Codegen for if condition failed due to missing Value for 'else' part";
  }
  builder.CreateBr(mergeBB);
  elseBB = builder.GetInsertBlock();

  F->getBasicBlockList().push_back(mergeBB);
  builder.SetInsertPoint(mergeBB);
  
  PHINode *PN = builder.CreatePHI(valTy, "iftmp");
  PN->addIncoming(then, thenBB);
  PN->addIncoming(else_, elseBB);
  return PN;
}

void CodegenPass::visit(IfExprAST* ast) {
  if (ast->value) return;

  (ast->testExpr)->accept(this);
  Value* cond = ast->testExpr->value;
  if (!cond) return;

  ast->value = codegenIfExpr(cond, LazyVisitedValue(this, ast->thenExpr),
                                   LazyVisitedValue(this, ast->elseExpr), ast->type);
}

void CodegenPass::visit(RefExprAST* ast) {
  if (ast->value) return;

  // Some values will see that they're a child of a RefExpr and substitute
  // a malloc for an alloca; others, like int literals or such, must be
  // manually copied out to a newly-malloc'ed cell.
  ast->value = ast->parts[0]->value;

  // If we're given a T when we want a T*, malloc a new value and copy.
  if (llvm::PointerType::getUnqual(ast->value->getType()) == ast->type) {

    std::cout << "RefExpr allocating/copying new value of type "
        << *(ast->value->getType()) << "\n";

    llvm::Value* mem = emitMalloc(ast->value->getType());
    builder.CreateStore(ast->value, mem, /*isVolatile=*/ false);

    ast->value = mem;
  }
}

void CodegenPass::visit(DerefExprAST* ast) {
  if (ast->value) return;

  ast->value = builder.CreateLoad(ast->parts[0]->value, /*isVolatile=*/ false, "deref");
}

void CodegenPass::visit(AssignExprAST* ast) {
  if (ast->value) return;

  builder.CreateStore(ast->parts[1]->value, ast->parts[0]->value);

  // Mark the assignment as having been codegenned; for now, assignment expressions
  // evaluate to constant zero (annotated for clarity).
  ConstantInt* zero = ConstantInt::get(Type::getInt32Ty(getGlobalContext()), 0);
  ast->value = builder.CreateBitCast(zero, zero->getType(), "assignval");
}

Value* getPointerToIndex(Value* compositeValue, unsigned idxValue, const std::string& name) {
  return builder.CreateConstGEP2_32(compositeValue, 0, idxValue, name.c_str());
}

Value* getPointerToIndex(Value* compositeValue, Value* idxValue, const std::string& name) {
  std::vector<Value*> idx;
  idx.push_back(ConstantInt::get(Type::getInt32Ty(getGlobalContext()), 0));
  idx.push_back(idxValue);
  return builder.CreateGEP(compositeValue, idx.begin(), idx.end(), name.c_str());
}

Value* getElementFromComposite(Value* compositeValue, Value* idxValue) {
  const Type* compositeType = compositeValue->getType();
  if (llvm::isa<llvm::PointerType>(compositeType)) {
    // Pointers to composites are indexed via getelementptr
    // TODO: "When indexing into a (optionally packed) structure,
    //        only i32 integer constants are allowed. When indexing
    //        into an array, pointer or vector, integers of any width
    //        are allowed, and they are not required to be constant."
    //   -- http://llvm.org/docs/LangRef.html#i_getelementptr
    Value* gep = getPointerToIndex(compositeValue, idxValue, "subgep");
    return builder.CreateLoad(gep, "subgep_ld");
  } else if (llvm::isa<llvm::StructType>(compositeType)
          && llvm::isa<llvm::Constant>(idxValue)) {
    // Struct values may be indexed only by constant expressions
    unsigned uidx = getSaturating<unsigned>(idxValue);
    return builder.CreateExtractValue(compositeValue, uidx, "subexv");
  } else if (llvm::isa<llvm::VectorType>(compositeType)) {
    if (llvm::isa<llvm::Constant>(idxValue)) {
      return builder.CreateExtractElement(compositeValue, idxValue, "simdexv");
    } else {
      std::cerr << "TODO: codegen for indexing vectors by non-constants " << __FILE__ << ":" << __LINE__ << std::endl;
      // TODO
    }
  } else {
    std::cerr << "Cannot index into value type " << *compositeType << " with non-constant index " << *idxValue << std::endl;
    return NULL;
  }
}

void CodegenPass::visit(SubscriptAST* ast) {
  if (ast->value) return;

  Value* base = ast->parts[0]->value;
  Value* idx  = ast->parts[1]->value;

  if (this->inAssignLHS) {
    ast->value = getPointerToIndex(base, idx, "assignLHS");
  } else {
    ast->value = getElementFromComposite(base, idx);
  }
}

////////////////////////////////////////////////////////////////////

void appendArg(std::vector<Value*>& valArgs, Value* V, const FunctionType* FT) {
  //std::cout << "actual arg " << valArgs.size() << " = " << *V << " has type " << *(V->getType()) << std::endl;
  //std::cout << "formal arg " << valArgs.size() << " has type " << *(FT->getParamType(valArgs.size())) << std::endl;
  
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
    unpackArgs(valArgs, getElementFromComposite(V, ConstantInt::get(Type::getInt32Ty(getGlobalContext()), j)), FT);
  }
}

void tempHackExtendIntTypes(const FunctionType* FT, std::vector<Value*>& valArgs) {
  for (int i = 0; i < valArgs.size(); ++i) {
    valArgs[i] = tempHackExtendInt(valArgs[i], FT->getParamType(i));
  }
  
  // TODO better long-term solution is probably make the libfoster
  // function expect_i8 instead of expect_i1, and add a Foster-impl
  // expect_i1 wrapper. And, eventually, implement libfoster in foster ;-)
}

const FunctionType* tryExtractFunctionPointerType(Value* FV) {
  const llvm::PointerType* fp = llvm::dyn_cast_or_null<llvm::PointerType>(FV->getType());
  if (fp == NULL) return NULL;
  return llvm::dyn_cast<FunctionType>(fp->getElementType());
}

void CodegenPass::visit(CallAST* ast) {
  if (ast->value) return;

  ExprAST* base = ast->parts[0];
  assert (base != NULL);

  //std::cout << "\t" << "Codegen CallAST "  << (base) << std::endl;
  //std::cout << "\t\t\tbase ast: "  << *(base) << std::endl;

  // TODO if base has closure type, it should be a ClosureAST node

  base->accept(this);
  Value* FV = base->value;

  const FunctionType* FT = NULL;
  std::vector<Value*> valArgs;

  if (Function* F = llvm::dyn_cast_or_null<Function>(FV)) {
    // Call to top level function
    FT = F->getFunctionType();
  } else if (FT = tryExtractFunctionPointerType(FV)) {
    // Call to function pointer
  } else if (const llvm::StructType* sty = llvm::dyn_cast<const llvm::StructType>(base->type)) {
    if (const llvm::FunctionType* fty = tryExtractCallableType(sty->getContainedType(0))) {
      // Call to closure struct
      FT = fty;
      llvm::Value* clo = FV;
      llvm::Value* envPtr = builder.CreateExtractValue(clo, 1, "getCloEnv");

      // Pass env pointer as first parameter to function.
      valArgs.push_back(envPtr);

      FV = builder.CreateExtractValue(clo, 0, "getCloCode");
    }
  } else {
    // Call to something we don't know how to call!
    std::cerr << "base: " << *base << "; FV: " << *FV << std::endl;
    std::cerr << "Unknown function referenced!" << std::endl;
    if (FV != NULL) { std::cerr << "\tFV: "  << *(FV) << std::endl; }

    return;
  }
  
  for (int i = 1; i < ast->parts.size(); ++i) {
    // Args checked for nulls during typechecking
    ExprAST* arg = ast->parts[i];
    
    UnpackExprAST* u = dynamic_cast<UnpackExprAST*>(arg);
    if (u != NULL) { // arg i is an unpack expr
      arg = u->parts[0]; // Replace unpack expr with underlying tuple expr
    }
    
    arg->accept(this);
    Value* V = arg->value;
    if (!V) {
      std::cerr << "Error: null value for argument " << (i - 1) << " found in CallAST codegen!" << std::endl;
      return;
    }
    
    // LLVM will automatically convert a Function Value to a Pointer-to-Function,
    // so we only have to handle non-trivial closure creation.
    //std::cout << "codegen CallAST arg " << (i-1) << "; argty " << *(arg->type)
    //          << " vs fn arg ty " << *(FT->getContainedType(i)) << std::endl;

    if (u != NULL) {
      unpackArgs(valArgs, V, FT); // Unpack (recursively) nested structs
    } else {
      appendArg(valArgs, V, FT); // Don't unpack non 'unpack'-marked structs
    }
  }

  if (false) {
    std::cout << "Creating call for AST {" << valArgs.size() << "} " << *base << std::endl;
    for (int i = 0; i < valArgs.size(); ++i) {
      std::cout << "\t" << *valArgs[i] << std::endl;
    }
  }
  
  int expectedNumArgs = FT->getNumParams();
  if (expectedNumArgs != valArgs.size()) {
    std::cerr << "Function " << *base <<  " got " << valArgs.size() << " args, expected "<< expectedNumArgs << std::endl;
    return;
  }
  
  // Temporary hack: if a function expects i8 and we have i1, manually convert
  tempHackExtendIntTypes(FT, valArgs);
  
  ast->value = builder.CreateCall(FV, valArgs.begin(), valArgs.end(), "calltmp");
}

bool isComposedOfIntLiterals(ExprAST* ast) {
  for (int i = 0; i < ast->parts.size(); ++i) {
    IntAST* v = dynamic_cast<IntAST*>(ast->parts[i]);
    if (!v) { return false; }
  }
  return true;
}

llvm::GlobalVariable* getGlobalArrayVariable(SeqAST* body, const llvm::ArrayType* arrayType) {
  using llvm::GlobalVariable;
  GlobalVariable* gvar = new GlobalVariable(*module,
    /*Type=*/         arrayType,
    /*isConstant=*/   true,
    /*Linkage=*/      llvm::GlobalValue::PrivateLinkage,
    /*Initializer=*/  0, // has initializer, specified below
    /*Name=*/         freshName("arrayGv"));

  // Constant Definitions
  std::vector<llvm::Constant*> arrayElements;

  for (int i = 0; i < body->parts.size(); ++i) {
    IntAST* v = dynamic_cast<IntAST*>(body->parts[i]);
    if (!v) {
      std::cerr << "Array initializer was not IntAST but instead " << *v << std::endl;
      return NULL;
    }
    
    ConstantInt* ci = llvm::dyn_cast<ConstantInt>(v->getConstantValue());
    if (!ci) {
      std::cerr << "Failed to cast array initializer value to ConstantInt" << std::endl;
      return NULL;
    }
    arrayElements.push_back(ci);
  }
  
  llvm::Constant* constArray = llvm::ConstantArray::get(arrayType, arrayElements);
  gvar->setInitializer(constArray);
  return gvar;
}

void CodegenPass::visit(ArrayExprAST* ast) {
  if (ast->value) return;

  const llvm::ArrayType* arrayType = llvm::dyn_cast<llvm::ArrayType>(ast->type);
  module->addTypeName(freshName("arrayTy"), arrayType);

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (body->parts.empty()) {
    // No initializer
    ast->value = builder.CreateAlloca(arrayType, 0, "noInitArr");
    // TODO add call to memset
  } else {
    // Have initializers; are they constants?
    if (isComposedOfIntLiterals(body)) {
      ast->value = getGlobalArrayVariable(body, arrayType);
    } else {
      ast->value = builder.CreateAlloca(arrayType, 0, "initArr");
      for (int i = 0; i < body->parts.size(); ++i) {
        builder.CreateStore(body->parts[i]->value, getPointerToIndex(ast->value, i, "arrInit"));
      }
    }
  }
}

void CodegenPass::visit(SimdVectorAST* ast) {
  if (ast->value) return;
  
  const llvm::VectorType* simdType = llvm::dyn_cast<const llvm::VectorType>(ast->type);
  
  
  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  bool isConstant = isComposedOfIntLiterals(body);
  
  using llvm::GlobalVariable;
  GlobalVariable* gvar = new GlobalVariable(*module,
    /*Type=*/         simdType,
    /*isConstant=*/   isConstant,
    /*Linkage=*/      llvm::GlobalValue::PrivateLinkage,
    /*Initializer=*/  0, // has initializer, specified below
    /*Name=*/         freshName("simdGv"));

  if (isConstant) {
    std::vector<llvm::Constant*> elements;
    for (int i = 0; i < body->parts.size(); ++i) {
      IntAST* intlit = dynamic_cast<IntAST*>(body->parts[i]);
      llvm::Constant* ci = intlit->getConstantValue();
      elements.push_back(llvm::dyn_cast<llvm::Constant>(ci));
    }
    
    llvm::Constant* constVector = llvm::ConstantVector::get(simdType, elements);
    gvar->setInitializer(constVector);
    ast->value = builder.CreateLoad(gvar, /*isVolatile*/ false, "simdLoad");
  } else {
    llvm::AllocaInst* pt = builder.CreateAlloca(simdType, 0, "s");
    for (int i = 0; i < body->parts.size(); ++i) {
      Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "simd-gep");
      body->parts[i]->accept(this);
      builder.CreateStore(body->parts[i]->value, dst, /*isVolatile=*/ false);
    }
    ast->value = pt;
  }
}

void copyTupleTo(CodegenPass* pass, Value* pt, TupleExprAST* ast) {
  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  for (int i = 0; i < body->parts.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    ExprAST* part = body->parts[i];
    part->accept(pass);

    if (TupleExprAST* tu = dynamic_cast<TupleExprAST*>(part)) {
      copyTupleTo(pass, dst, tu);
    } else {
      builder.CreateStore(part->value, dst, /*isVolatile=*/ false);
    }
  }
}

llvm::Value* emitMalloc(const llvm::Type* ty) {
  llvm::Value* memalloc = scope.lookup("memalloc", "");
  if (!memalloc) {
    std::cerr << "NO MEMALLOC IN MODULE! :(" << std::endl;
    return NULL;
  }
  llvm::Value* mem = builder.CreateCall(memalloc, 
    llvm::ConstantInt::get(getGlobalContext(), llvm::APInt(64, llvm::StringRef("32"), 10)), "mem");
  return builder.CreateBitCast(mem, llvm::PointerType::getUnqual(ty), "memcast");
}

void CodegenPass::visit(TupleExprAST* ast) {
  if (ast->value) return;
  
  std::cout << "CodegenPass visiting TupleExprAST " << ast << std::endl;

  assert(ast->type != NULL);

  // Create struct type underlying tuple
  const Type* tupleType = ast->type;

  module->addTypeName(freshName("tuple"), tupleType);

  // Allocate tuple space
  llvm::AllocaInst* pt = builder.CreateAlloca(tupleType, 0, "s");
  //llvm::Value* pt = emitMalloc(tupleType);
  

  copyTupleTo(this, pt, ast);
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
