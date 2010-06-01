// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "CodegenPass.h"
#include "TypecheckPass.h"
#include "FosterAST.h"
#include "FosterUtils.h"

#include "llvm/Attributes.h"
#include "llvm/CallingConv.h"
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

// returns type  void (i8**, i8*)
const FunctionType* get_llvm_gcroot_ty() {
  const Type* i8ty = LLVMTypeFor("i8");
  const Type* pi8ty = llvm::PointerType::getUnqual(i8ty);
  const Type* ppi8ty = llvm::PointerType::getUnqual(pi8ty);
  const Type* voidty = llvm::Type::getVoidTy(llvm::getGlobalContext());
  std::vector<const Type*> params;
  params.push_back(pi8ty);
  return llvm::FunctionType::get(voidty, params, /*isvararg=*/ false);
}

void markGCRoot(llvm::Value* root, llvm::Value* meta) {
  std::cout << "Marking gc root!" << std::endl;
  llvm::Constant* llvm_gcroot = module->getOrInsertFunction("llvm.gcroot", get_llvm_gcroot_ty());
  if (!llvm_gcroot) {
    std::cerr << "Error! Could not mark GC root!" << std::endl;
    exit(1);
  }

  if (!meta) {
    meta = llvm::ConstantPointerNull::get(llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(getGlobalContext())));
  }

  builder.CreateCall2(llvm_gcroot, root, meta);
}

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
    llvm::errs() << "numericOf() got a non-constant-int value " << *v << ", returning " << allOnes << "\n";
    return allOnes;
  }
}

Value* tempHackExtendInt(Value* val, const Type* toTy) {
  const Type* valTy = val->getType();
  // The type checker should ensure that size(expTy) is >= size(argTy)
  if (valTy != toTy && valTy->isIntegerTy() && toTy->isIntegerTy()) {
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
    std::cerr << "Error: CodegenPass: Unknown variable name " << ast->name << std::endl;
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

  if (!ast->parts.empty()) {
    // Find last non-void value
    for (int n = ast->parts.size() - 1; n >= 0; --n) {
      ast->value = ast->parts[n]->value;
      if (!isVoid(ast->value->getType())) {
        break;
      }
    }
  }

  if (!ast->value) {
    // Give the sequence a default value for now; eventually, this
    // should probably be assigned a value of unit.
    ast->value = llvm::ConstantInt::get(LLVMTypeFor("i32"), 0);
  }
}

void CodegenPass::visit(FnAST* ast) {
  if (ast->value) return;

  assert(ast->body != NULL);

  (ast->proto)->accept(this);
  Function* F = llvm::dyn_cast<Function>(ast->proto->value);
  if (!F) { return; }

  F->setGC("shadow-stack");
  scope.pushScope("fn " + ast->proto->name);

  this->insertPointStack.push(builder.GetInsertBlock());

  BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "entry", F);
  builder.SetInsertPoint(BB);

  (ast->body)->accept(this);
  Value* RetVal = ast->body->value;
  if (RetVal == NULL) std::cerr << "Oops, null body value in fn " << ast->proto->name << std::endl;
  assert (RetVal != NULL);

  bool returningVoid = isVoid(ast->proto->resultTy);

  // If we try to return a tuple* when the fn specifies a tuple, manually insert a load
  if (RetVal->getType()->isDerivedType()
      && !returningVoid
      && RetVal->getType() == llvm::PointerType::get(ast->proto->resultTy, 0)) {
    RetVal = builder.CreateLoad(RetVal, false, "structPtrToStruct");
  }

  scope.popScope();

  if (RetVal) {
    if (returningVoid) {
      builder.CreateRetVoid();
    } else if (isVoid(RetVal->getType())) {
      std::cerr << "Error! Can't return non-void value given only a void value!\n";
    } else {
      builder.CreateRet(RetVal);
    }
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
    fnPtr->accept(&tp);
    fnPtr->accept(this);

    env->accept(&tp);
    env->accept(this);
  }

  if (ast->isTrampolineVersion) {
    if (Function* func = llvm::dyn_cast<Function>(fnPtr->value)) {
      func->addAttribute(1, llvm::Attribute::Nest);
    }
  }

  llvm::errs() << "Closure conversion " << ast->fn->proto->name << "\n\tfnPtr value: "
      << *fnPtr->value << "\n\tFunction? " << llvm::isa<Function>(fnPtr->value) << "\n";

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
    markGCRoot(clo, NULL);

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

void CodegenPass::visit(ForRangeExprAST* ast) {
  if (ast->value) return;

  (ast->startExpr)->accept(this);
  if (!ast->startExpr->value) { return; }

  Function* parentFn = builder.GetInsertBlock()->getParent();
  BasicBlock* preLoopBB  = builder.GetInsertBlock();
  BasicBlock* loopBB     = BasicBlock::Create(llvm::getGlobalContext(), "forTo", parentFn);

  builder.CreateBr(loopBB);
  builder.SetInsertPoint(loopBB);

  llvm::PHINode* pickvar = builder.CreatePHI(LLVMTypeFor("i32"), ast->varName);
  pickvar->addIncoming(ast->startExpr->value, preLoopBB);

  scope.pushScope("for-range " + ast->varName);
  scope.insert(ast->varName, pickvar);

  (ast->bodyExpr)->accept(this);
  if (!ast->bodyExpr->value) { return; }
  scope.popScope();

  Value* one  = ConstantInt::get(LLVMTypeFor("i32"), 1);
  Value* next = builder.CreateAdd(pickvar, one, "next");

  (ast->endExpr)->accept(this);
  if (!ast->endExpr->value) { return; }
  Value* end = ast->endExpr->value;
  Value* endCond = builder.CreateICmpNE(next, end, "loopcond");

  BasicBlock* loopEndBB = builder.GetInsertBlock();
  BasicBlock* afterBB   = BasicBlock::Create(getGlobalContext(), "postloop", parentFn);
  builder.CreateCondBr(endCond, loopEndBB, afterBB);
  builder.SetInsertPoint(afterBB);

  pickvar->addIncoming(next, loopEndBB);

  ast->value = ConstantInt::get(LLVMTypeFor("i32"), 0);
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
    llvm::errs() << "Cannot index into value type " << *compositeType << " with non-constant index " << *idxValue << "\n";
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

FnAST* getVoidReturningVersionOf(ExprAST* arg, const llvm::FunctionType* fnty) {
  static std::map<string, FnAST*> voidReturningVersions;
  if (VariableAST* var = dynamic_cast<VariableAST*>(arg)) {
    string fnName = "__voidReturningVersionOf__" + var->name;
    if (FnAST* exists = voidReturningVersions[fnName]) {
      return exists;
    }

    // Create function  void fnName(arg-args) { arg(arg-args) }
    std::vector<VariableAST*> inArgs;
    std::vector<ExprAST*> callArgs;

    for (int i = 0; i < fnty->getNumParams(); ++i) {
      std::stringstream ss; ss << "a" << i;
      VariableAST* a = new VariableAST(ss.str(), fnty->getParamType(i));
      inArgs.push_back(a);
      callArgs.push_back(a);
    }
    PrototypeAST* proto = new PrototypeAST(fnty->getVoidTy(getGlobalContext()), fnName, inArgs);
    ExprAST* body = new CallAST(arg, callArgs);
    FnAST* fn = new FnAST(proto, body);
    { TypecheckPass tp; CodegenPass cp; fn->accept(&tp); fn->accept(&cp); }
    voidReturningVersions[fnName] = fn;
    return fn;
  } else {
    std::cerr << "Error! getVoidReturningVersionOf() expected a variable naming a fn!\n";
    std::cerr << "\tInstead, got: " << *arg << std::endl;
    exit(1);
  }
  return NULL;
}

Function* getLLVMInitTrampoline() {
  // This isn't added along with the other intrinsics because
  // it's not supposed to be directly callable from foster code.

  const llvm::Type* pi8 = llvm::PointerType::getUnqual(LLVMTypeFor("i8"));

  std::vector<const Type*> llvm_init_trampoline_fnty_args;
  llvm_init_trampoline_fnty_args.push_back(pi8);
  llvm_init_trampoline_fnty_args.push_back(pi8);
  llvm_init_trampoline_fnty_args.push_back(pi8);
  FunctionType* llvm_init_trampoline_fnty = FunctionType::get(
      pi8, llvm_init_trampoline_fnty_args, /*isVarArg=*/false);

  Function* llvm_init_trampoline = Function::Create(
      /*Type=*/    llvm_init_trampoline_fnty,
      /*Linkage=*/ llvm::GlobalValue::ExternalLinkage,
      /*Name=*/    "llvm.init.trampoline", module); // (external, no body)
  llvm_init_trampoline->setCallingConv(llvm::CallingConv::C);
  return llvm_init_trampoline;
}

llvm::Value* getTrampolineForClosure(ClosureAST* cloAST) {
  static Function* llvm_init_trampoline = getLLVMInitTrampoline();

  const llvm::Type* i8 = LLVMTypeFor("i8");
  const llvm::Type* pi8 = llvm::PointerType::getUnqual(i8);

  // We have a closure { code*, env* } and must convert it to a bare
  // trampoline function pointer.
  const llvm::Type* trampolineArrayType = llvm::ArrayType::get(i8, 24); // Sufficient for x86 and x86_64
  llvm::AllocaInst* trampolineBuf = builder.CreateAlloca(trampolineArrayType, 0, "trampBuf");

  trampolineBuf->setAlignment(16); // sufficient for x86 and x86_64
  Value* trampi8 = builder.CreateBitCast(trampolineBuf, pi8, "trampi8");

  markGCRoot(trampi8, NULL);

  // It would be nice and easy to extract the code pointer from the closure,
  // but LLVM requires that pointers passed to trampolines be "obvious" function
  // pointers. Thus, we need direct access to the closure's underlying fn.
  ExprAST* fnPtr = new VariableAST(cloAST->fn->proto->name, llvm::PointerType::get(cloAST->fn->type, 0));
  { TypecheckPass tp; CodegenPass cp;
    fnPtr->accept(&tp);
    fnPtr->accept(&cp);
  }
  Value* codePtr = fnPtr->value;
  Value* envPtr = builder.CreateExtractValue(cloAST->value, 1, "getEnvPtr");

  Value* tramp = builder.CreateCall3(llvm_init_trampoline,
                      trampi8,
                      builder.CreateBitCast(codePtr, pi8),
                      builder.CreateBitCast(envPtr,  pi8), "tramp");
  return tramp;
}

FnAST* getClosureVersionOf(ExprAST* arg, const llvm::FunctionType* fnty) {
  static std::map<string, FnAST*> closureVersions;
  if (VariableAST* var = dynamic_cast<VariableAST*>(arg)) {
    string fnName = "__closureVersionOf__" + var->name;
    if (FnAST* exists = closureVersions[fnName]) {
      return exists;
    }

    // Create function    fnName(i8* env, arg-args) { arg(arg-args) }
    // that hard-codes call to fn referenced by arg

    std::vector<VariableAST*> inArgs;
    std::vector<ExprAST*> callArgs;
    inArgs.push_back(new VariableAST("__ignored_env__", llvm::PointerType::getUnqual(LLVMTypeFor("i8"))));

    for (int i = 0; i < fnty->getNumParams(); ++i) {
      std::stringstream ss; ss << "a" << i;
      VariableAST* a = new VariableAST(ss.str(), fnty->getParamType(i));
      inArgs.push_back(a);
      callArgs.push_back(a);
    }
    PrototypeAST* proto = new PrototypeAST(fnty->getReturnType(), fnName, inArgs);
    ExprAST* body = new CallAST(arg, callArgs);
    FnAST* fn = new FnAST(proto, body);
    { TypecheckPass tp; CodegenPass cp; fn->accept(&tp); fn->accept(&cp); }
    closureVersions[fnName] = fn;
    return fn;
  } else {
    std::cerr << "Error! getClosureVersionOf() expected a variable naming a fn!\n";
    std::cerr << "\tInstead, got: " << *arg << std::endl;
    exit(1);
  }
  return NULL;
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
    std::cerr << "base: " << *base;
    llvm::errs() << "; FV: " << *FV << "\n";
    std::cerr << "Unknown function referenced!" << std::endl;
    if (FV != NULL) { llvm::errs() << "\tFV: "  << *(FV) << "\n"; }

    return;
  }

  for (int i = 1; i < ast->parts.size(); ++i) {
    // Args checked for nulls during typechecking
    ExprAST* arg = ast->parts[i];

    UnpackExprAST* u = dynamic_cast<UnpackExprAST*>(arg);
    if (u != NULL) { // arg i is an unpack expr
      arg = u->parts[0]; // Replace unpack expr with underlying tuple expr
    }

    ClosureAST* clo = NULL;

    const llvm::Type* expectedType = FT->getContainedType(i);

    // Codegenning   callee( arg )  where arg has raw function type, not closure type!
    if (const FunctionType* fnty = llvm::dyn_cast<const FunctionType>(arg->type)) {
      // If we still have a bare function type at codegen time, it means
      // the code specified a (top-level) function name.
      // Since we made it past type checking, we should have only two
      // possibilities for what kind of function is doing the invoking:
      //
      // 1) A C-linkage function which expects a bare function pointer.
      // 2) A Foster function which expects a closure value.
      bool passFunctionPointer = isPointerToCompatibleFnTy(expectedType, fnty);

      std::cout << "Passing function to " << (passFunctionPointer ? "fn ptr" : "closure") << "\n";

      if (passFunctionPointer) {
      // Case 1 is simple; we just change the arg type to "function pointer"
      // instead of "function value" and LLVM takes care of the rest.
      //
      // The only wrinkle is return value compatibility: we'd like to
      // automatically generate a return-value-eating wrapper if we try
      // to pass a function returning a value to a function expecting
      // a procedure returning void.
        if (const FunctionType* expectedFnTy = tryExtractCallableType(expectedType)) {
          if (isVoid(expectedFnTy->getReturnType()) && !isVoid(fnty)) {
            arg = getVoidReturningVersionOf(arg, fnty);
            { TypecheckPass tp; arg->accept(&tp); }
          }
        }
      } else {
      // Case 2 is not so simple, since a closure code pointer must take the
      // environment pointer as its first argument, and presumably the fn
      // we want to invoke does not take an env pointer. Thus we need a pointer
      // to a forwarding function, which acts as the opposite of a trampoline:
      // instead of excising one (implicitly-added) parameter from a function
      // signature, we add one (implicitly-ignored) parameter to the signature.
      //
      // The simplest approach is to lazily generate a "closure version" of any
      // functions we see being passed directly by name; it would forward
      // all parameters to the regular function, except for the env ptr.
        ClosureAST* clo = new ClosureAST(getClosureVersionOf(arg, fnty));
        clo->hasKnownEnvironment = true; // Empty by definition!
        arg = clo;
        { TypecheckPass tp; arg->accept(&tp); }
      //
      // One slightly more clever approach could use a trampoline to reduce
      // code bloat. Instead of one "closure version" per function, we'd
      // generate one "generic closure forwarder" per function type
      // signature. The forwarder for a function G of type R (X, Y) would be
      // of type R (R (X, Y)* nest, i8* env, X, Y). The body of the forwarder
      // would simply call the nest function pointer with the provided params.
      // The trampoline would embed the pointer to G, yielding a callable
      // function of the desired type, R (i8* env, X, Y).
      // This would have the additional benefit of working with anonymous
      // function pointer values e.g. from a lookup table.
      }

      std::cout << "codegen CallAST arg " << (i-1) << "; argty " << *(arg->type)
                << " vs fn arg ty " << *(FT->getContainedType(i)) << std::endl;
    } else {
      clo = dynamic_cast<ClosureAST*>(arg);
    }

    arg->accept(this);
    Value* V = arg->value;
    if (!V) {
      std::cerr << "Error: null value for argument " << (i - 1) << " found in CallAST codegen!" << std::endl;
      return;
    }

    if (clo && clo->isTrampolineVersion) {
      std::cout << "Creating trampoline for closure; bitcasting to " << *expectedType << std::endl;
      V = builder.CreateBitCast(getTrampolineForClosure(clo), expectedType, "trampfn");
    }

    if (u != NULL) {
      unpackArgs(valArgs, V, FT); // Unpack (recursively) nested structs
    } else {
      appendArg(valArgs, V, FT); // Don't unpack non 'unpack'-marked structs
    }
  }

  if (true) {
    std::cout << "Creating call for AST {" << valArgs.size() << "} " << *base << std::endl;
    for (int i = 0; i < valArgs.size(); ++i) {
      llvm::errs() << "\tAST arg " << i << ":\t" << *valArgs[i] << "\n";
    }
  }

  int expectedNumArgs = FT->getNumParams();
  if (expectedNumArgs != valArgs.size()) {
    std::cerr << "Function " << *base <<  " got " << valArgs.size() << " args, expected "<< expectedNumArgs << std::endl;
    return;
  }

  // Temporary hack: if a function expects i8 and we have i1, manually convert
  tempHackExtendIntTypes(FT, valArgs);

  std::cout << *FT <<  " ; " << isVoid(FT->getReturnType()) << std::endl;

  if (isVoid(FT->getReturnType())) {
    ast->value = builder.CreateCall(FV, valArgs.begin(), valArgs.end());
  } else {
    ast->value = builder.CreateCall(FV, valArgs.begin(), valArgs.end(), "calltmp");
  }
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

    // We only need to mark arrays of pointers as GC roots
    if (arrayType->getElementType()->isPointerTy()) {
      markGCRoot(ast->value, NULL);
    }

    // TODO add call to memset
  } else {
    // Have initializers; are they constants?
    if (isComposedOfIntLiterals(body)) {
      ast->value = getGlobalArrayVariable(body, arrayType);
    } else {
      ast->value = builder.CreateAlloca(arrayType, 0, "initArr");

      // We only need to mark arrays of pointers as GC roots
      if (arrayType->getElementType()->isPointerTy()) {
        markGCRoot(ast->value, NULL);
      }

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
    // simd vectors are never gc roots
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

// returns ty*, with a ty** on the stack
llvm::Value* emitMalloc(const llvm::Type* ty) {
  llvm::Value* memalloc = scope.lookup("memalloc", "");
  if (!memalloc) {
    std::cerr << "NO MEMALLOC IN MODULE! :(" << std::endl;
    return NULL;
  }
  llvm::Value* mem = builder.CreateCall(memalloc,
    llvm::ConstantInt::get(getGlobalContext(), llvm::APInt(64, llvm::StringRef("32"), 10)), "mem");

  llvm::Value* pointer = builder.CreateBitCast(mem, llvm::PointerType::getUnqual(ty), "memcast");;

  llvm::AllocaInst* stackref = builder.CreateAlloca(llvm::PointerType::getUnqual(ty), 0, "stackref");
  builder.CreateStore(pointer, stackref, /*isVolatile*/ false);
  markGCRoot(stackref, NULL);

  return pointer;
}

bool structTypeContainsPointers(const llvm::StructType* ty) {
  for (unsigned i = 0; i < ty->getNumElements(); ++i) {
    if (ty->getTypeAtIndex(i)->isPointerTy()) {
      return true;
    }
  }
  return false;
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

  // We only need to mark tuples containing pointers as GC roots
  if (structTypeContainsPointers(llvm::dyn_cast<llvm::StructType>(tupleType))) {
    markGCRoot(pt, NULL);
  }

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
