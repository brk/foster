// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"
#include "parse/CompilationContext.h"
#include "parse/ExprASTVisitor.h"

#include "passes/CodegenPass.h"
#include "passes/TypecheckPass.h"

#include "_generated_/FosterConfig.h"

#include "llvm/Attributes.h"
#include "llvm/CallingConv.h"
#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Metadata.h"
#include "llvm/Support/Format.h"

#include "pystring/pystring.h"

#include <map>
#include <set>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::getGlobalContext;
using llvm::Value;
using llvm::ConstantInt;
using llvm::ConstantExpr;
using llvm::APInt;
using llvm::PHINode;
using llvm::dyn_cast;

using foster::LLVMTypeFor;
using foster::module;
using foster::builder;
using foster::currentOuts;
using foster::currentErrs;
using foster::SourceRange;
using foster::EDiag;
using foster::show;

struct CodegenPass : public ExprASTVisitor {
  #include "parse/ExprASTVisitor.decls.inc.h"
};


namespace foster {
  void codegen(ExprAST* ast) {
    CodegenPass cp; ast->accept(&cp);
  }

  void codegen(ExprAST* ast, CodegenPass* cp) {
    ast->accept(cp);
  }
}

const char* llvmValueTag(const llvm::Value* v) {
  using llvm::isa;
  if (isa<llvm::AllocaInst>(v))         return "AllocaInst";
  if (isa<llvm::LoadInst>(v))           return "LoadInst";
  if (isa<llvm::CallInst>(v))           return "CallInst";
  if (isa<llvm::StoreInst>(v))          return "StoreInst";
  if (isa<llvm::BinaryOperator>(v))     return "BinaryOperator";

  if (isa<llvm::Constant>(v))     return "Constant";
  if (isa<llvm::Argument>(v))     return "Argument";
  if (isa<llvm::GlobalValue>(v))  return "GlobalValue";
  if (isa<llvm::CastInst>(v))     return "CastInst";

  if (isa<llvm::GetElementPtrInst>(v))  return "GetElementPtrInst";
  if (isa<llvm::ICmpInst>(v))           return "ICmpInst";
  if (isa<llvm::FCmpInst>(v))           return "FCmpInst";
  if (isa<llvm::SelectInst>(v))         return "SelectInst";
  if (isa<llvm::ExtractElementInst>(v)) return "ExtractElementInst";
  if (isa<llvm::ExtractValueInst>(v))   return "ExtractValueInst";
  if (isa<llvm::SelectInst>(v))         return "SelectInst";
  if (isa<llvm::SwitchInst>(v))         return "SwitchInst";
  if (isa<llvm::InsertElementInst>(v))  return "InsertElementInst";
  if (isa<llvm::InsertValueInst>(v))    return "InsertValueInst";
  if (isa<llvm::PHINode>(v))            return "PHINode";
  if (isa<llvm::ReturnInst>(v))         return "ReturnInst";
  if (isa<llvm::BranchInst>(v))         return "BranchInst";
  if (isa<llvm::IndirectBrInst>(v))     return "IndirectBrInst";
  if (isa<llvm::InvokeInst>(v))         return "InvokeInst";
  if (isa<llvm::UnwindInst>(v))         return "UnwindInst";
  if (isa<llvm::TruncInst>(v))          return "TruncInst";
  if (isa<llvm::BitCastInst>(v))        return "BitCastInst";


  return "Unknown Value";
}

void setValue(ExprAST* ast, llvm::Value* V) {
  foster::dbg("setValue") << "ast@" << ast << " :tag: " << std::string(ast->tag)
        << "\t; value tag: " << llvmValueTag(V) << "\t; value " << *V << "\n";
  ast->value = V;
}

llvm::Value* getValue(ExprAST* ast) {
  if (false && ast->value) {
  foster::dbg("getValue") << "ast@" << ast << " :tag: " << std::string(ast->tag)
      << "\t; value: " << *(ast->value) << "\n";
  }
  return ast->value;
}



// Declarations for Codegen-typemaps.cpp
llvm::GlobalVariable*
emitTypeMap(const Type* ty, std::string name, bool skipOffsetZero = false);

void registerType(const Type* ty, std::string desiredName,
                  bool isClosureEnvironment = false);

llvm::GlobalVariable* getTypeMapForType(const llvm::Type*);

bool mightContainHeapPointers(const llvm::Type* ty);

// Returns type  void (i8**, i8*).
const FunctionType* get_llvm_gcroot_ty() {
  const Type* i8ty = LLVMTypeFor("i8");
  const Type* pi8ty = llvm::PointerType::getUnqual(i8ty);
  const Type* ppi8ty = llvm::PointerType::getUnqual(pi8ty);
  const Type* voidty = llvm::Type::getVoidTy(llvm::getGlobalContext());
  std::vector<const Type*> params;
  params.push_back(ppi8ty);
  params.push_back(pi8ty);
  return llvm::FunctionType::get(voidty, params, /*isvararg=*/ false);
}

llvm::AllocaInst* getAllocaForRoot(llvm::Instruction* root) {
  if (llvm::AllocaInst* ai = llvm::dyn_cast<llvm::AllocaInst>(root)) {
    return ai;
  }

  if (llvm::BitCastInst* bi = llvm::dyn_cast<llvm::BitCastInst>(root)) {
    llvm::Value* op = *(bi->op_begin());
    return llvm::cast<llvm::AllocaInst>(op);
  }

  ASSERT(false) << "root must be alloca or bitcast of alloca!";
  return NULL;
}

// root should be an AllocaInst or a bitcast of such
void markGCRoot(llvm::Value* root, llvm::Constant* meta) {
  llvm::Constant* llvm_gcroot = module->getOrInsertFunction("llvm.gcroot",
                                                          get_llvm_gcroot_ty());
  if (!llvm_gcroot) {
    currentErrs() << "Error! Could not mark GC root!" << "\n";
    exit(1);
  }

  if (!meta) {
    meta = getTypeMapForType(root->getType());
  }

#if 0
  llvm::outs() << "Marking gc root " << *root << " with ";
  if (meta) llvm::outs() << *meta;
  else      llvm::outs() << " null metadata pointer";
  llvm::outs() << "\n";
#endif

  if (!meta) {
    meta = llvm::ConstantPointerNull::get(
                               llvm::PointerType::getUnqual(LLVMTypeFor("i8")));
  } else if (meta->getType() != LLVMTypeFor("i8*")) {
    meta = ConstantExpr::getBitCast(meta, LLVMTypeFor("i8*"));
  }

  llvm::Value* const vmeta = meta;
  llvm::MDNode* metamdnode =
            llvm::MDNode::get(llvm::getGlobalContext(), &vmeta, 1);
  llvm::Instruction* rootinst = llvm::dyn_cast<llvm::Instruction>(root);
  llvm::AllocaInst* allocainst = getAllocaForRoot(rootinst);
  if (!rootinst) {
    llvm::outs() << "root kind is " << llvmValueTag(root) << "\n";
    ASSERT(false) << "need inst!";
  }
  rootinst->setMetadata("fostergcroot", metamdnode);

  builder.CreateCall2(llvm_gcroot, root, meta);
}

// Creates an AllocaInst in the entry block of the current function,
// so that mem2reg will be able to optimize loads and stores from the alloca.
// Code from the Kaleidoscope tutorial on mutable variables,
// http://llvm.org/docs/tutorial/LangImpl7.html
llvm::AllocaInst* CreateEntryAlloca(const llvm::Type* ty, const char* name) {
  llvm::BasicBlock& entryBlock =
      builder.GetInsertBlock()->getParent()->getEntryBlock();
  llvm::IRBuilder<> tmpBuilder(&entryBlock, entryBlock.begin());
  return tmpBuilder.CreateAlloca(ty, /*ArraySize=*/ 0, name);
}

// Unlike markGCRoot, this does not require the root be an AllocaInst
// (though it should still be a pointer).
// This function is intended for marking intermediate values. It stores
// the value into a new stack slot, and marks the stack slot as a root.
llvm::Value* storeAndMarkPointerAsGCRoot(llvm::Value* val) {
  if (!val->getType()->isPointerTy()) {
     llvm::Value* valptr = CreateEntryAlloca(val->getType(), "ptrfromnonptr");
     builder.CreateStore(val, valptr, /*isVolatile=*/ false);
     val = valptr;
  }

  // allocate a slot for a T* on the stack
  llvm::AllocaInst* stackslot = CreateEntryAlloca(val->getType(), "stackref");
  llvm::Value* root = builder.CreateBitCast(stackslot,
                                            LLVMTypeFor("i8**"),
                                            "gcroot");

  markGCRoot(root, getTypeMapForType(val->getType()->getContainedType(0)));
  builder.CreateStore(val, stackslot, /*isVolatile=*/ false);

  // Instead of returning the pointer (of type T*),
  // we return the stack slot (of type T**) so that copying GC will be able to
  // modify the stack slot effectively.
  return stackslot;
}

void markAsNonAllocating(llvm::CallInst* callInst) {
  llvm::Value* tru = llvm::ConstantInt::getTrue(llvm::getGlobalContext());
  llvm::MDNode* mdnode = llvm::MDNode::get(llvm::getGlobalContext(), &tru, 1);
  callInst->setMetadata("willnotgc", mdnode);
}

// Returns ty**, the stack slot containing a ty*.
llvm::Value* emitMalloc(const llvm::Type* ty) {
  llvm::Value* memalloc = gScopeLookupValue("memalloc");
  if (!memalloc) {
    currentErrs() << "NO MEMALLOC IN MODULE! :(" << "\n";
    return NULL;
  }

  // TODO we should statically determine
  // the proper allocation size.
  llvm::CallInst* mem = builder.CreateCall(memalloc,
                                        getConstantInt64For(32),
                                        "mem");
  return storeAndMarkPointerAsGCRoot(
      builder.CreateBitCast(mem, llvm::PointerType::getUnqual(ty), "ptr"));
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

const llvm::Type* getLLVMType(TypeAST* type) {
  if (!type) return NULL;
  return type->getLLVMType();
}

llvm::Value* allocateMPInt() {
  llvm::Value* mp_int_alloc = foster::module->getFunction("mp_int_alloc");
  ASSERT(mp_int_alloc);
  llvm::Value* mpint = builder.CreateCall(mp_int_alloc);
  return mpint;
}

void CodegenPass::visit(IntAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  llvm::Value* small = getConstantInt(ast);

  ASSERT(ast->type && ast->type->getLLVMType());

  if (ast->type->getLLVMType()->isIntegerTy()) {
    setValue(ast, small);
  } else if (false) {
    // MP integer constants that do not fit in 64 bits
    // must be initialized from string data.
    ASSERT(false) << "codegen for int values that don't fit"
                  << " in 64 bits not yet implemented";
  } else {
    // Small integers may be initialized immediately.
    llvm::Value* mpint = allocateMPInt();

    // Call mp_int_init_value() (ignore rv for now)
    llvm::Value* mp_int_init_value = foster::module->getFunction("mp_int_init_value");
    ASSERT(mp_int_init_value);

    builder.CreateCall2(mp_int_init_value, mpint, small);
    setValue(ast, mpint);
  }
}

void CodegenPass::visit(BoolAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);
  setValue(ast, (ast->boolValue)
      ? ConstantInt::getTrue(getGlobalContext())
      : ConstantInt::getFalse(getGlobalContext()));
}

void CodegenPass::visit(VariableAST* ast) {
  // This looks up the lexically closest definition for the given variable
  // name, as provided by a function parameter or some such binding construct.
  // Note that getValue(ast) is NOT used to cache the result; this ensures
  // that closure conversion is free to duplicate AST nodes and still get
  // properly scoped argument values inside converted functions.
  if (ast->lazilyInsertedPrototype) {
    if (!ast->lazilyInsertedPrototype->value) {
      ast->lazilyInsertedPrototype->accept(this);
    }
    setValue(ast, ast->lazilyInsertedPrototype->value);
  } else {
    setValue(ast, gScopeLookupValue(ast->name));
    if (!getValue(ast)) {
      EDiag() << "looking up variable " << ast->name << ", got "
              << str(ast) << show(ast);
      gScope.dump(currentOuts());
    }
  }

  if (!getValue(ast)) {
    EDiag() << "Unknown variable name " << ast->name << " in CodegenPass"
            << show(ast);
    exit(2);
  }
}

void CodegenPass::visit(UnaryOpExprAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  Value* V = ast->parts[0]->value;
  const std::string& op = ast->op;

  if (!V) {
    EDiag() << "unary op " << op << " had null operand" << show(ast);
    return;
  }

       if (op == "-")   { setValue(ast, builder.CreateNeg(V, "negtmp")); }
  else if (op == "not") { setValue(ast, builder.CreateNot(V, "nottmp")); }
  else {
    EDiag() << "unknown unary op '" << op << "' during codegen" << show(ast);
  }
}

llvm::Value* emitPrimitiveLLVMOperation(const std::string& op,
                                        llvm::Value* VL, llvm::Value* VR) {
       if (op == "+") { return builder.CreateAdd(VL, VR, "addtmp"); }
  else if (op == "-") { return builder.CreateSub(VL, VR, "subtmp"); }
  else if (op == "/") { return builder.CreateSDiv(VL, VR, "divtmp"); }
  else if (op == "*") { return builder.CreateMul(VL, VR, "multmp"); }

  else if (op == "<")  { return builder.CreateICmpSLT(VL, VR, "slttmp"); }
  else if (op == "<=") { return builder.CreateICmpSLE(VL, VR, "sletmp"); }
  else if (op == ">")  { return builder.CreateICmpSGT(VL, VR, "sgttmp"); }
  else if (op == ">=") { return builder.CreateICmpSGE(VL, VR, "sgetmp"); }
  else if (op == "==") { return builder.CreateICmpEQ(VL, VR, "eqtmp"); }
  else if (op == "!=") { return builder.CreateICmpNE(VL, VR, "netmp"); }

  else if (op == "bitand") { return builder.CreateAnd(VL, VR, "bitandtmp"); }
  else if (op == "bitor") {  return builder.CreateOr( VL, VR, "bitortmp"); }
  else if (op == "bitxor") { return builder.CreateXor(VL, VR, "bitxortmp"); }

  else if (op == "bitshl") { return builder.CreateShl(VL, VR, "shltmp"); }
  else if (op == "bitlshr") { return builder.CreateLShr(VL, VR, "lshrtmp"); }
  else if (op == "bitashr") { return builder.CreateAShr(VL, VR, "ashrtmp"); }
}

bool isPrimitiveLLVMNumericType(const llvm::Type* ty) {
  return ty->isIntOrIntVectorTy() || ty->isFloatingPointTy();
}

bool isRuntimeArbitraryPrecisionNumericType(const llvm::Type* ty) {
  TypeAST* intType = foster::TypeASTFor("int");
  return intType && ty == intType->getLLVMType();
}

llvm::Value* emitRuntimeMPInt_Op(llvm::Value* VL, llvm::Value* VR,
                                 const char* mp_int_op_name) {
  // TODO If we have ASTs, we would be able to use the _value
  // variants for small constants.

  llvm::Value* result = allocateMPInt();
  builder.CreateCall(foster::module->getFunction("mp_int_init"), result);
  builder.CreateCall3(foster::module->getFunction(mp_int_op_name),
                      VL, VR, result);
  return result;
}

llvm::Value* emitRuntimeArbitraryPrecisionOperation(const std::string& op,
                                        llvm::Value* VL, llvm::Value* VR) {
       if (op == "+") { return emitRuntimeMPInt_Op(VL, VR, "mp_int_add"); }
  //else if (op == "-") { return builder.CreateSub(VL, VR, "subtmp"); }
  //else if (op == "/") { return builder.CreateSDiv(VL, VR, "divtmp"); }
  else if (op == "*") { return emitRuntimeMPInt_Op(VL, VR, "mp_int_mul"); }

  //else if (op == "<")  { return builder.CreateICmpSLT(VL, VR, "slttmp"); }
  //else if (op == "<=") { return builder.CreateICmpSLE(VL, VR, "sletmp"); }
  //else if (op == ">")  { return builder.CreateICmpSGT(VL, VR, "sgttmp"); }
  //else if (op == ">=") { return builder.CreateICmpSGE(VL, VR, "sgetmp"); }
  //else if (op == "==") { return builder.CreateICmpEQ(VL, VR, "eqtmp"); }
  //else if (op == "!=") { return builder.CreateICmpNE(VL, VR, "netmp"); }
  //
  //else if (op == "bitand") { return builder.CreateAnd(VL, VR, "bitandtmp"); }
  //else if (op == "bitor") {  return builder.CreateOr( VL, VR, "bitortmp"); }
  //else if (op == "bitxor") { return builder.CreateXor(VL, VR, "bitxortmp"); }
  //
  //else if (op == "bitshl") { return builder.CreateShl(VL, VR, "shltmp"); }
  //else if (op == "bitlshr") { return builder.CreateLShr(VL, VR, "lshrtmp"); }
  //else if (op == "bitashr") { return builder.CreateAShr(VL, VR, "ashrtmp");

  EDiag() << "\t emitRuntimeArbitraryPrecisionOperation() not yet implemented"
          << " for operation " << op << "!";
  exit(1);
  return NULL;
}

bool leftTypeBiggerInt(const Type* left, const Type* right) {
  return left->getScalarSizeInBits() > right->getScalarSizeInBits();
}

void CodegenPass::visit(BinaryOpExprAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  Value* VL = ast->parts[ast->kLHS]->value;
  Value* VR = ast->parts[ast->kRHS]->value;

  const std::string& op = ast->op;

  if (!VL || !VR) {
    EDiag() << "binary '" << op << "' had null operand " << show(ast);
    return;
  }

  if (VL->getType() != VR->getType() && (isArithOp(op) || isCmpOp(op))) {
    if (leftTypeBiggerInt(VL->getType(), VR->getType())) {
      VR = tempHackExtendInt(VR, VL->getType());
    } else {
      VL = tempHackExtendInt(VL, VR->getType());
    }
  }

  if (isPrimitiveLLVMNumericType(VL->getType())) {
    setValue(ast, emitPrimitiveLLVMOperation(op, VL, VR));
  } else if (isRuntimeArbitraryPrecisionNumericType(VL->getType())) {
    setValue(ast, emitRuntimeArbitraryPrecisionOperation(op, VL, VR));
  }

  if (!getValue(ast)) {
    EDiag() << "Unable to codegen binary operator " << op << " : "
            << str(VL->getType()) << show(ast);
    return;
  }
}

std::string getSymbolName(const std::string& sourceName) {
  // TODO this substitution should probably be explicitly restricted
  // to apply only to top-level function definitions.
  if (sourceName == "main") {
    // libfoster contains a main() symbol that handles
    // initialization and shutdown/cleanup of the runtime,
    // calling this symbol in between.
    return "foster__main";
  }
  return sourceName;
}

void CodegenPass::visit(PrototypeAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  std::string symbolName = getSymbolName(ast->getName());

  if (ast->scope) {
    gScope.pushExistingScope(ast->scope);
  } else {
    gScope.pushScope(ast->getName());
  }

  // Give function literals internal linkage, since we know that
  // they can only be referenced from the function in which they
  // are defined.
  llvm::GlobalValue::LinkageTypes functionLinkage =
      (ast->getName().find("anon_fnlet_") != string::npos)
        ? Function::InternalLinkage
        : Function::ExternalLinkage;

  const llvm::FunctionType* FT = dyn_cast<FunctionType>(getLLVMType(ast->type));
  Function* F = Function::Create(FT, functionLinkage, symbolName, module);

  ASSERT(ast->inArgs.size() == F->arg_size());

  if (!F) {
    EDiag() << "function creation failed" << show(ast);
  } else if (F->getName() != symbolName) {
    // If F conflicted, there was already something with our desired name
    EDiag() << "redefinition of function " << symbolName << show(ast);
  } else {
    // Set names for all arguments
    Function::arg_iterator AI = F->arg_begin();
    for (size_t i = 0; i != ast->inArgs.size(); ++i, ++AI) {
      AI->setName(ast->inArgs[i]->name);
      gScopeInsert(ast->inArgs[i]->name, (AI));
    }
  }

  if (ast->scope) {
    gScope.popExistingScope(ast->scope);
  } else {
    gScope.popScope();
  }

  if (FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(ast->type)) {
    F->setCallingConv(fnty->getCallingConventionID());
  }

  setValue(ast, F);
}

void CodegenPass::visit(SeqAST* ast) {
  //EDiag() << "Codegen for SeqASTs should (eventually) be subsumed by CFG building!";
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  if (!ast->parts.empty()) {
    // Find last non-void value
    for (size_t n = ast->parts.size() - 1; n >= 0; --n) {
      setValue(ast, ast->parts[n]->value);
      if (!isVoid(getValue(ast)->getType())) {
        break;
      }
    }
  }

  if (!getValue(ast)) {
    // Give the sequence a default value for now; eventually, this
    // should probably be assigned a value of unit.
    foster::DDiag() << "warning: empty sequence" << show(ast);
    setValue(ast, llvm::ConstantInt::get(LLVMTypeFor("i32"), 0));
  }
}

void CodegenPass::visit(FnAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  ASSERT(ast->getBody() != NULL);
  ASSERT(ast->getProto()->scope) << "no scope for " << ast->getName();
  ASSERT(ast->getProto()->value) << "ModuleAST should codegen function protos.";

  Function* F = dyn_cast<Function>(ast->getProto()->value);
  if (!F) { return; }

#if USE_FOSTER_GC_PLUGIN
  F->setGC("fostergc");
#else
  F->setGC("shadow-stack");
#endif

  BasicBlock* prevBB = builder.GetInsertBlock();
  BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "entry", F);
  builder.SetInsertPoint(BB);

  gScope.pushExistingScope(ast->getProto()->scope);

  // If the body of the function might allocate memory, the first thing
  // the function should do is create stack slots/GC roots to hold
  // dynamically-allocated pointer parameters.
  if (true) { // conservative approximation to MightAlloc
    Function::arg_iterator AI = F->arg_begin();
    for (size_t i = 0; i != ast->getProto()->inArgs.size(); ++i, ++AI) {
      if (mightContainHeapPointers(AI->getType())) {
#if 0
        std::cout << "marking root for var " << ast->getProto()->inArgs[i]->name
            << " of ast type " << *(ast->getProto()->inArgs[i]->type)
            << " and value type " << *(AI->getType()) << "\n";
#endif
        gScopeInsert(ast->getProto()->inArgs[i]->name,
            storeAndMarkPointerAsGCRoot(AI));
      }
    }
  }

  (ast->getBody())->accept(this);
  Value* RetVal = ast->getBody()->value;
  if (RetVal == NULL) {
    EDiag() << "null body value when codegenning function " << ast->getName()
            << show(ast);
    return;
  }
  ASSERT(RetVal != NULL);

  bool returningVoid = isVoid(ast->getProto()->resultTy);

  // If we try to return a tuple* when the fn specifies a tuple, manually insert a load
  if (RetVal->getType()->isDerivedType()
      && !returningVoid
      && isPointerToType(RetVal->getType(), ast->getProto()->resultTy->getLLVMType())) {
    RetVal = builder.CreateLoad(RetVal, false, "structPtrToStruct");
  }

  gScope.popExistingScope(ast->getProto()->scope);

  if (RetVal) {
    if (returningVoid) {
      builder.CreateRetVoid();
    } else if (isVoid(RetVal->getType())) {
      EDiag() << "unable to return non-void value given only void" << show(ast);
    } else {
      builder.CreateRet(RetVal);
    }
    //llvm::verifyFunction(*F);
    setValue(ast, F);
  } else {
    F->eraseFromParent();
    EDiag() << "function '" << ast->getName()
              << "' retval creation failed" << show(ast);
  }

  // Restore the insertion point, if there was one.
  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }
}

// converts   t1, (envptrty, t2, t3)   to   { rt (envptrty, t2, t3)*, envptrty }
// TODO handle functions of native arity >= 1
const llvm::StructType* closureTypeFromClosedFnType(const FunctionType* fnty) {
  const Type* envPtrTy = fnty->getParamType(0);

  std::vector<const Type*> cloTypes;
  cloTypes.push_back(llvm::PointerType::get(fnty, 0));
  cloTypes.push_back(envPtrTy);
  const llvm::StructType* cloTy = llvm::StructType::get(getGlobalContext(),
                                                        cloTypes,
                                                        /*isPacked=*/ false);
  return cloTy;
}

void CodegenPass::visit(ClosureAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  ASSERT(ast->hasKnownEnvironment) <<
      "closure made it to codegen with no environment type" << show(ast);

  TupleExprAST* env = new TupleExprAST(new SeqAST(ast->parts,
                                          SourceRange::getEmptyRange()),
                                       SourceRange::getEmptyRange());
  ExprAST* fnPtr = new VariableAST(ast->fn->getName(),
                   RefTypeAST::get(ast->fn->type), SourceRange::getEmptyRange());
  typecheck(fnPtr);
  fnPtr->accept(this);

  env->isClosureEnvironment = true;
  typecheck(env);
  env->accept(this);

#if 0
  llvm::errs() << "Closure conversion " << ast->fn->proto->name << "\n\tfnPtr value: "
      << *fnPtr->value << "\n\tFunction? " << llvm::isa<Function>(fnPtr->value) << "\n";
#endif

  FnTypeAST* fnTy = dynamic_cast<FnTypeAST*>(ast->fn->type);
  ASSERT(fnTy != NULL) << "closure fn ref had non-function pointer type?!? "
      << str(ast->fn->type) << show(ast);


  // Manually build struct for now, since we don't have PtrAST nodes
  const llvm::StructType* specificCloTy = closureTypeFromClosedFnType(
      llvm::cast<FunctionType>(fnTy->getLLVMType()));
  TupleTypeAST* genericCloTy = genericVersionOfClosureType(fnTy);

  addClosureTypeName(module, genericCloTy);

  // { code*, env* }*
  llvm::AllocaInst* clo = CreateEntryAlloca(specificCloTy, "closure");

  // TODO the (stack reference to the) closure should be marked as
  // a GC root IFF the environment has been dynamically allocated.

  // (code*)*
  Value* clo_code_slot = builder.CreateConstGEP2_32(clo, 0, 0, "clo_code");
  builder.CreateStore(fnPtr->value, clo_code_slot, /*isVolatile=*/ false);

  // (env*)*
  Value* clo_env_slot = builder.CreateConstGEP2_32(clo, 0, 1, "clo_env");

  if (!ast->parts.empty()) {
    // Store the typemap in the environment's typemap slot.
    const llvm::Type* specificEnvTyPtr = specificCloTy->getContainedType(1);
    const llvm::Type* specificEnvTy = specificEnvTyPtr->getContainedType(0);

    llvm::GlobalVariable* clo_env_typemap
        = getTypeMapForType(specificEnvTy);

    Value* clo_env_typemap_slot = builder.CreateConstGEP2_32(env->value, 0, 0,
                                                      "clo_env_typemap_slot");
    builder.CreateStore(ConstantExpr::getBitCast(
        clo_env_typemap, clo_env_typemap_slot->getType()->getContainedType(0)),
        clo_env_typemap_slot, /*isVolatile=*/ false);

    // Only store the env in the closure if the env contains entries.
    builder.CreateStore(env->value, clo_env_slot, /*isVolatile=*/ false);
  } else {
    // Store null env pointer if environment is empty
    builder.CreateStore(
        llvm::ConstantPointerNull::getNullValue(
                       clo_env_slot->getType()->getContainedType(0)),
        clo_env_slot,
        /* isVolatile= */ false);
  }

  Value* genericClo = builder.CreateBitCast(clo,
      llvm::PointerType::getUnqual(genericCloTy->getLLVMType()), "hideCloTy");
  setValue(ast, builder.CreateLoad(genericClo, /*isVolatile=*/ false, "loadClosure"));
}

void CodegenPass::visit(NamedTypeDeclAST* ast) {
  return;
}

void CodegenPass::visit(ModuleAST* ast) {
  // Ensure that the llvm::Function*s are created for all the function
  // prototypes, so that mutually recursive function references resolve.
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (FnAST* f = dynamic_cast<FnAST*>(ast->parts[i])) {
      f->getProto()->accept(this);
      // Ensure that the value is in the SymbolInfo entry in the symbol table,
      // and not just in the ->value field of the prototype AST node.
      gScopeInsert(f->getName(), f->getProto()->value);
    }
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    ast->parts[i]->accept(this);
  }
}

void CodegenPass::visit(IfExprAST* ast) {
  //EDiag() << "Codegen for IfExprASTs should (eventually) be subsumed by CFG building!";
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  (ast->getTestExpr())->accept(this);
  Value* cond = ast->getTestExpr()->value;
  if (!cond) return;

  Function *F = builder.GetInsertBlock()->getParent();

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then", F);
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);

  Value* then; Value* else_;

  { // Codegen the then-branch of the if expression
    builder.SetInsertPoint(thenBB);
    ast->getThenExpr()->accept(this);
    then = ast->getThenExpr()->value;
    if (!then) {
      EDiag() << "codegen for if expr failed due to missing 'then' branch";
      return;
    }
    builder.CreateBr(mergeBB);
    thenBB = builder.GetInsertBlock();
  }

  { // Codegen the else-branch of the if expression
    F->getBasicBlockList().push_back(elseBB);
    builder.SetInsertPoint(elseBB);
    ast->getElseExpr()->accept(this);
    else_ = ast->getElseExpr()->value;
    if (!else_) {
      EDiag() << "codegen for if expr failed due to missing 'else' branch";
      return;
    }
    builder.CreateBr(mergeBB);
    elseBB = builder.GetInsertBlock();
  }

  { // Codegen the PHI node to merge control flow
    const Type* valTy = getLLVMType(ast->type);
    if (valTy != then->getType() && isPointerToType(then->getType(), valTy)) {
      // If we have a code construct like
      //   if cond then { new blah {} } else { new blah {} }
      // then the ast type (and thus valType) will be blah*
      // but the exprs will be stack slots of type blah**
      valTy = then->getType();
    }

    F->getBasicBlockList().push_back(mergeBB);
    builder.SetInsertPoint(mergeBB);

    PHINode *PN = builder.CreatePHI(valTy, "iftmp");
    PN->addIncoming(then, thenBB);
    PN->addIncoming(else_, elseBB);
    setValue(ast, PN);
  }
}

void CodegenPass::visit(NilExprAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);
  setValue(ast, llvm::ConstantPointerNull::getNullValue(getLLVMType(ast->type)));
}

// The getValue(ast) for a RefExpr of Foster type Tf
// (which is generally a LLVM type Tl*)
// is a T(*)* stack slot holding the actual pointer value.
void CodegenPass::visit(RefExprAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  // Some values will see that they're a child of a RefExpr and substitute
  // a malloc for an alloca; others, like int literals or such, must be
  // manually copied out to a newly-malloc'ed cell.
  setValue(ast, ast->parts[0]->value);
  const llvm::Type* llType = getValue(ast)->getType();

  if (getLLVMType(ast->type) == llType) {
    // e.g. ast type is i32* but value type is i32* instead of i32**
    llvm::Value* stackslot = CreateEntryAlloca(llType, "stackslot");
    builder.CreateStore(getValue(ast), stackslot, /*isVolatile=*/ false);
    setValue(ast, stackslot);
  } else if (isPointerToType(getLLVMType(ast->type), llType)) {
    // If we're given a T when we want a T**, malloc a new T to get a T*
    // stored in a T** on the stack, then copy our T into the T*.

    // stackslot has type T**
    llvm::Value* stackslot = emitMalloc(llType);
    // mem has type T*
    llvm::Value* mem = builder.CreateLoad(stackslot,
                                          /*isVolatile=*/false,
                                          "unstack");
    // write our T into the T* given by malloc
    builder.CreateStore(getValue(ast), mem, /*isVolatile=*/ false);
    setValue(ast, stackslot);
  } else if (isPointerToType(llType, getLLVMType(ast->type))) {
    // Given a T**, and we want a T**. Great!
  } else {
    ASSERT(false) << "unexpected fall-through when codegenning RefExprAST: "
        << "\n\t value Type : " << str(llType)
        << "\n\t ast Type   : " << str(getLLVMType(ast->type))
        << "\n\t ast type   : " << str(ast->type)
        << show(ast);
  }
}

void CodegenPass::visit(DerefExprAST* ast) {
  // Note: unlike the other AST nodes, DerefExprASTs may be codegenned
  // multiple times. The reason is that closure conversion replaces distinct
  // AST nodes with references to a single DerefAST node.

  // TODO is it problematic to cache the Value in the presence of copying
  // collection?

  llvm::Value* src = ast->parts[0]->value;

  if (isPointerToPointerToType(src->getType(), getLLVMType(ast->type))) {
    src = builder.CreateLoad(src, /*isVolatile=*/ false, "prederef");
  }

  ASSERT(isPointerToType(src->getType(), getLLVMType(ast->type)))
      << "deref needs a T* to produce a T, given src type "
      << str(src->getType()) << " and ast type " << str(getLLVMType(ast->type))
      << "\n\t" << ast->tag << " ; " << ast->type->tag;
      //<< show(ast);
  setValue(ast, builder.CreateLoad(src, /*isVolatile=*/ false, "deref"));
}

void CodegenPass::visit(AssignExprAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  const llvm::Type* srcty = ast->parts[1]->value->getType();
  llvm::Value* dst = ast->parts[0]->value;
#if 0
  foster::DDiag(llvm::raw_ostream::BLUE)
    << "assign" << str(srcty) << " to " << str(dst->getType()) << show(ast);
#endif

  // The usual case is set (T*) = T.
  // With implicit dereferencing, we also wish to accept
  //                   set (T*) = (T*)
  ASSERT(isPointerToType(dst->getType(), srcty))
    << "assignment must store T in a T*, given extrapolated dst type "
    << str(ast->parts[0]->value->getType())
    << "\n\tand original dst type" << str(dst->getType())
    << " and srcty " << str(srcty) << "\n\t"
    << "dest HL type: " << str(ast->parts[0]->type);

  builder.CreateStore(ast->parts[1]->value, dst);

  // Mark the assignment as having been codegenned; for now, assignment
  // expressions evaluate to constant zero (annotated for clarity).
  ConstantInt* zero = ConstantInt::get(Type::getInt32Ty(getGlobalContext()), 0);
  setValue(ast, builder.CreateBitCast(zero, zero->getType(), "assignval"));
}

Value* getPointerToIndex(Value* compositeValue,
                         unsigned idxValue,
                         const std::string& name) {
  return builder.CreateConstGEP2_32(compositeValue, 0, idxValue, name.c_str());
}

Value* getPointerToIndex(Value* compositeValue,
                         Value* idxValue,
                         const std::string& name) {
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
    unsigned uidx = unsigned(getSaturating(idxValue));
    return builder.CreateExtractValue(compositeValue, uidx, "subexv");
  } else if (llvm::isa<llvm::VectorType>(compositeType)) {
    if (llvm::isa<llvm::Constant>(idxValue)) {
      return builder.CreateExtractElement(compositeValue, idxValue, "simdexv");
    } else {
      EDiag() << "TODO: codegen for indexing vectors by non-constants"
              << __FILE__ << ":" << __LINE__ << "\n";
    }
  } else {
    llvm::errs() << "Cannot index into value type " << *compositeType
                 << " with non-constant index " << *idxValue << "\n";
  }
  return NULL;
}

void CodegenPass::visit(SubscriptAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  Value* base = ast->parts[0]->value;
  Value* idx  = ast->parts[1]->value;

  ASSERT(base); ASSERT(idx);

  const llvm::Type* baseTy = base->getType();
  if (getLLVMType(ast->type) && isPointerToType(baseTy, getLLVMType(ast->type))
      || (baseTy->isPointerTy()
       && baseTy->getContainedType(0)->isPointerTy())) {
    base = builder.CreateLoad(base, /*isVolatile*/ false, "subload");
  }

  setValue(ast, getElementFromComposite(base, idx));
}

////////////////////////////////////////////////////////////////////

void tempHackExtendIntTypes(const FunctionType* FT, std::vector<Value*>& valArgs) {
  for (size_t i = 0; i < valArgs.size(); ++i) {
    valArgs[i] = tempHackExtendInt(valArgs[i], FT->getParamType(i));
  }

  // TODO better long-term solution is probably make the libfoster
  // function expect_i8 instead of expect_i1, and add a Foster-impl
  // expect_i1 wrapper. And, eventually, implement libfoster in foster ;-)
}

const FunctionType* tryExtractFunctionPointerType(Value* FV) {
  const llvm::PointerType* fp =
                       llvm::dyn_cast_or_null<llvm::PointerType>(FV->getType());
  if (fp == NULL) return NULL;
  return dyn_cast<FunctionType>(fp->getElementType());
}

// Create function    fnName(i8* env, arg-args) { arg(arg-args) }
// that hard-codes call to fn referenced by arg,
// and is suitable for embedding as the code ptr in a closure pair,
// unlike the given function, which doesn't want the env ptr.
FnAST* getClosureVersionOf(ExprAST* arg, FnTypeAST* fnty) {
  static std::map<string, FnAST*> closureVersions;

  string protoName;

  if (VariableAST* var = dynamic_cast<VariableAST*>(arg)) {
    protoName = var->name;
  } else if (PrototypeAST* proto = dynamic_cast<PrototypeAST*>(arg)) {
    protoName = proto->getName();
  }

  if (!protoName.empty()) {
    string fnName = "__closureVersionOf__" + protoName;
    if (FnAST* exists = closureVersions[fnName]) {
      return exists;
    }

    std::vector<VariableAST*> inArgs;
    std::vector<ExprAST*> callArgs;
    inArgs.push_back(new VariableAST(freshName("__ignored_env__"),
        RefTypeAST::get(TypeAST::i(8)),
        SourceRange::getEmptyRange()));

    for (size_t i = 0; i < fnty->getNumParams(); ++i) {
      VariableAST* a = new VariableAST(freshName("_cv_a"),
                             fnty->getParamType(i),
                             SourceRange::getEmptyRange());
      inArgs.push_back(a);
      callArgs.push_back(a);
    }

    // Create a scope for the new proto.
    foster::SymbolTable<foster::SymbolInfo>::LexicalScope* protoScope =
                                    gScope.newScope("fn proto " + fnName);
    // But don't use it for doing codegen outside the proto.
    gScope.popExistingScope(protoScope);

    PrototypeAST* proto = new PrototypeAST(fnty->getReturnType(),
                               fnName, inArgs, arg->sourceRange, protoScope);
    ExprAST* body = new CallAST(arg, callArgs, SourceRange::getEmptyRange());
    FnAST* fn = new FnAST(proto, body, SourceRange::getEmptyRange());

    typecheck(fn);
    // We must manually codegen the proto because functions expect
    // their protos to be codegenned, and we've created this function
    // after the other prototpyes have already been codegenned.
    codegen(fn->getProto());
    codegen(fn);

    // Regular functions get their proto values added when the module
    // starts codegenning, but we need to do it ourselves here.
    gScopeInsert(fn->getName(), fn->getProto()->value);

    closureVersions[fnName] = fn;

    return fn;
  } else {
    EDiag() << "getClosureVersionOf() was given unxpected arg " << str(arg) << show(arg);
    exit(1);
  }
  return NULL;
}

// Follows up to two (type-based) pointer indirections for the given value.
llvm::Value* getClosureStructValue(llvm::Value* maybePtrToClo) {
  if (maybePtrToClo->getType()->isPointerTy()) {
    maybePtrToClo = builder.CreateLoad(maybePtrToClo, /*isVolatile=*/ false, "derefCloPtr");
  }
  if (maybePtrToClo->getType()->isPointerTy()) {
    maybePtrToClo = builder.CreateLoad(maybePtrToClo, /*isVolatile=*/ false, "derefCloPtr");
  }
  return maybePtrToClo;
}

bool
isKnownNonAllocating(ExprAST* ast) {
  if (VariableAST* varast = dynamic_cast<VariableAST*>(ast)) {
    // silly hack for now...
    if (pystring::startswith(varast->getName(), "expect_")) return true;
    if (pystring::startswith(varast->getName(), "print_")) return true;
    return false;
  }
  llvm::outs() << "isKnownNonAllocating: " << str(ast) << "\n";
  return false;
}

void CodegenPass::visit(CallAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  ExprAST* base = ast->parts[0];
  ASSERT(base != NULL);

  base->accept(this);
  Value* FV = base->value;

  const FunctionType* FT = NULL;
  std::vector<Value*> valArgs;

  // TODO extract directly from FnTypeAST
  llvm::CallingConv::ID callingConv = llvm::CallingConv::C;

  if (Function* F = llvm::dyn_cast_or_null<Function>(FV)) {
    // Call to top level function
    FT = F->getFunctionType();
    callingConv = F->getCallingConv();
  } else if (FT = tryExtractFunctionPointerType(FV)) {
    // Call to function pointer
    ASSERT(false) << "don't know what calling convention to use for ptrs";
  } else if (ClosureTypeAST* cty = dynamic_cast<ClosureTypeAST*>(base->type)) {
    // Call to closure struct
    FnTypeAST* fty = tryExtractCallableType(cty->clotype->getContainedType(0));
    ASSERT(fty) << "closure must have function type at codegen time!";

    FT = dyn_cast<const FunctionType>(fty->getLLVMType());
    llvm::Value* clo = getClosureStructValue(FV);

    ASSERT(!clo->getType()->isPointerTy())
        << "clo value should be a tuple, not a pointer";
    llvm::Value* envPtr = builder.CreateExtractValue(clo, 1, "getCloEnv");

    // Pass env pointer as first parameter to function.
    valArgs.push_back(envPtr);

    FV = builder.CreateExtractValue(clo, 0, "getCloCode");
    callingConv = llvm::CallingConv::Fast;
  } else {
    EDiag() << "call to uncallable something" << show(base)
            << "\nFV: " << str(FV);
    return;
  }

  for (size_t i = 1; i < ast->parts.size(); ++i) {
    // Args checked for nulls during typechecking
    ExprAST* arg = ast->parts[i];

    ClosureAST* clo = NULL;

    const llvm::Type* expectedType = FT->getContainedType(i);

    if (clo = dynamic_cast<ClosureAST*>(arg)) {
      // continue...
    } else if (FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(arg->type)) {
      // Codegenning   callee( arg )  where arg has raw function type, not closure type!
      const llvm::FunctionType* llvmFnTy =
            llvm::dyn_cast<const llvm::FunctionType>(fnty->getLLVMType());
      // If we still have a bare function type at codegen time, it means
      // the code specified a (top-level) function name.
      // Since we made it past type checking, we should have only two
      // possibilities for what kind of function is doing the invoking:
      //
      // 1) A C-linkage function which expects a bare function pointer.
      // 2) A Foster function which expects a closure value.
      bool passFunctionPointer = isPointerToCompatibleFnTy(expectedType, llvmFnTy);
      if (passFunctionPointer) {
      // Case 1 is simple; we just change the arg type to "function pointer"
      // instead of "function value" and LLVM takes care of the rest.
      //
      // The only wrinkle is return value compatibility: we'd like to
      // automatically generate a return-value-eating wrapper if we try
      // to pass a function returning a value to a function expecting
      // a procedure returning void.
        if (FnTypeAST* expectedFnTy =
              tryExtractCallableType(TypeAST::reconstruct(
                  llvm::dyn_cast<const llvm::DerivedType>(expectedType)))) {
          if (isVoid(expectedFnTy->getReturnType()) && !isVoid(llvmFnTy)) {
            ASSERT(false) << "No support at the moment for "
                << "auto-generating void-returning wrappers.";
            //arg = getVoidReturningVersionOf(arg, fnty);
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
        ClosureAST* clo = new ClosureAST(getClosureVersionOf(arg, fnty),
                                         SourceRange::getEmptyRange());
        clo->hasKnownEnvironment = true; // Empty by definition!
        arg = clo;
        typecheck(arg);
      }
    }

    arg->accept(this);
    Value* V = arg->value;
    if (!V) {
      EDiag() << "null value for argument " << (i - 1) << " of call"
              << show(arg);
      return;
    }

    // Is the formal parameter a pass-by-value struct and the provided argument
    // a pointer to the same kind of struct? If so, load the struct into a virtual
    // register in order to pass it to the function...
    const Type* formalType = FT->getParamType(valArgs.size());
    if (llvm::isa<llvm::StructType>(formalType)) {
      if (llvm::PointerType::get(formalType, 0) == V->getType()) {
        V = builder.CreateLoad(V, "loadStructParam");
      }
    }

    valArgs.push_back(V);
  }

  // Stack slot loads must be done after codegen for all arguments
  // has taken place, in order to ensure that no allocations will occur
  // between the load and the call.
  for (size_t i = 0; i < valArgs.size(); ++i) {
    llvm::Value*& V = valArgs[i];

    // ContainedType[0] is the return type; args start at 1
    const llvm::Type* expectedType = FT->getContainedType(i + 1);

    // If we're given a T** when we expect a T*,
    // automatically load the reference from the stack.
    if (V->getType() != expectedType
     && expectedType->isPointerTy()
     && isPointerToType(V->getType(), expectedType)) {
      V = builder.CreateLoad(V, /*isVolatile=*/ false, "unstackref");
    }

    bool needsAdjusting = V->getType() != expectedType;
    if (needsAdjusting) {
      ExprAST* arg = ast->parts[i + 1];
      TypeAST* argty = ast->parts[i + 1]->type;

      EDiag() << str(V) << "->getType() is " << str(V->getType())
              << "; expecting " << str(expectedType)
              << "\n\targ is " << str(arg)
              << "\n\targty is " << argty->tag << "\t" << str(argty)
              << show(arg);
    }

    // If we're given a clo** when we expect a clo,
    // automatically load the reference from the stack.
    if (isPointerToPointerToType(V->getType(), expectedType)
     && isGenericClosureType(expectedType)) {
      V = getClosureStructValue(V);
    }

    if (needsAdjusting) {
      currentOuts() << V << "->getType() is " << str(V->getType())
          << "; expect clo? " << isGenericClosureType(expectedType) << "\n";
    }

    // Give print_ref() "polymorphic" behavior by converting a pointer argument
    // of any type to the expected type (i8*, probably).
    if (V->getType() != expectedType
     && V->getType()->isPointerTy() && isPrintRef(base)) {
      while (V->getType()->getContainedType(0)->isPointerTy()) {
        V = builder.CreateLoad(V, false, "strip-all-indirection");
      }
      V = builder.CreateBitCast(V, expectedType, "polyptr");
    }

    if (V->getType() != expectedType) {
      EDiag() << "type mismatch, " << str(V->getType())
              << " vs expected type " << str(expectedType) << show(ast->parts[i + 1]);
    }
  }

  size_t expectedNumArgs = FT->getNumParams();
  if (expectedNumArgs != valArgs.size()) {
    EDiag() << "function arity mismatch, got " << valArgs.size()
            << " args but expected " << expectedNumArgs
            << str(base) << "\n"
            << show(base);
    return;
  }

  // Temporary hack: if a function expects i8 and we have i1, manually convert
  tempHackExtendIntTypes(FT, valArgs);

  llvm::CallInst* callInst = NULL;
  if (isVoid(FT->getReturnType())) {
    callInst = builder.CreateCall(FV, valArgs.begin(), valArgs.end());
  } else {
    callInst = builder.CreateCall(FV, valArgs.begin(), valArgs.end(), "calltmp");
  }

  callInst->setCallingConv(callingConv);

  if (isKnownNonAllocating(base)) {
    markAsNonAllocating(callInst);
  }

  setValue(ast, callInst);

  // If we have e.g. a function like mk-tree(... to ref node)
  // that returns a pointer, we assume that the pointer refers to
  // heap-allocated memory and must be stored on the stack and marked
  // as a GC root. In order that updates from the GC take effect,
  // we use the stack slot (of type T**) instead of the pointer (T*) itself
  // as the return value of the call.
  if (getValue(ast)->getType()->isPointerTy()) {
    const llvm::Type* retty = getValue(ast)->getType();
    if (retty->getContainedType(0)->isPointerTy()) {
      // have T**; load T* value so it can be stored in a gcroot slot
      setValue(ast, builder.CreateLoad(getValue(ast), /*isVolatile=*/ false, "destack"));
    }

    setValue(ast, storeAndMarkPointerAsGCRoot(getValue(ast)));
  }
}

#if 0
bool isComposedOfIntLiterals(ExprAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    IntAST* v = dynamic_cast<IntAST*>(ast->parts[i]);
    if (!v) { return false; }
  }
  return true;
}

llvm::GlobalVariable* getGlobalArrayVariable(SeqAST* body,
                                             const llvm::ArrayType* arrayType) {
  using llvm::GlobalVariable;
  GlobalVariable* gvar = new GlobalVariable(*module,
    /*Type=*/         arrayType,
    /*isConstant=*/   true,
    /*Linkage=*/      llvm::GlobalValue::PrivateLinkage,
    /*Initializer=*/  0, // has initializer, specified below
    /*Name=*/         freshName("arrayGv"));

  // Constant Definitions
  std::vector<llvm::Constant*> arrayElements;

  for (size_t i = 0; i < body->parts.size(); ++i) {
    IntAST* v = dynamic_cast<IntAST*>(body->parts[i]);
    if (!v) {
      EDiag() << "array initializer was not IntAST" << show(body->parts[i]);
      return NULL;
    }

    ConstantInt* ci = dyn_cast<ConstantInt>(getConstantInt(v));
    if (!ci) {
      EDiag() << "array initializer was not a constant" << show(body->parts[i]);
      return NULL;
    }
    arrayElements.push_back(ci);
  }

  llvm::Constant* constArray = llvm::ConstantArray::get(arrayType, arrayElements);
  gvar->setInitializer(constArray);
  return gvar;
}

void CodegenPass::visit(ArrayExprAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  const llvm::ArrayType* arrayType
                            = dyn_cast<llvm::ArrayType>(getLLVMType(ast->type));
  module->addTypeName(freshName("arrayTy"), arrayType);

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (body->parts.empty()) {
    // No initializer
    setValue(ast, CreateEntryAlloca(arrayType, "noInitArr"));

    // We only need to mark arrays of non-atomic objects as GC roots
    // TODO handle rooting arrays of non-atomic objects
    //if (containsPointers(arrayType->getElementType())) {
    //  markGCRoot(getValue(ast), NULL);
    //}

    // TODO add call to memset
  } else {
    // Have initializers; are they constants?
    if (isComposedOfIntLiterals(body)) {
      setValue(ast, getGlobalArrayVariable(body, arrayType));
    } else {
      setValue(ast, CreateEntryAlloca(arrayType, "initArr"));

      // We only need to mark arrays of non-atomic objects as GC roots
          // TODO handle rooting arrays of non-atomic objects
          //if (containsPointers(arrayType->getElementType())) {
          //  markGCRoot(getValue(ast), NULL);
          //}

      for (size_t i = 0; i < body->parts.size(); ++i) {
        builder.CreateStore(body->parts[i]->value,
                            getPointerToIndex(getValue(ast), i, "arrInit"));
      }
    }
  }
}

void CodegenPass::visit(SimdVectorAST* ast) {
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  const llvm::VectorType* simdType
                     = dyn_cast<const llvm::VectorType>(getLLVMType(ast->type));

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
    for (size_t i = 0; i < body->parts.size(); ++i) {
      IntAST* intlit = dynamic_cast<IntAST*>(body->parts[i]);
      llvm::Constant* ci = getConstantInt(intlit);
      elements.push_back(dyn_cast<llvm::Constant>(ci));
    }

    llvm::Constant* constVector = llvm::ConstantVector::get(simdType, elements);
    gvar->setInitializer(constVector);
    setValue(ast, builder.CreateLoad(gvar, /*isVolatile*/ false, "simdLoad"));
  } else {
    llvm::AllocaInst* pt = CreateEntryAlloca(simdType, "s");
    // simd vectors are never gc roots
    for (size_t i = 0; i < body->parts.size(); ++i) {
      Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "simd-gep");
      body->parts[i]->accept(this);
      builder.CreateStore(body->parts[i]->value, dst, /*isVolatile=*/ false);
    }
    setValue(ast, pt);
  }
}
#endif

// pt should be an alloca, either of type tuple* or tuple**,
// where tuple is the type of the TupleExprAST
void copyTupleTo(Value* pt, TupleExprAST* ast) {
  if (isPointerToPointerToType(pt->getType(), getLLVMType(ast->type))) {
    pt = builder.CreateLoad(pt, false, "stackload");
  }

  // pt should now be of type tuple*
  ASSERT(isPointerToType(pt->getType(), getLLVMType(ast->type)));

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  for (size_t i = 0; i < body->parts.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    ExprAST* part = body->parts[i];
    ASSERT(part->value) << "codegen should have been run on the tuple!";

    if (TupleExprAST* tu = dynamic_cast<TupleExprAST*>(part)) {
      copyTupleTo(dst, tu);
    } else {
      if (part->value->getType() == dst->getType()) {
        // Storing a T* in a T* -- need to load to store a T in the T*
        llvm::Value* derefed = builder.CreateLoad(
            part->value, /*isVolatile=*/ false, "derefed");
        builder.CreateStore(derefed, dst, /*isVolatile=*/ false);
      } else if (isPointerToType(dst->getType(), part->value->getType())) {
        builder.CreateStore(part->value, dst, /*isVolatile=*/ false);
      } else {
        EDiag() << "can't store a value of type " << str(part->value->getType())
                << " through a pointer of type " << str(dst->getType())
                << show(part);
      }
    }
  }
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
  ASSERT(!getValue(ast)) << "codegenned twice?!?" << show(ast);

  ASSERT(ast->type != NULL);

  // Create struct type underlying tuple
  const Type* tupleType = getLLVMType(ast->type);
  const char* typeName = (ast->isClosureEnvironment) ? "env" : "tuple";
  registerType(tupleType, typeName, ast->isClosureEnvironment);

  llvm::Value* pt = NULL;

  // Allocate tuple space
  if (dynamic_cast<RefExprAST*>(ast->parent)) {
    // pt has type tuple**
    pt = emitMalloc(tupleType);
  } else {
    // pt has type tuple*
    pt = CreateEntryAlloca(tupleType, "s");
  }

#if 0
  // We only need to mark tuples containing pointers as GC roots
  if (structTypeContainsPointers(dyn_cast<llvm::StructType>(tupleType))) {
    storeAndMarkValueAsGCRoot(pt);
  }
#endif

  copyTupleTo(pt, ast);
  setValue(ast, pt);
}

void CodegenPass::visit(BuiltinCompilesExprAST* ast) {
  if (ast->status == ast->kWouldCompile) {
    setValue(ast, ConstantInt::getTrue(getGlobalContext()));
  } else if (ast->status == ast->kWouldNotCompile) {
    setValue(ast, ConstantInt::getFalse(getGlobalContext()));
  } else {
    EDiag() << "__COMPILES__ expression not checked" << show(ast);
    setValue(ast, ConstantInt::getFalse(getGlobalContext()));
  }
}
