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
#include "llvm/Target/TargetData.h"

#include <cassert>
#include <sstream>
#include <map>
#include <set>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;
using llvm::APInt;
using llvm::PHINode;

typedef std::pair<const llvm::Type*, int> OffsetInfo;
typedef std::set<OffsetInfo> OffsetSet;

// TODO replace with ConstantExpr::getOffsetOf(ty, slot) ?
int getOffsetOfStructSlot(const llvm::StructType* ty, int slot) {
  const llvm::TargetData* td = ee->getTargetData();
  int offset = 0;
  for (int i = 0; i < slot; ++i) {
	offset += td->getTypeStoreSize(ty->getContainedType(i));
  }
  return offset;
}

OffsetSet countPointersInType(const llvm::Type* ty) {
  assert(ty != NULL && "Can't count pointers in a NULL type!");

  OffsetSet rv;
  if (ty->isPointerTy()) {
	rv.insert(OffsetInfo(ty->getContainedType(0), 0));
  }

  // array, struct, union
  else if (const llvm::ArrayType* aty = llvm::dyn_cast<const llvm::ArrayType>(ty)) {
	// TODO need to decide how Foster semantics will map to LLVM IR for arrays.
	// Will EVERY (C++), SOME (Factor, C#?), or NO (Java) types be unboxed in arrays?
	// Also need to figure out how the gc will collect arrays.
    //return aty->getNumElements() * countPointersInType(aty->getElementType());
  }

  // if we have a struct { T1; T2 } then our offset set will be the set for T1,
  // plus the set for T2 with offsets incremented by the size of T1.
  else if (const llvm::StructType* sty = llvm::dyn_cast<const llvm::StructType>(ty)) {
    for (int i = 0; i < sty->getNumElements(); ++i) {
      int slotOffset = getOffsetOfStructSlot(sty, i);
      OffsetSet sub = countPointersInType(sty->getTypeAtIndex(i));
      for (OffsetSet::iterator si = sub.begin(); si != sub.end(); ++si) {
    	const llvm::Type* subty = si->first;
    	int suboffset = si->second;
    	rv.insert(OffsetInfo(subty, suboffset + slotOffset));
      }
    }
  }

  // TODO Also need to decide how to represent type maps for unions
  // in such a way that the GC can safely collect unions.
  else if (const llvm::UnionType* uty = llvm::dyn_cast<const llvm::UnionType>(ty)) {
    //return 0;
  }

  // all other types do not contain pointers
  return rv;
}

llvm::ConstantInt* getConstantInt64For(int64_t val) {
  std::stringstream ss; ss << val;
  return llvm::ConstantInt::get(getGlobalContext(), llvm::APInt(64, ss.str(), 10));
}

llvm::ConstantInt* getConstantInt32For(int val) {
  std::stringstream ss; ss << val;
  return llvm::ConstantInt::get(getGlobalContext(), llvm::APInt(32, ss.str(), 10));
}

std::map<const llvm::Type*, llvm::GlobalVariable*> typeMapForType;

llvm::Constant* getTypeMapEntryFor(
		const llvm::StructType* typeMapEntryTy,
		const llvm::Type* entryTy, int v2) {
  std::vector<llvm::Constant*> fields;

  llvm::GlobalVariable* typeMapVar = typeMapForType[entryTy];
  if (typeMapVar) {
	fields.push_back(llvm::ConstantExpr::getCast(llvm::Instruction::BitCast,
			typeMapVar, LLVMTypeFor("i8*")));
  } else {
	// If we can't tell the garbage collector how to collect a type by
	// giving it a pointer to a type map, it's probably because the type
	// doesn't have a type map, i.e. the type is atomic. Instead, tell
	// the garbage collector how large the type is.
	fields.push_back(llvm::ConstantExpr::getCast(llvm::Instruction::IntToPtr,
	  		llvm::ConstantExpr::getSizeOf(entryTy), LLVMTypeFor("i8*")));
  }
  fields.push_back(getConstantInt32For(v2));
  return llvm::ConstantStruct::get(typeMapEntryTy, fields);
}

llvm::Constant* arrayVariableToPointer(llvm::GlobalVariable* arr) {
  std::vector<llvm::Constant*> idx;
  idx.push_back(getConstantInt64For(0));
  idx.push_back(getConstantInt64For(0));
  return llvm::ConstantExpr::getGetElementPtr(arr, &idx[0], idx.size());
}

// return a global corresponding to the following layout:
// struct {
//   const char* typeName;
//   i32 numPtrEntries;
//   struct { i8* typeinfo; i32 offset }[numPtrEntries];
// }
llvm::GlobalVariable* emitTypeMap(const llvm::Type* ty, std::string name) {
  using llvm::StructType;

  OffsetSet pointerOffsets = countPointersInType(ty);
  int numPointers = pointerOffsets.size();

  // Construct the type map's LLVM type
  std::vector<const Type*> entryty_types;
  entryty_types.push_back(LLVMTypeFor("i8*"));
  entryty_types.push_back(LLVMTypeFor("i32"));
  StructType* entryty = StructType::get(getGlobalContext(), entryty_types, /*isPacked=*/false);
  module->addTypeName("typemap_entry", entryty);

  std::vector<const Type*> typeMapTyFields;
  llvm::ArrayType* entriesty = llvm::ArrayType::get(entryty, numPointers);

  typeMapTyFields.push_back(LLVMTypeFor("i8*"));
  typeMapTyFields.push_back(LLVMTypeFor("i32"));
  typeMapTyFields.push_back(entriesty);

  const StructType* typeMapTy = StructType::get(getGlobalContext(), typeMapTyFields);

  llvm::GlobalVariable* typeMapVar = new llvm::GlobalVariable(
    /*Module=*/     *module,
    /*Type=*/       typeMapTy,
    /*isConstant=*/ false,
    /*Linkage=*/    llvm::GlobalValue::ExternalLinkage,
    /*Initializer=*/ 0,
    /*Name=*/        "__foster_typemap_" + name,
    /*ThreadLocal=*/ false);
  typeMapVar->setAlignment(16);

  // Register the (as-yet uninitialized) variable to avoid problems
  // with recursive types.
  typeMapForType[ty] = typeMapVar;

  // Construct the type map itself
  std::stringstream ss; ss << name << " = " << *ty;
  std::vector<llvm::Constant*> typeMapFields;
  llvm::Constant* cname = llvm::ConstantArray::get(getGlobalContext(), ss.str().c_str(), true);
  llvm::GlobalVariable* typeNameVar = new llvm::GlobalVariable(
      /*Module=*/      *module,
      /*Type=*/        cname->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     llvm::GlobalValue::PrivateLinkage,
      /*Initializer=*/ cname,
      /*Name=*/        ".typename." + name);
  typeNameVar->setAlignment(1);

  llvm::Constant* cnameptr = arrayVariableToPointer(typeNameVar);
  typeMapFields.push_back(cnameptr);
  //typeMapFields.push_back(llvm::ConstantPointerNull::getNullValue(LLVMTypeFor("i8*")));
  typeMapFields.push_back(getConstantInt32For(numPointers));

  std::vector<llvm::Constant*> typeMapEntries;
  for (OffsetSet::iterator si =  pointerOffsets.begin();
		                   si != pointerOffsets.end(); ++si) {
	const llvm::Type* subty = si->first;
	int suboffset = si->second;
	typeMapEntries.push_back(
	  getTypeMapEntryFor(entryty, subty, suboffset));
  }


  typeMapFields.push_back(llvm::ConstantArray::get(entriesty, typeMapEntries));

  llvm::Constant* typeMap = llvm::ConstantStruct::get(typeMapTy, typeMapFields);

  typeMapVar->setInitializer(typeMap);
  return typeMapVar;
}

void registerType(const llvm::Type* ty, std::string desiredName) {
  static std::map<const llvm::Type*, bool> registeredTypes;

  if (registeredTypes[ty]) return;

  registeredTypes[ty] = true;

  std::string name = freshName(desiredName);
  module->addTypeName(name, ty);
  emitTypeMap(ty, name);
}

// returns type  void (i8**, i8*)
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

// root should be an AllocaInst or a bitcast of such
void markGCRoot(llvm::Value* root, llvm::Constant* meta) {
  std::cout << "Marking gc root!" << std::endl;
  llvm::Constant* llvm_gcroot = module->getOrInsertFunction("llvm.gcroot", get_llvm_gcroot_ty());
  if (!llvm_gcroot) {
    std::cerr << "Error! Could not mark GC root!" << std::endl;
    exit(1);
  }

  if (!meta) {
    meta = typeMapForType[root->getType()];
  }

  if (!meta) {
    meta = llvm::ConstantPointerNull::get(llvm::PointerType::getUnqual(llvm::Type::getInt8Ty(getGlobalContext())));
  } else if (meta->getType() != LLVMTypeFor("i8*")) {
    meta = llvm::ConstantExpr::getBitCast(meta, LLVMTypeFor("i8*"));
  }

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
  assert(val->getType()->isPointerTy());

  llvm::AllocaInst* stackslot = CreateEntryAlloca(val->getType(), "stackref");
  llvm::Value* root = builder.CreateBitCast(stackslot, LLVMTypeFor("i8**"), "gcroot");

  markGCRoot(root, typeMapForType[val->getType()->getContainedType(0)]);
  builder.CreateStore(val, stackslot, /*isVolatile=*/ false);

  // Instead of returning the pointer (of type T*),
  // we return the stack slot (of type T**) so that copying GC will be able to
  // modify the stack slot effectively.
  return stackslot;
}

// returns ty**, the stack slot containing a ty*
llvm::Value* emitMalloc(const llvm::Type* ty) {
  llvm::Value* memalloc = scope.lookup("memalloc", "");
  if (!memalloc) {
    std::cerr << "NO MEMALLOC IN MODULE! :(" << std::endl;
    return NULL;
  }
  llvm::Value* mem = builder.CreateCall(memalloc, getConstantInt64For(32), "mem");
  return storeAndMarkPointerAsGCRoot(
      builder.CreateBitCast(mem, llvm::PointerType::getUnqual(ty), "ptr"));
}

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

#if 0
  if (isPointerToType(ast->value->getType(), ast->type) &&
      !ast->type->isFunctionTy()) {
    std::cout << "\tfound indirect variable of type "
        << *(ast->type) << ": " << ast->name << std::endl;
  }
#endif

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

  std::string sourceName = ast->name;
  std::string symbolName = sourceName;

  // TODO this substitution should probably be explicitly restricted
  // to apply only to top-level function definitions.
  if (symbolName == "main") {
    // libfoster contains a main() symbol that handles
    // initialization and shutdown/cleanup of the runtime,
    // calling this symbol in between.
    symbolName = "foster__main";
  }

  //std::cout << "\t" << "Codegen proto "  << sourceName << std::endl;
  const llvm::FunctionType* FT = llvm::dyn_cast<FunctionType>(ast->type);
  Function* F = Function::Create(FT, Function::ExternalLinkage, symbolName, module);

  if (!F) {
    std::cout << "Function creation failed!" << std::endl;
    return;
  }

  // If F conflicted, there was already something with our desired name 
  if (F->getName() != symbolName) {
    std::cout << "Error: redefinition of function " << symbolName << std::endl;
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

  //std::cout << "\tdone codegen proto " << sourceName << std::endl;
  ast->value = F;

  scope.insert(sourceName, F);
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

  // If the body of the function might allocate memory, the first thing
  // the function should do is create stack slots/GC roots to hold
  // dynamically-allocated pointer parameters.
  if (true) { // conservative approximation to MightAlloc
    Function::arg_iterator AI = F->arg_begin();
    for (int i = 0; i != ast->proto->inArgs.size(); ++i, ++AI) {
      if (AI->getType()->isPointerTy()) {
        scope.insert(ast->proto->inArgs[i]->name,
            storeAndMarkPointerAsGCRoot(AI));
      }
    }
  }

  (ast->body)->accept(this);
  Value* RetVal = ast->body->value;
  if (RetVal == NULL) std::cerr << "Oops, null body value in fn " << ast->proto->name << std::endl;
  assert (RetVal != NULL);

  bool returningVoid = isVoid(ast->proto->resultTy);

  // If we try to return a tuple* when the fn specifies a tuple, manually insert a load
  if (RetVal->getType()->isDerivedType()
      && !returningVoid
      && isPointerToType(RetVal->getType(), ast->proto->resultTy)) {
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

    llvm::AllocaInst* clo = CreateEntryAlloca(cloTy, "closure");
    std::cout << "clo has type " << *(clo->getType()) << std::endl;

    // TODO the (stack reference to the) closure should only be marked as
    // a GC root if the environment has been dynamically allocated...
    //markGCRoot(clo, NULL);

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

PHINode* codegenIfExpr(Value* cond,
    const LazyValue& lazyThen,
    const LazyValue& lazyElse,
    const Type* valTy) {
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

  // If we have a code construct like
  //   if cond then { new blah {} } else { new blah {} }
  // then the ast type (and thus valType) will be blah*
  // but the exprs will be stack slots of type blah**
  if (valTy != then->getType() && isPointerToType(then->getType(), valTy)) {
    valTy = then->getType();
  }

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

  Value* incr;
  if (ast->incrExpr) {
	(ast->incrExpr)->accept(this);
	if (!ast->incrExpr->value) { return; }
	incr = ast->incrExpr->value;
  } else {
	incr = ConstantInt::get(LLVMTypeFor("i32"), 1);
  }

  (ast->startExpr)->accept(this);
  if (!ast->startExpr->value) { return; }

  Function* parentFn = builder.GetInsertBlock()->getParent();
  BasicBlock* preLoopBB  = builder.GetInsertBlock();
  BasicBlock* loopBB     = BasicBlock::Create(llvm::getGlobalContext(), "forTo", parentFn);

  builder.CreateBr(loopBB);
  builder.SetInsertPoint(loopBB);

  llvm::PHINode* pickvar = builder.CreatePHI(ast->var->type, ast->var->name);
  pickvar->addIncoming(ast->startExpr->value, preLoopBB);

  scope.pushScope("for-range " + ast->var->name);
  scope.insert(ast->var->name, pickvar);

  (ast->bodyExpr)->accept(this);
  if (!ast->bodyExpr->value) { return; }
  scope.popScope();

  Value* next = builder.CreateAdd(pickvar, incr, "next");

  (ast->endExpr)->accept(this);
  if (!ast->endExpr->value) { return; }
  Value* end = ast->endExpr->value;
  Value* endCond = builder.CreateICmpSLT(next, end, "loopcond");

  BasicBlock* loopEndBB = builder.GetInsertBlock();
  BasicBlock* afterBB   = BasicBlock::Create(getGlobalContext(), "postloop", parentFn);
  builder.CreateCondBr(endCond, loopBB, afterBB);
  builder.SetInsertPoint(afterBB);

  pickvar->addIncoming(next, loopEndBB);

  ast->value = ConstantInt::get(LLVMTypeFor("i32"), 0);
}

void CodegenPass::visit(NilExprAST* ast) {
  if (ast->value) return;
  ast->value = llvm::ConstantPointerNull::getNullValue(ast->type);
		  //ast->type->getContainedType(0));
}

void CodegenPass::visit(RefExprAST* ast) {
  if (ast->value) return;

  // Some values will see that they're a child of a RefExpr and substitute
  // a malloc for an alloca; others, like int literals or such, must be
  // manually copied out to a newly-malloc'ed cell.
  ast->value = ast->parts[0]->value;
#if 1
  std::cout << "refExprAST (indirect? "<< ast->isIndirect() << ")"
      << ": val ty is " << *(ast->value->getType())
      << "; ast ty is " << *(ast->type) << std::endl;
#endif

  if (ast->isIndirect()) {
    if (ast->type == ast->value->getType()) {
      // e.g. ast type is i32* but value type is i32* instead of i32**
      llvm::Value* stackslot = CreateEntryAlloca(ast->value->getType(), "stackslot");
      builder.CreateStore(ast->value, stackslot, /*isVolatile=*/ false);
      ast->value = stackslot;
    } else if (isPointerToType(ast->type, ast->value->getType())) {
      // If we're given a T when we want a T**, malloc a new T to get a T*
      // stored in a T** on the stack, then copy our T into the T*.
      const llvm::Type* T = ast->value->getType();
      // stackslot has type T**
      llvm::Value* stackslot = emitMalloc(T);
      // mem has type T*
      llvm::Value* mem = builder.CreateLoad(stackslot, /*isVolatile=*/false, "destack");
      // write our T into the T* given by malloc
      builder.CreateStore(ast->value, mem, /*isVolatile=*/ false);
      ast->value = stackslot;
    }
  } else {
    if (isPointerToType(ast->type, ast->value->getType())) {
      // e.g. ast type is i32* but value type is i32
      // stackslot has type i32* (not i32**)
      llvm::Value* stackslot = CreateEntryAlloca(ast->value->getType(), "stackslot");
      builder.CreateStore(ast->value, stackslot, /*isVolatile=*/ false);
      ast->value = stackslot;
    }
  }
}

void CodegenPass::visit(DerefExprAST* ast) {
  if (ast->value) return;

  llvm::Value* src = ast->parts[0]->value;
#if 0
  std::cout << "deref value of type " << *(src->getType())
       << " vs ast type of " << *(ast->type) << std::endl;
#endif
  if (isPointerToPointerToType(src->getType(), ast->type)) {
    src = builder.CreateLoad(src, /*isVolatile=*/ false, "prederef");
  }

  assert(isPointerToType(src->getType(), ast->type)
      && "deref needs a T* to produce a T!");
  ast->value = builder.CreateLoad(src, /*isVolatile=*/ false, "deref");
}

void CodegenPass::visit(AssignExprAST* ast) {
  if (ast->value) return;

  const llvm::Type* srcty = ast->parts[1]->value->getType();
  llvm::Value* dst = ast->parts[0]->value;
#if 0
  std::cout << "assign " << *(srcty) << " to " << *(dst->getType()) << std::endl;
#endif

  if (isPointerToPointerToType(dst->getType(), srcty)) {
    dst = builder.CreateLoad(dst, /*isVolatile=*/ false, "unstack");
  }

  assert(isPointerToType(dst->getType(), srcty) && "assignment must store T in a T*");

  builder.CreateStore(ast->parts[1]->value, dst);

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

#if 0
  llvm::errs() << "subscriptast base: " << *base
      << "\n\tof type " << *(base->getType())
      << "\n\twith ast type: " << *(ast->type) << "\n";
#endif

  // TODO why does ast have no type here...?
  const llvm::Type* baseTy = base->getType();
  if ((ast->type && isPointerToType(baseTy, ast->type))
      || (baseTy->isPointerTy()
       && baseTy->getContainedType(0)->isPointerTy())) {
    base = builder.CreateLoad(base, /*isVolatile*/ false, "subload");
  }

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
  llvm::AllocaInst* trampolineBuf = CreateEntryAlloca(trampolineArrayType, "trampBuf");

  trampolineBuf->setAlignment(16); // sufficient for x86 and x86_64
  Value* trampi8 = builder.CreateBitCast(trampolineBuf, pi8, "trampi8");

  //markGCRoot(trampolineBuf, NULL);

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

  // Stack slot loads must be done after codegen for all arguments
  // has taken place, in order to ensure that no allocations will occur
  // between the load and the call.
  for (int i = 0; i < valArgs.size(); ++i) {
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

    // Give print_ref() "polymorphic" behavior by converting a pointer argument
    // of any type to the expected type (i8*, probably).
    if (V->getType() != expectedType
     && V->getType()->isPointerTy() && isPrintRef(base)) {
      V = builder.CreateBitCast(V, expectedType, "polyptr");
    }

    if (V->getType() != expectedType) {
      std::cout << "Error: arg " << i << " of call to " << *base << " has type mismatch:\n"
          << *(V->getType()) << " vs expected type " << *(expectedType) << "\n";
    }
  }

  if (false) {
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

  // If we have e.g. a function like mk-tree(... to ref node)
  // that returns a pointer, we assume that the pointer refers to
  // heap-allocated memory and must be stored on the stack and marked
  // as a GC root. In order that updates from the GC take effect,
  // we use the stack slot (of type T**) instead of the pointer (T*) itself
  // as the return value of the call.
  if (ast->value->getType()->isPointerTy()) {
    const llvm::Type* retty = ast->value->getType();
    if (retty->getContainedType(0)->isPointerTy()) {
      // have T**; load T* value so it can be stored in a gcroot slot
      ast->value = builder.CreateLoad(ast->value, /*isVolatile=*/ false, "destack");
    }

    ast->value = storeAndMarkPointerAsGCRoot(ast->value);
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
    ast->value = CreateEntryAlloca(arrayType, "noInitArr");

    // We only need to mark arrays of non-atomic objects as GC roots
    // TODO handle rooting arrays of non-atomic objects
    //if (containsPointers(arrayType->getElementType())) {
    //  markGCRoot(ast->value, NULL);
    //}

    // TODO add call to memset
  } else {
    // Have initializers; are they constants?
    if (isComposedOfIntLiterals(body)) {
      ast->value = getGlobalArrayVariable(body, arrayType);
    } else {
      ast->value = CreateEntryAlloca(arrayType, "initArr");

      // We only need to mark arrays of non-atomic objects as GC roots
	  // TODO handle rooting arrays of non-atomic objects
	  //if (containsPointers(arrayType->getElementType())) {
	  //  markGCRoot(ast->value, NULL);
	  //}

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
    llvm::AllocaInst* pt = CreateEntryAlloca(simdType, "s");
    // simd vectors are never gc roots
    for (int i = 0; i < body->parts.size(); ++i) {
      Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "simd-gep");
      body->parts[i]->accept(this);
      builder.CreateStore(body->parts[i]->value, dst, /*isVolatile=*/ false);
    }
    ast->value = pt;
  }
}

// pt should be an alloca, either of type tuple* or tuple**,
// where tuple is the type of the TupleExprAST
void copyTupleTo(CodegenPass* pass, Value* pt, TupleExprAST* ast) {
  if (isPointerToPointerToType(pt->getType(), ast->type)) {
    pt = builder.CreateLoad(pt, false, "stackload");
  }

  // pt should now be of type tuple*
  assert(isPointerToType(pt->getType(), ast->type));

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  for (int i = 0; i < body->parts.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    ExprAST* part = body->parts[i];
    part->accept(pass);

    if (TupleExprAST* tu = dynamic_cast<TupleExprAST*>(part)) {
      copyTupleTo(pass, dst, tu);
    } else {
      if (part->value->getType() == dst->getType()) {
        // Storing a T* in a T* -- need to load to store a T in the T*
        llvm::Value* derefed = builder.CreateLoad(
            part->value, /*isVolatile=*/ false, "derefed");
        builder.CreateStore(derefed, dst, /*isVolatile=*/ false);
      } else if (isPointerToType(dst->getType(), part->value->getType())) {
        builder.CreateStore(part->value, dst, /*isVolatile=*/ false);
      } else {
        std::cerr << "Can't store a value of type " << *(part->value->getType())
            << " in a pointer of type " << *(dst->getType()) << std::endl;
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
  if (ast->value) return;

  std::cout << "CodegenPass visiting TupleExprAST " << ast << std::endl;

  assert(ast->type != NULL);

  // Create struct type underlying tuple
  const Type* tupleType = ast->type;

  registerType(tupleType, "tuple");

  llvm::Value* pt = NULL;

  // Allocate tuple space
  if (RefExprAST* ref = dynamic_cast<RefExprAST*>(ast->parent)) {
    // pt has type tuple**
    pt = emitMalloc(tupleType);
  } else {
    // pt has type tuple*
    pt = CreateEntryAlloca(tupleType, "s");
  }

#if 0
  // We only need to mark tuples containing pointers as GC roots
  if (structTypeContainsPointers(llvm::dyn_cast<llvm::StructType>(tupleType))) {
    storeAndMarkValueAsGCRoot(pt);
  }
#endif

  std::cout << "1350" << std::endl;
  copyTupleTo(this, pt, ast);
  std::cout << "1352" << std::endl;
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
