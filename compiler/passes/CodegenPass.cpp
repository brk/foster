// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "parse/FosterAST.h"
#include "parse/CompilationContext.h"
#include "passes/CodegenPass.h"
#include "passes/TypecheckPass.h"
#include "parse/FosterUtils.h"
#include "_generated_/FosterConfig.h"

#include "llvm/Attributes.h"
#include "llvm/CallingConv.h"
#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Target/TargetData.h"

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
using llvm::APInt;
using llvm::PHINode;
using llvm::dyn_cast;

using foster::LLVMTypeFor;
using foster::module;
using foster::builder;
using foster::SourceRange;
using foster::EDiag;
using foster::show;

typedef std::pair<const llvm::Type*, int> OffsetInfo;
typedef std::set<OffsetInfo> OffsetSet;

// TODO replace with ConstantExpr::getOffsetOf(ty, slot) ?
int getOffsetOfStructSlot(const llvm::StructType* ty, int slot) {
  const llvm::TargetData* td = foster::ee->getTargetData();
  ASSERT(td) << "Need TargetData to compute struct offsets!";
  int offset = 0;
  for (int i = 0; i < slot; ++i) {
        offset += td->getTypeStoreSize(ty->getContainedType(i));
  }
  return offset;
}

OffsetSet countPointersInType(const llvm::Type* ty) {
  ASSERT(ty) << "Can't count pointers in a NULL type!";

  OffsetSet rv;
  if (ty->isPointerTy()) {
        rv.insert(OffsetInfo(ty->getContainedType(0), 0));
  }

  // array, struct, union
  else if (dyn_cast<const llvm::ArrayType>(ty)) {
    // TODO need to decide how Foster semantics will map to LLVM IR for arrays.
    // Will EVERY (C++), SOME (Factor, C#?), or NO (Java) types be unboxed?
    // Also need to figure out how the gc will collect arrays.
    //return aty->getNumElements() * countPointersInType(aty->getElementType());
  }

  // if we have a struct { T1; T2 } then our offset set will be the set for T1,
  // plus the set for T2 with offsets incremented by the size of T1.
  else if (const llvm::StructType* sty
                            = dyn_cast<const llvm::StructType>(ty)) {
    for (size_t i = 0; i < sty->getNumElements(); ++i) {
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
  else if (dyn_cast<const llvm::UnionType>(ty)) {
    //return 0;
  }

  // all other types do not contain pointers
  return rv;
}

llvm::ConstantInt* getConstantInt64For(int64_t val) {
  return ConstantInt::get(Type::getInt64Ty(getGlobalContext()), val);
}

llvm::ConstantInt* getConstantInt32For(int val) {
  return ConstantInt::get(Type::getInt32Ty(getGlobalContext()), val);
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
        fields.push_back(
            llvm::ConstantExpr::getCast(llvm::Instruction::IntToPtr,
                                        llvm::ConstantExpr::getSizeOf(entryTy),
                                        LLVMTypeFor("i8*")));
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

void printOffsets(std::ostream& out, const OffsetSet& os) {
  for (OffsetSet::iterator it = os.begin(); it != os.end(); ++it) {
    out << "\t{ " << it->second << " : " << *(it->first) << " }\n";
  }
}

void removeEntryWithOffset(OffsetSet& os, int offset) {
  OffsetSet::iterator toRemove = os.end();
  for (OffsetSet::iterator it = os.begin(); it != os.end(); ++it) {
    if (it->second == offset) {
      toRemove = it;
      break;
    }
  }

  if (toRemove != os.end()) {
    os.erase(toRemove);
  }
}

// return a global corresponding to the following layout:
// struct {
//   const char* typeName;
//   i32 numPtrEntries;
//   struct { i8* typeinfo; i32 offset }[numPtrEntries];
// }
// The returned global is also stored in the typeMapForType[] map.
llvm::GlobalVariable* emitTypeMap(const llvm::Type* ty, std::string name,
    bool skipOffsetZero = false) {
  using llvm::StructType;

  OffsetSet pointerOffsets = countPointersInType(ty);
  //std::cout << "emitting type map for type " << *ty 
  // << " ; skipping offset zero? " << skipOffsetZero << std::endl;

  if (skipOffsetZero) {
    // Remove entry for first pointer, which corresponds
    // to the type map for the environment.
    removeEntryWithOffset(pointerOffsets, 0);
  }
  int numPointers = pointerOffsets.size();

  // Construct the type map's LLVM type
  std::vector<const Type*> entryty_types;
  entryty_types.push_back(LLVMTypeFor("i8*"));
  entryty_types.push_back(LLVMTypeFor("i32"));
  StructType* entryty = StructType::get(getGlobalContext(),
                                        entryty_types,
                                        /*isPacked=*/false);
  module->addTypeName("typemap_entry", entryty);

  std::vector<const Type*> typeMapTyFields;
  llvm::ArrayType* entriesty = llvm::ArrayType::get(entryty, numPointers);

  typeMapTyFields.push_back(LLVMTypeFor("i8*"));
  typeMapTyFields.push_back(LLVMTypeFor("i32"));
  typeMapTyFields.push_back(entriesty);

  const StructType* typeMapTy = StructType::get(getGlobalContext(),
                                                typeMapTyFields);

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
  llvm::Constant* cname = llvm::ConstantArray::get(getGlobalContext(),
                                                   ss.str().c_str(),
                                                   true);
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

void registerType(const llvm::Type* ty, std::string desiredName,
    bool isClosureEnvironment = false) {
  static std::map<const llvm::Type*, bool> registeredTypes;

  if (registeredTypes[ty]) return;

  registeredTypes[ty] = true;

  std::string name = freshName(desiredName);
  module->addTypeName(name, ty);
  emitTypeMap(ty, name, isClosureEnvironment);
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
  llvm::Constant* llvm_gcroot = module->getOrInsertFunction("llvm.gcroot",
                                                          get_llvm_gcroot_ty());
  if (!llvm_gcroot) {
    std::cerr << "Error! Could not mark GC root!" << std::endl;
    exit(1);
  }

  if (!meta) {
    meta = typeMapForType[root->getType()];
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

// Checks that ty == { i32 (i8*, ...)*, i8* }
bool isGenericClosureType(const llvm::Type* ty) {
  if (const llvm::StructType* sty= dyn_cast<const llvm::StructType>(ty)) {
    if (!isValidClosureType(sty)) return false;
    if (sty->getContainedType(1) != LLVMTypeFor("i8*")) return false;
    if (!sty->getContainedType(0)->isPointerTy()) return false;

    const llvm::Type* fnty = sty->getContainedType(0)->getContainedType(0);
    if (!fnty->isFunctionTy()) return false;
    if (!fnty->getNumContainedTypes() >= 2) return false;
    if (fnty->getContainedType(0) != LLVMTypeFor("i32")) return false;
    if (fnty->getContainedType(1) != LLVMTypeFor("i8*")) return false;
    return true;
  }
  return false;
}

llvm::GlobalVariable* getTypeMapForType(const llvm::Type* ty) {
  llvm::GlobalVariable* gv = typeMapForType[ty];
  if (gv) return gv;

  if (!ty->isAbstract() && !ty->isAggregateType()) {
    gv = emitTypeMap(ty, freshName("gcatom"));
    // emitTypeMap also sticks gv in typeMapForType
  } else if (isGenericClosureType(ty)) {
    gv = emitTypeMap(ty, freshName("genericClosure"),
                     /*skipOffsetZero*/ true);
  }

  if (!gv) {
    std::cout << "No type map for type " << *(ty) << std::endl;
  }

  return gv;
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

// returns ty**, the stack slot containing a ty*
llvm::Value* emitMalloc(const llvm::Type* ty) {
  llvm::Value* memalloc = gScopeLookupValue("memalloc");
  if (!memalloc) {
    std::cerr << "NO MEMALLOC IN MODULE! :(" << std::endl;
    return NULL;
  }
  llvm::Value* mem = builder.CreateCall(memalloc,
                                        getConstantInt64For(32),
                                        "mem");
  return storeAndMarkPointerAsGCRoot(
      builder.CreateBitCast(mem, llvm::PointerType::getUnqual(ty), "ptr"));
}


bool mightContainHeapPointers(const llvm::Type* ty) {
  // For now, we don't distinguish between different kinds of pointer;
  // we consider any pointer to be a possible heap pointer.
  OffsetSet offsets = countPointersInType(ty);
  return !offsets.empty();
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
  // This looks up the lexically closest definition for the given variable
  // name, as provided by a function parameter or some such binding construct.
  // Note that ast->value is NOT used to cache the result; this ensures
  // that closure conversion is free to duplicate AST nodes and still get
  // properly scoped argument values inside converted functions.
  if (ast->lazilyInsertedPrototype) {
    if (!ast->lazilyInsertedPrototype->value) {
      ast->lazilyInsertedPrototype->accept(this);
    }
    ast->value = ast->lazilyInsertedPrototype->value;
  } else {
    ast->value = gScopeLookupValue(ast->name);
    if (!ast->value) {
      EDiag() << "looking up variable " << ast->name << ", got "
              << str(ast->value) << show(ast);
      gScope.dump(std::cout);
    }
  }

#if 0
  if (isPointerToType(ast->value->getType(), ast->type) &&
      !ast->type->isFunctionTy()) {
    std::cout << "\tfound indirect variable of type "
        << *(ast->type) << ": " << ast->name << std::endl;
  }
#endif

  if (!ast->value) {
    EDiag() << "Unknown variable name " << ast->name << " in CodegenPass"
            << show(ast);
    exit(2);
  }
}

void CodegenPass::visit(UnaryOpExprAST* ast) {
  if (ast->value) return;

  Value* V = ast->parts[0]->value;
  const std::string& op = ast->op;

  if (!V) {
    EDiag() << "unary op " << op << " had null operand" << show(ast);
    return;
  }

       if (op == "-")   { ast->value = builder.CreateNeg(V, "negtmp"); }
  else if (op == "not") { ast->value = builder.CreateNot(V, "nottmp"); }
  else {
    EDiag() << "unknown unary op '" << op << "' during codegen" << show(ast);
  }
}

bool leftTypeBiggerInt(const Type* left, const Type* right) {
  return left->getScalarSizeInBits() > right->getScalarSizeInBits();
}

void CodegenPass::visit(BinaryOpExprAST* ast) {
  if (ast->value) return;

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

       if (op == "+") { ast->value = builder.CreateAdd(VL, VR, "addtmp"); }
  else if (op == "-") { ast->value = builder.CreateSub(VL, VR, "subtmp"); }
  else if (op == "/") { ast->value = builder.CreateSDiv(VL, VR, "divtmp"); }
  else if (op == "*") { ast->value = builder.CreateMul(VL, VR, "multmp"); }

  else if (op == "<")  { ast->value = builder.CreateICmpSLT(VL, VR, "slttmp"); }
  else if (op == "<=") { ast->value = builder.CreateICmpSLE(VL, VR, "sletmp"); }
  else if (op == ">")  { ast->value = builder.CreateICmpSGT(VL, VR, "sgttmp"); }
  else if (op == ">=") { ast->value = builder.CreateICmpSGE(VL, VR, "sgetmp"); }
  else if (op == "==") { ast->value = builder.CreateICmpEQ(VL, VR, "eqtmp"); }
  else if (op == "!=") { ast->value = builder.CreateICmpNE(VL, VR, "netmp"); }

  else if (op == "bitand") { ast->value = builder.CreateAnd(VL, VR, "bitandtmp"); }
  else if (op == "bitor") {  ast->value = builder.CreateOr( VL, VR, "bitortmp"); }
  else if (op == "bitxor") { ast->value = builder.CreateXor(VL, VR, "bitxortmp"); }

  else if (op == "bitshl") { ast->value = builder.CreateShl(VL, VR, "shltmp"); }
  else if (op == "bitlshr") { ast->value = builder.CreateLShr(VL, VR, "lshrtmp"); }
  else if (op == "bitashr") { ast->value = builder.CreateAShr(VL, VR, "ashrtmp"); }
  else {
    EDiag() << "unable to codegen binary '" << op << "'" << show(ast);
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
  if (ast->value) return;

  std::string symbolName = getSymbolName(ast->name);

  if (ast->scope) {
    gScope.pushExistingScope(ast->scope);
  } else {
    gScope.pushScope(ast->name);
  }

  llvm::GlobalValue::LinkageTypes functionLinkage =
      (ast->name.find("anon_fnlet_") != string::npos)
        ? Function::InternalLinkage
        : Function::ExternalLinkage;

  const llvm::FunctionType* FT = dyn_cast<FunctionType>(getLLVMType(ast->type));
  Function* F = Function::Create(FT, functionLinkage, symbolName, module);

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

  ast->value = F;
}

void CodegenPass::visit(SeqAST* ast) {
  //EDiag() << "Codegen for SeqASTs should (eventually) be subsumed by CFG building!";
  if (ast->value) return;

  if (!ast->parts.empty()) {
    // Find last non-void value
    for (size_t n = ast->parts.size() - 1; n >= 0; --n) {
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

  ASSERT(ast->body != NULL);
  ASSERT(ast->proto->scope) << " no scope for " << ast->proto->name;

  (ast->proto)->accept(this);
  Function* F = dyn_cast<Function>(ast->proto->value);
  if (!F) { return; }

#if USE_FOSTER_GC_PLUGIN
  F->setGC("fostergc");
#else
  F->setGC("shadow-stack");
#endif

  BasicBlock* prevBB = builder.GetInsertBlock();
  BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "entry", F);
  builder.SetInsertPoint(BB);

  gScopeInsert(ast->proto->name, F);
  gScope.pushExistingScope(ast->proto->scope);

  // If the body of the function might allocate memory, the first thing
  // the function should do is create stack slots/GC roots to hold
  // dynamically-allocated pointer parameters.
  if (true) { // conservative approximation to MightAlloc
    Function::arg_iterator AI = F->arg_begin();
    for (size_t i = 0; i != ast->proto->inArgs.size(); ++i, ++AI) {
      if (mightContainHeapPointers(AI->getType())) {
#if 0
        std::cout << "marking root for var " << ast->proto->inArgs[i]->name
            << " of ast type " << *(ast->proto->inArgs[i]->type)
            << " and value type " << *(AI->getType()) << std::endl;
#endif
        gScopeInsert(ast->proto->inArgs[i]->name,
            storeAndMarkPointerAsGCRoot(AI));
      }
    }
  }

  (ast->body)->accept(this);
  Value* RetVal = ast->body->value;
  if (RetVal == NULL) {
    EDiag() << "null body value when codegenning function " << ast->proto->name
            << show(ast);
    return;
  }
  ASSERT(RetVal != NULL);

  bool returningVoid = isVoid(ast->proto->resultTy);

  // If we try to return a tuple* when the fn specifies a tuple, manually insert a load
  if (RetVal->getType()->isDerivedType()
      && !returningVoid
      && isPointerToType(RetVal->getType(), ast->proto->resultTy->getLLVMType())) {
    RetVal = builder.CreateLoad(RetVal, false, "structPtrToStruct");
  }

  gScope.popExistingScope(ast->proto->scope);

  if (RetVal) {
    if (returningVoid) {
      builder.CreateRetVoid();
    } else if (isVoid(RetVal->getType())) {
      EDiag() << "unable to return non-void value given only void" << show(ast);
    } else {
      builder.CreateRet(RetVal);
    }
    //llvm::verifyFunction(*F);
    ast->value = F;
  } else {
    F->eraseFromParent();
    EDiag() << "function '" << ast->proto->name
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

  std::cout << "Specific closure, fn ty: " << *fnty << std::endl;
  std::cout << "Specific closure, env ty: " << *envPtrTy << std::endl;
  std::cout << "Specific closure, cloty: " << *cloTy << std::endl;
  return cloTy;
}

void CodegenPass::visit(ClosureAST* ast) {
  if (ast->value) return;

  if (!ast->hasKnownEnvironment) {
    EDiag() << "closure made it to codegen with no environment type" << show(ast);
  }

#if 0
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    std::cout << "Codegen ClosureAST, part: " << *ast->parts[i] << std::endl;
    std::cout << "Codegen ClosureAST, part: " << *ast->parts[i]->type << std::endl;
    std::cout << std::endl;
  }

  if (ast->parts.size() == 0) {
    std::cout << "\t\t\tclosure with empty env: " << ast << "; " << *ast << std::endl;
  }
#endif

  TupleExprAST* env = new TupleExprAST(new SeqAST(ast->parts,
                                          SourceRange::getEmptyRange()),
                                       SourceRange::getEmptyRange());
  ExprAST* fnPtr = new VariableAST(ast->fn->proto->name,
                   RefTypeAST::get(ast->fn->type), SourceRange::getEmptyRange());
  { TypecheckPass tp;
    fnPtr->accept(&tp);
    fnPtr->accept(this);

    env->isClosureEnvironment = true;
    env->accept(&tp);
    env->accept(this);
  }

  if (ast->isTrampolineVersion) {
    if (Function* func = dyn_cast<Function>(fnPtr->value)) {
      func->addAttribute(1, llvm::Attribute::Nest);
      // If we're creating a trampoline, it must be to get a value
      // callable from C; thus, we must ensure that the underlying
      // function itself gets a standard C calling convention.
      func->setCallingConv(llvm::CallingConv::C);
    }
  }

#if 0
  llvm::errs() << "Closure conversion " << ast->fn->proto->name << "\n\tfnPtr value: "
      << *fnPtr->value << "\n\tFunction? " << llvm::isa<Function>(fnPtr->value) << "\n";
#endif

  if (FnTypeAST* fnTy = dynamic_cast<FnTypeAST*>(ast->fn->type)) {
    // Manually build struct for now, since we don't have PtrAST nodes
    const llvm::StructType* specificCloTy = closureTypeFromClosedFnType(
        llvm::cast<FunctionType>(fnTy->getLLVMType()));
    TupleTypeAST* genericCloTy = genericVersionOfClosureType(fnTy);

#if 0
    std::cout << std::endl;
    std::cout << "Fn type: " << *fnTy << std::endl;
    std::cout << "Specific closure type: " << *specificCloTy << std::endl;
    std::cout << "Generic closure type: " << *genericCloTy << std::endl;
#endif

    addClosureTypeName(module, genericCloTy);

    // { code*, env* }*
    llvm::AllocaInst* clo = CreateEntryAlloca(specificCloTy, "closure");

    // TODO the (stack reference to the) closure should only be marked as
    // a GC root if the environment has been dynamically allocated...
    //markGCRoot(clo, NULL);

    // (code*)*
    Value* clo_code_slot = builder.CreateConstGEP2_32(clo, 0, 0, "clo_code");
    builder.CreateStore(fnPtr->value, clo_code_slot, /*isVolatile=*/ false);

    // (env*)*
    Value* clo_env_slot = builder.CreateConstGEP2_32(clo, 0, 1, "clo_env");

    if (!ast->parts.empty()) {
      // Store the typemap in the environment
      const llvm::Type* specificEnvTyPtr = specificCloTy->getContainedType(1);
      const llvm::Type* specificEnvTy = specificEnvTyPtr->getContainedType(0);

      llvm::GlobalVariable* clo_env_typemap
          = getTypeMapForType(specificEnvTy);

      Value* clo_env_typemap_slot = builder.CreateConstGEP2_32(env->value, 0, 0,
                                                        "clo_env_typemap_slot");
      builder.CreateStore(llvm::ConstantExpr::getBitCast(
          clo_env_typemap, clo_env_typemap_slot->getType()->getContainedType(0)),
          clo_env_typemap_slot, /*isVolatile=*/ false);
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
    ast->value = builder.CreateLoad(genericClo, /*isVolatile=*/ false, "loadClosure");
  }

  if (!ast->value) {
    EDiag() << "closure fn ref had non-function pointer type?!? "
            << str(ast->fn->type) << show(ast);
  }
}

void CodegenPass::visit(NamedTypeDeclAST* ast) {
  return;
}

void CodegenPass::visit(ModuleAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    ast->parts[i]->accept(this);
  }
}

void CodegenPass::visit(IfExprAST* ast) {
  //EDiag() << "Codegen for IfExprASTs should (eventually) be subsumed by CFG building!";
  if (ast->value) return;

  (ast->testExpr)->accept(this);
  Value* cond = ast->testExpr->value;
  if (!cond) return;

  Function *F = builder.GetInsertBlock()->getParent();

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then", F);
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);

  Value* then; Value* else_;

  { // Codegen the then-branch of the if expression
    builder.SetInsertPoint(thenBB);
    ast->thenExpr->accept(this);
    then = ast->thenExpr->value;
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
    ast->elseExpr->accept(this);
    else_ = ast->elseExpr->value;
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
    ast->value = PN;
  }
}

void CodegenPass::visit(ForRangeExprAST* ast) {
  if (ast->value) return;
  //EDiag() << "Codegen for ForRangeExprASTs should (eventually) be subsumed by CFG building!";

  Function* parentFn = builder.GetInsertBlock()->getParent();
  ////BasicBlock* preLoopBB  = builder.GetInsertBlock();
  BasicBlock* loopHdrBB  = BasicBlock::Create(llvm::getGlobalContext(), "forToHdr", parentFn);
  BasicBlock* loopBB     = BasicBlock::Create(llvm::getGlobalContext(), "forTo", parentFn);
  BasicBlock* afterBB    = BasicBlock::Create(llvm::getGlobalContext(), "postloop", parentFn);

  // InsertPoint is preLoopBB
  builder.CreateBr(loopHdrBB);


  builder.SetInsertPoint(loopHdrBB);
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

  (ast->endExpr)->accept(this);
  if (!ast->endExpr->value) { return; }



/* Generate LLVM IR with the following CFG structure:
preLoopBB:
      ...
      br loopHdrBB

loopHdrBB:
      incr = incrExpr
      end = endExpr
      sv = startExpr
      precond = sv < end
      br precond? loopBB afterBB

loopBB:
      loopvar = phi...
      body
      ...

loopEndBB:
      ...
      next = loopvar + 1

      cond = next < end
      br cond? loopBB afterBB

afterBB:
      (to be filled in by further codegen)
 */

  builder.SetInsertPoint(loopBB);

    llvm::PHINode* pickvar = builder.CreatePHI(getLLVMType(ast->var->type),
                                               ast->var->name);

    gScope.pushScope("for-range " + ast->var->name);
    gScopeInsert(ast->var->name, (pickvar));

    (ast->bodyExpr)->accept(this);
    if (!ast->bodyExpr->value) { return; }
    gScope.popScope();


  BasicBlock* loopEndBB = builder.GetInsertBlock();

  builder.SetInsertPoint(loopEndBB);

    Value* next = builder.CreateAdd(pickvar, incr, "next");
    Value* endCond = builder.CreateICmpSLT(next, ast->endExpr->value,
                                           "loopcond");
    builder.CreateCondBr(endCond, loopBB, afterBB);


  // At the start of the loop, compare start and end (instead of next and end)
  // and skip the loop if we shouldn't execute it.
  builder.SetInsertPoint(loopHdrBB);
  {
    Value* startCond = builder.CreateICmpSLT(ast->startExpr->value,
                                             ast->endExpr->value,
                                             "preloopcond");
    builder.CreateCondBr(startCond, loopBB, afterBB);
  }

  pickvar->addIncoming(ast->startExpr->value, loopHdrBB);
  pickvar->addIncoming(next, loopEndBB);

  // Leave the insert point after the loop for later codegenning.
  builder.SetInsertPoint(afterBB);

  ast->value = ConstantInt::get(LLVMTypeFor("i32"), 0);
}

void CodegenPass::visit(NilExprAST* ast) {
  if (ast->value) return;
  ast->value = llvm::ConstantPointerNull::getNullValue(getLLVMType(ast->type));
}

void CodegenPass::visit(RefExprAST* ast) {
  if (ast->value) return;

  // Some values will see that they're a child of a RefExpr and substitute
  // a malloc for an alloca; others, like int literals or such, must be
  // manually copied out to a newly-malloc'ed cell.
  ast->value = ast->parts[0]->value;

  if (ast->isIndirect()) {
    if (getLLVMType(ast->type) == ast->value->getType()) {
      // e.g. ast type is i32* but value type is i32* instead of i32**
      llvm::Value* stackslot = CreateEntryAlloca(ast->value->getType(),
                                                 "stackslot");
      builder.CreateStore(ast->value, stackslot, /*isVolatile=*/ false);
      ast->value = stackslot;
    } else if (isPointerToType(getLLVMType(ast->type), ast->value->getType())) {
      // If we're given a T when we want a T**, malloc a new T to get a T*
      // stored in a T** on the stack, then copy our T into the T*.
      const llvm::Type* T = ast->value->getType();
      // stackslot has type T**
      llvm::Value* stackslot = emitMalloc(T);
      // mem has type T*
      llvm::Value* mem = builder.CreateLoad(stackslot,
                                            /*isVolatile=*/false,
                                            "destack");
      // write our T into the T* given by malloc
      builder.CreateStore(ast->value, mem, /*isVolatile=*/ false);
      ast->value = stackslot;
    }
  } else {
    if (isPointerToType(getLLVMType(ast->type), ast->value->getType())) {
      // e.g. ast type is i32* but value type is i32
      // stackslot has type i32* (not i32**)
      llvm::Value* stackslot = CreateEntryAlloca(ast->value->getType(),
                                                 "stackslot");
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
  if (isPointerToPointerToType(src->getType(), getLLVMType(ast->type))) {
    src = builder.CreateLoad(src, /*isVolatile=*/ false, "prederef");
  }

  ASSERT(isPointerToType(src->getType(), getLLVMType(ast->type)))
      << "deref needs a T* to produce a T, given src type "
      << str(src->getType()) << " and ast type " << str(getLLVMType(ast->type));
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

  ASSERT(isPointerToType(dst->getType(), srcty))
    << "assignment must store T in a T*, given dst type "
    << str(dst->getType()) << " and srcty " << str(srcty);

  builder.CreateStore(ast->parts[1]->value, dst);

  // Mark the assignment as having been codegenned; for now, assignment
  // expressions evaluate to constant zero (annotated for clarity).
  ConstantInt* zero = ConstantInt::get(Type::getInt32Ty(getGlobalContext()), 0);
  ast->value = builder.CreateBitCast(zero, zero->getType(), "assignval");
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
    unsigned uidx = getSaturating<unsigned>(idxValue);
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
  if (getLLVMType(ast->type) && isPointerToType(baseTy, getLLVMType(ast->type))
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

FnAST* getVoidReturningVersionOf(ExprAST* arg, FnTypeAST* fnty) {
  static std::map<string, FnAST*> voidReturningVersions;
  string protoName;
  if (VariableAST* var = dynamic_cast<VariableAST*>(arg)) {
    protoName = var->name;
  } else if (PrototypeAST* proto = dynamic_cast<PrototypeAST*>(arg)) {
    protoName = proto->name;
  }

  if (!protoName.empty()) {
    string fnName = "__voidReturningVersionOf__" + protoName;
    if (FnAST* exists = voidReturningVersions[fnName]) {
      return exists;
    }

    // Create function  void fnName(arg-args) { arg(arg-args) }
    std::vector<VariableAST*> inArgs;
    std::vector<ExprAST*> callArgs;

    for (size_t i = 0; i < fnty->getNumParams(); ++i) {
      std::stringstream ss; ss << "a" << i;
      // TODO fix this...
      VariableAST* a = new VariableAST(ss.str(),
                                       fnty->getParamType(i),
                                       SourceRange::getEmptyRange());
      inArgs.push_back(a);
      callArgs.push_back(a);
    }

    foster::SymbolTable<foster::SymbolInfo>::LexicalScope* protoScope =
                                    gScope.newScope("fn proto " + fnName);
    gScope.popExistingScope(protoScope);
    PrototypeAST* proto = new PrototypeAST(
                                TypeAST::getVoid(),
                                fnName, inArgs, protoScope,
                                SourceRange::getEmptyRange());
    ExprAST* body = new CallAST(arg, callArgs, SourceRange::getEmptyRange());
    FnAST* fn = new FnAST(proto, body, SourceRange::getEmptyRange());
    { TypecheckPass tp; CodegenPass cp; fn->accept(&tp); fn->accept(&cp); }
    voidReturningVersions[fnName] = fn;
    return fn;
  } else {
    EDiag() << "getVoidReturningVersionOf() expected a variable naming a fn, "
            << "but got" << show(arg);
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

  // TODO need to call a runtime library function to get mprotect()ed pages
  // on Mac OS X; 10.5 marks stack as NX, and 10.6 marks stack and heap pages
  // as NX by default.
  //
  // TODO also need to think about if/how trampolines, external C code, and GC
  // might play nice. Trampolines effectively serve as (very likely) GC roots
  // that we don't control and cannot directly track, and which (probably) must
  // pin whatever memory they can access, to avoid possible data races with
  // C code when updating pointers in the trampoline env after copying GC.
  const llvm::Type* trampolineArrayType = llvm::ArrayType::get(i8, 32); // Sufficient for x86 and x86_64
  llvm::AllocaInst* trampolineBuf = CreateEntryAlloca(trampolineArrayType, "trampBuf");

  trampolineBuf->setAlignment(32); // sufficient for x86 and x86_64
  Value* trampi8 = builder.CreateBitCast(trampolineBuf, pi8, "trampi8");

  //markGCRoot(trampolineBuf, NULL);

  // It would be nice and easy to extract the code pointer from the closure,
  // but LLVM requires that pointers passed to trampolines be "obvious" function
  // pointers. Thus, we need direct access to the closure's underlying fn.
  ExprAST* fnPtr = new VariableAST(cloAST->fn->proto->name,
                               RefTypeAST::get(cloAST->fn->type),
                               SourceRange::getEmptyRange());
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

FnAST* getClosureVersionOf(ExprAST* arg, FnTypeAST* fnty) {
  static std::map<string, FnAST*> closureVersions;
  string protoName;
  if (VariableAST* var = dynamic_cast<VariableAST*>(arg)) {
    protoName = var->name;
  } else if (PrototypeAST* proto = dynamic_cast<PrototypeAST*>(arg)) {
    protoName = proto->name;
  }

  if (!protoName.empty()) {
    string fnName = "__closureVersionOf__" + protoName;
    if (FnAST* exists = closureVersions[fnName]) {
      return exists;
    }

    // Create function    fnName(i8* env, arg-args) { arg(arg-args) }
    // that hard-codes call to fn referenced by arg

    std::vector<VariableAST*> inArgs;
    std::vector<ExprAST*> callArgs;
    inArgs.push_back(new VariableAST("__ignored_env__",
        RefTypeAST::get(TypeAST::i(8)),
        SourceRange::getEmptyRange()));

    for (size_t i = 0; i < fnty->getNumParams(); ++i) {
      std::stringstream ss; ss << "a" << i;
      VariableAST* a = new VariableAST(ss.str(),
                             fnty->getParamType(i),
                             SourceRange::getEmptyRange());
      inArgs.push_back(a);
      callArgs.push_back(a);
    }

    foster::SymbolTable<foster::SymbolInfo>::LexicalScope* protoScope =
                                    gScope.newScope("fn proto " + fnName);
    gScope.popExistingScope(protoScope);
    PrototypeAST* proto = new PrototypeAST(fnty->getReturnType(),
                               fnName, inArgs, protoScope,
                                               SourceRange::getEmptyRange());
    ExprAST* body = new CallAST(arg, callArgs, SourceRange::getEmptyRange());
    FnAST* fn = new FnAST(proto, body, SourceRange::getEmptyRange());
    { TypecheckPass tp; CodegenPass cp; fn->accept(&tp); fn->accept(&cp); }
    closureVersions[fnName] = fn;
    return fn;
  } else {
    EDiag() << "getClosureVersionOf() expected a variable or prototype of a fn, "
            << "but got" << str(arg) << show(arg);
    exit(1);
  }
  return NULL;
}

llvm::Value* getClosureStructValue(llvm::Value* maybePtrToClo) {
  if (maybePtrToClo->getType()->isPointerTy()) {
    maybePtrToClo = builder.CreateLoad(maybePtrToClo, /*isVolatile=*/ false, "derefCloPtr");
  }
  if (maybePtrToClo->getType()->isPointerTy()) {
    maybePtrToClo = builder.CreateLoad(maybePtrToClo, /*isVolatile=*/ false, "derefCloPtr");
  }
  return maybePtrToClo;
}

void CodegenPass::visit(CallAST* ast) {
  if (ast->value) return;

  ExprAST* base = ast->parts[0];
  ASSERT(base != NULL);

  //std::cout << "\t" << "Codegen CallAST "  << (base) << std::endl;
  //std::cout << "\t\t\tbase ast: "  << *(base) << std::endl;

  // TODO if base has closure type, it should be a ClosureAST node

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
    std::cout << "closure fntype is " << fty << std::endl;
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

    // Codegenning   callee( arg )  where arg has raw function type, not closure type!
    if (FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(arg->type)) {
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

      std::cout << "Passing function to " << (passFunctionPointer ? "fn ptr" : "closure") << "\n";

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
            arg = getVoidReturningVersionOf(arg, fnty);
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
        std::cout << "clo 1347 = " << clo << std::endl;
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
    } else {
      clo = dynamic_cast<ClosureAST*>(arg);
    }

    arg->accept(this);
    Value* V = arg->value;
    if (!V) {
      EDiag() << "null value for argument " << (i - 1) << " of call"
              << show(arg);
      return;
    }

    if (clo && clo->isTrampolineVersion) {
      std::cout << "Creating trampoline for closure; bitcasting to " << *expectedType << std::endl;
      V = builder.CreateBitCast(getTrampolineForClosure(clo), expectedType, "trampfn");
    }

    appendArg(valArgs, V, FT); // Don't unpack non 'unpack'-marked structs
  }

  // Stack slot loads must be done after codegen for all arguments
  // has taken place, in order to ensure that no allocations will occur
  // between the load and the call.
  for (size_t i = 0; i < valArgs.size(); ++i) {
    llvm::Value*& V = valArgs[i];

    // ContainedType[0] is the return type; args start at 1
    const llvm::Type* expectedType = FT->getContainedType(i + 1);
    
    std::cout <<" FT: " << str(FT) << std::endl;

    // If we're given a T** when we expect a T*,
    // automatically load the reference from the stack.
    if (V->getType() != expectedType
     && expectedType->isPointerTy()
     && isPointerToType(V->getType(), expectedType)) {
      V = builder.CreateLoad(V, /*isVolatile=*/ false, "unstackref");
    }

    bool needsAdjusting = V->getType() != expectedType;
    if (needsAdjusting) {
      EDiag() << str(V) << "->getType() is " << str(V->getType())
              << "; expecting " << str(expectedType) << show(ast->parts[i + 1]);
    }

    // If we're given a clo** when we expect a clo,
    // automatically load the reference from the stack.
    if (isPointerToPointerToType(V->getType(), expectedType)
     && isGenericClosureType(expectedType)) {
      V = getClosureStructValue(V);
    }

    if (needsAdjusting) {
      std::cout << V << "->getType() is " << str(V->getType())
          << "; expect clo? " << isGenericClosureType(expectedType) << std::endl;
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

  if (false) {
    std::cout << "Creating call for AST {" << valArgs.size() << "} " << *base << std::endl;
    for (size_t i = 0; i < valArgs.size(); ++i) {
      llvm::errs() << "\tAST arg " << i << ":\t" << *valArgs[i] << "\n";
    }
  }

  size_t expectedNumArgs = FT->getNumParams();
  if (expectedNumArgs != valArgs.size()) {
    EDiag() << "function arity mismatch, got " << valArgs.size()
            << " but expected " << expectedNumArgs
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

  ast->value = callInst;

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
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    IntAST* v = dynamic_cast<IntAST*>(ast->parts[i]);
    if (!v) { return false; }
  }
  return true;
}

#if 0
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

    ConstantInt* ci = dyn_cast<ConstantInt>(v->getConstantValue());
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
  if (ast->value) return;

  const llvm::ArrayType* arrayType
                            = dyn_cast<llvm::ArrayType>(getLLVMType(ast->type));
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

      for (size_t i = 0; i < body->parts.size(); ++i) {
        builder.CreateStore(body->parts[i]->value,
                            getPointerToIndex(ast->value, i, "arrInit"));
      }
    }
  }
}
#endif

void CodegenPass::visit(SimdVectorAST* ast) {
  if (ast->value) return;

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
      llvm::Constant* ci = intlit->getConstantValue();
      elements.push_back(dyn_cast<llvm::Constant>(ci));
    }

    llvm::Constant* constVector = llvm::ConstantVector::get(simdType, elements);
    gvar->setInitializer(constVector);
    ast->value = builder.CreateLoad(gvar, /*isVolatile*/ false, "simdLoad");
  } else {
    llvm::AllocaInst* pt = CreateEntryAlloca(simdType, "s");
    // simd vectors are never gc roots
    for (size_t i = 0; i < body->parts.size(); ++i) {
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
  if (isPointerToPointerToType(pt->getType(), getLLVMType(ast->type))) {
    pt = builder.CreateLoad(pt, false, "stackload");
  }

  // pt should now be of type tuple*
  ASSERT(isPointerToType(pt->getType(), getLLVMType(ast->type)));

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  for (size_t i = 0; i < body->parts.size(); ++i) {
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
  if (ast->value) return;

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

  copyTupleTo(this, pt, ast);
  ast->value = pt;
}

void CodegenPass::visit(BuiltinCompilesExprAST* ast) {
  if (ast->status == ast->kWouldCompile) {
    ast->value = ConstantInt::getTrue(getGlobalContext());
  } else if (ast->status == ast->kWouldNotCompile) {
    ast->value = ConstantInt::getFalse(getGlobalContext());
  } else {
    EDiag() << "__COMPILES__ expression not checked" << show(ast);
    ast->value = ConstantInt::getFalse(getGlobalContext());
  }
}
