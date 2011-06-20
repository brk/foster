// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterLL.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"
#include "parse/ParsingContext.h"
#include "parse/DumpStructure.h"

#include "passes/CodegenPass-impl.h"

#include "llvm/Attributes.h"
#include "llvm/CallingConv.h"
#include "llvm/LLVMContext.h"
#include "llvm/Intrinsics.h"

#include "llvm/Metadata.h"
//#include "llvm/Analysis/DIBuilder.h"
#include "llvm/Support/Dwarf.h"

#include "pystring/pystring.h"

#include <map>
#include <sstream>

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

using foster::builder;
using foster::currentOuts;
using foster::currentErrs;
using foster::SourceRange;
using foster::ParsingContext;
using foster::EDiag;
using foster::show;

char kFosterMain[] = "foster__main";

struct IsClosureEnvironment {
  explicit IsClosureEnvironment(bool v) : value(v) {}
  bool value;
};

struct CanStackAllocate {
  explicit CanStackAllocate(bool v) : value(v) {}
  bool value;
};

namespace foster {

void codegenLL(LLModule* package, llvm::Module* mod) {
  CodegenPass cp(mod);
  package->codegen(&cp);
}

std::string getGlobalSymbolName(const std::string& sourceName) {
  if (sourceName == "main") {
    // libfoster contains a main() symbol that handles
    // initialization and shutdown/cleanup of the runtime,
    // calling this symbol in between.
    return kFosterMain;
  }
  return sourceName;
}

} // namespace foster

CanStackAllocate canStackAllocate(LLTuple* ast) {
  return CanStackAllocate(true);
}

// Follows a (type-based) pointer indirections for the given value.
llvm::Value* getClosureStructValue(llvm::Value* maybePtrToClo) {
  llvm::outs() << "maybePtrToClo: " << str(maybePtrToClo) << "\n";
  if (maybePtrToClo->getType()->isPointerTy()) {
    maybePtrToClo = builder.CreateLoad(maybePtrToClo, /*isVolatile=*/ false, "derefCloPtr");
  }
  ASSERT(maybePtrToClo->getType()->isStructTy());
  return maybePtrToClo;
}

const llvm::Type* getLLVMType(TypeAST* type) {
  ASSERT(type) << "getLLVMType must be given a non-null type!";
  return type->getLLVMType();
}


////////////////////////////////////////////////////////////////////

void LLModule::codegen(CodegenPass* pass) {
  // Ensure that the llvm::Function*s are created for all the function
  // prototypes, so that mutually recursive function references resolve.
  for (size_t i = 0; i < procs.size(); ++i) {
    LLProc* f = procs[i];
    // Ensure that the value is in the SymbolInfo entry in the symbol table.
    pass->valueSymTab.insert(f->getName(), f->codegenProto(pass));
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegen(pass);
  }
}

bool isSafeToStackAllocate(LLTuple* ast) {
  return true;
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

llvm::Value* generateAllocDAarray32(CodegenPass* pass) {
  // Create a function of type  array[i32] (i32 n)
  std::vector<const Type*> fnTyArgs;
  fnTyArgs.push_back(builder.getInt32Ty());

  const llvm::Type* elt_ty = builder.getInt32Ty();
  const llvm::FunctionType* fnty =
        llvm::FunctionType::get(
                   /*Result=*/   ArrayTypeAST::getZeroLengthTypeRef(elt_ty),
                   /*Params=*/   fnTyArgs,
                   /*isVarArg=*/ false);

  Function* f = Function::Create(
    /*Type=*/    fnty,
    /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
    /*Name=*/    ".foster_alloc_array_32", pass->mod);

  f->setGC("fostergc");

  /////////////////////////////

  Function::arg_iterator args = f->arg_begin();
  Value* n = args++;
  n->setName("n");

  BasicBlock* prevBB = builder.GetInsertBlock();
  BasicBlock* BB = BasicBlock::Create(builder.getContext(), "entry", f);
  builder.SetInsertPoint(BB);

  Value* slot = pass->emitArrayMalloc(elt_ty, n);
  builder.CreateRet(builder.CreateLoad(slot, /*isVolatile=*/ false));

  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return f;
}

llvm::Value* CodegenPass::lookup(const std::string& fullyQualifiedSymbol) {
  llvm::Value* v =  valueSymTab.lookup(fullyQualifiedSymbol);
  if (v) return v;

  // Otherwise, it should be a function name.
  v = mod->getFunction(fullyQualifiedSymbol);

  if (!v && fullyQualifiedSymbol == "allocDArray32") {
    v = generateAllocDAarray32(this);
  }

  if (!v) {
   currentErrs() << "name was neither fn arg nor fn name: "
              << fullyQualifiedSymbol << "\n";
   valueSymTab.dump(currentErrs());
   ASSERT(false) << "unable to find value for symbol " << fullyQualifiedSymbol;
  }
  return v;
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

llvm::Value* LLInt::codegen(CodegenPass* pass) {
  ASSERT(this->type && this->type->getLLVMType());
  const llvm::Type* ty = this->type->getLLVMType();

  llvm::Value* small = ConstantInt::get(ty, this->getAPInt());

  // Our type could be an LLVM type, or an arbitrary precision int type.
  if (this->type->getLLVMType()->isIntegerTy()) {
    return small;
  } else if (false) {
    // MP integer constants that do not fit in 64 bits
    // must be initialized from string data.
    ASSERT(false) << "codegen for int values that don't fit"
                  << " in 64 bits not yet implemented";
    return NULL;
  } else {
    // Small integers may be initialized immediately.
    llvm::Value* mpint = pass->allocateMPInt();

    // Call mp_int_init_value() (ignore rv for now)
    llvm::Value* mp_int_init_value = pass->mod->getFunction("mp_int_init_value");
    ASSERT(mp_int_init_value);

    builder.CreateCall2(mp_int_init_value, mpint, small);
    return mpint;
  }
}

llvm::Value* LLBool::codegen(CodegenPass* pass) {
  return builder.getInt1(this->boolValue);
}

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  // The variable for an environment can be looked up multiple times...
  llvm::Value* v = pass->lookup(getName());

  if (llvm::AllocaInst* ai = llvm::dyn_cast_or_null<llvm::AllocaInst>(v)) {
    EDiag() << "var " << getName() << " was     alloca:\n\t" << str(v) << " :: " << str(v->getType());
    return builder.CreateLoad(ai, /*isVolatile=*/ false, "autoload");
  } else if (v) {
    //EDiag() << "var " << getName() << " was not alloca:\n\t" << str(v) << " :: " << str(v->getType());
    return v;
  }

  pass->valueSymTab.dump(currentOuts());
  ASSERT(false) << "Unknown variable name " << this->name << " in CodegenPass";
  return NULL;
}

/**
// Note: the logical signature of addition on multi-precision ints (Int)
// is (+Int) :: Int -> Int -> Int
// but the C-level signature for mp_int_add is
// mp_result mp_int_add(mp_int, mp_int, mp_int);

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
  else if (op == "*") { return emitRuntimeMPInt_Op(VL, VR, "mp_int_mul"); }

  EDiag() << "\t emitRuntimeArbitraryPrecisionOperation() not yet implemented"
          << " for operation " << op << "!";
  exit(1);
  return NULL;
}
*/

void setFunctionArgumentNames(llvm::Function* F,
              const std::vector<std::string>& argnames) {
  ASSERT(argnames.size() == F->arg_size())
            << "error when codegenning proto " << F->getName()
            << "\n of type " << str(F->getType())
            << "; inArgs.size: " << argnames.size() <<
               "; F.arg_size: " << F->arg_size() << "\n" << str(F);

  Function::arg_iterator AI = F->arg_begin();
  for (size_t i = 0; i != argnames.size(); ++i, ++AI) {
    AI->setName(argnames[i]);
  }
}

llvm::Value* LLAlloc::codegen(CodegenPass* pass) {
  // (alloc base) is equivalent to
  //    let sv = base;
  //        rs  = mallocType t;
  //        r   = rs^;
  //     in sv >^ r;
  //        r
  //    end
  ASSERT(this && this->base && this->base->type);
  llvm::Value* storedVal = this->base->codegen(pass);
  llvm::Value* ptrSlot   = pass->emitMalloc(this->base->type->getLLVMType());
  llvm::Value* ptr       = builder.CreateLoad(ptrSlot, /*isVolatile=*/ false, "");
  builder.CreateStore(storedVal, ptr, /*isVolatile=*/ false);
  return ptr;
}

llvm::Value* LLDeref::codegen(CodegenPass* pass) {
  // base could be an array a[i] or a slot for a reference variable r.
  // a[i] should codegen to &a[i], the address of the slot in the array.
  // r    should codegen to the contents of the slot (the ref pointer value),
  //        not the slot address.
  return builder.CreateLoad(this->base->codegen(pass),
                            /*isVolatile=*/ false,
                            "");
}

llvm::Value* LLStore::codegen(CodegenPass* pass) {
  llvm::Value* vv = this->v->codegen(pass);
  llvm::Value* vr = this->r->codegen(pass);
  ASSERT(isPointerToType(vr->getType(), vv->getType()));
  return builder.CreateStore(vv, vr, /*isVolatile=*/ false);
}

llvm::Value* LLLetVal::codegen(CodegenPass* pass) {
  Value* b = boundexpr->codegen(pass);
  if (!b->getType()->isVoidTy()) {
    b->setName(this->name);
  }

  pass->valueSymTab.insert(this->name, b);
  Value* rv = inexpr->codegen(pass);
  pass->valueSymTab.remove(this->name);
  return rv;
}

llvm::Value* LLClosures::codegen(CodegenPass* pass) {
  // This AST node binds a mutually-recursive set of functions,
  // represented as closure values, in a designated expression.

  ASSERT(closures.size() == 1)
       << "EXPEDIENT HACK: MUTUALLY RECURSIVE CLOSURE CODEGEN"
                << " NOT YET IMPLEMENTED!";

  LLClosure& c = *closures[0];

  llvm::Value* clo = c.codegen(pass);

  pass->valueSymTab.insert(c.varname, clo);

  llvm::Value* exp = expr->codegen(pass);

  for (size_t i = 0; i < closures.size(); ++i) {
     pass->valueSymTab.remove(closures[i]->varname);
  }

  return exp;
}

bool tryBindClosureFunctionTypes(const llvm::Type*          origType,
                                 const llvm::FunctionType*& fnType,
                                 const llvm::StructType*  & envStructTy,
                                 const llvm::StructType*  & cloStructTy) {
  fnType = NULL; envStructTy = NULL; cloStructTy = NULL;

  const llvm::PointerType* pfnty = llvm::dyn_cast<llvm::PointerType>(origType);
  if (!pfnty) {
    EDiag() << "expected " << str(origType) << " to be a ptr type.";
    return false;
  }
  fnType = llvm::dyn_cast<llvm::FunctionType>(pfnty->getContainedType(0));
  if (!fnType) {
    EDiag() << "expected " << str(origType) << " to be a ptr to fn type.";
    return false;
  }
  if (fnType->getNumParams() == 0) {
    EDiag() << "expected " << str(fnType) << " to have an env parameter.";
    return false;
  }
  const llvm::PointerType* maybeEnvType =
                llvm::dyn_cast<llvm::PointerType>(fnType->getParamType(0));
  if (!maybeEnvType) return false;
  envStructTy = llvm::dyn_cast<llvm::StructType>(
                          maybeEnvType->getContainedType(0));
  if (!envStructTy) {
    EDiag() << "expected " << str(fnType) << " to have a concrete struct env parameter.";
    return false;
  }

  cloStructTy = llvm::StructType::get(origType->getContext(),
                    pfnty, maybeEnvType, NULL);
  return true;
}

// Converts { r({...}*, ----), {....}* }
// to       { r( i8*,   ----),   i8*   }.
const llvm::StructType*
genericClosureStructTy(const llvm::FunctionType* fnty) {
  const Type* retty = fnty->getReturnType();
  std::vector<const llvm::Type*> argTypes;
  for (size_t i = 0; i < fnty->getNumParams(); ++i) {
     argTypes.push_back(fnty->getParamType(i));
  }
  argTypes[0] = builder.getInt8PtrTy();

  return llvm::StructType::get(fnty->getContext(),
           ptrTo(FunctionType::get(retty, argTypes, false)),
           builder.getInt8PtrTy(), NULL);
}

llvm::Value*
codegenTupleValues(CodegenPass* pass,
                   std::vector<llvm::Value*> values,
                   CanStackAllocate     canStackAllocate,
                   IsClosureEnvironment isClosureEnvironment);

llvm::Value* LLClosure::codegen(CodegenPass* pass) {
  llvm::Value* proc = pass->lookup(procname);
  ASSERT(proc) << "no proc named " << procname << " when codegenning closure";
  const llvm::FunctionType* fnty;
  const llvm::StructType* envStructTy;
  const llvm::StructType* cloStructTy;

  if (!tryBindClosureFunctionTypes(proc->getType(),
            fnty, envStructTy, cloStructTy)) {
    ASSERT(false) << "proc " << procname
                  << " with type " << str(proc->getType())
                  << " not closed??";
  }

  // { code*, env* }*
  llvm::AllocaInst* clo = CreateEntryAlloca(cloStructTy, varname + ".closure");

  // TODO the (stack reference to the) closure should be marked as
  // a GC root IFF the environment has been dynamically allocated.

  // (code*)*
  Value* clo_code_slot = builder.CreateConstGEP2_32(clo, 0, 0, varname + ".clo_code");
  builder.CreateStore(proc, clo_code_slot, /*isVolatile=*/ false);

  // (env*)*
  Value* clo_env_slot = builder.CreateConstGEP2_32(clo, 0, 1, varname + ".clo_env");


  if (vars.empty()) {
    storeNullPointerToSlot(clo_env_slot);
  } else {
    std::vector<llvm::Value*> values;

    // Ensure that the environment contains space for the type map.
    //const llvm::Type* pi8 = builder.getInt8PtrTy();
    //values.push_back(llvm::ConstantPointerNull::getNullValue(pi8));

    for (size_t i = 0; i < vars.size(); ++i) {
      LLVar v(vars[i]);
      values.push_back(v.codegen(pass));
    }

    bool isClosureEnvironment  = true;
    bool isSafeToStackAllocate = false;
    llvm::Value* envValue = codegenTupleValues(pass, values,
                   CanStackAllocate(isSafeToStackAllocate),
               IsClosureEnvironment(isClosureEnvironment));

    #if 0 // this is broken atm...
      // Store the typemap in the environment's typemap slot.
      llvm::GlobalVariable* clo_env_typemap
          = getTypeMapForType(envStructTy, pass->mod);

      Value* clo_env_typemap_slot =
            builder.CreateConstGEP2_32(envValue, 0, 0,
                                       varname + ".clo_env_typemap_slot");
      llvm::outs() << "clo_env_typemap :: " << clo_env_typemap <<"\n";
      llvm::outs() << "clo_env_typemap :: " << str(clo_env_typemap->getType()) <<"\n";
      llvm::outs() << "clo_env_typemap_slot : " << str(clo_env_typemap_slot->getType()) <<"\n";
      llvm::outs() << "clo_env_typemap_slot*: " << str(clo_env_typemap_slot->getType()->getContainedType(0)) <<"\n";

      Value* clo_env_typemap_cast =
          ConstantExpr::getBitCast(clo_env_typemap,
                                   clo_env_typemap_slot->getType()->getContainedType(0));

      builder.CreateStore(clo_env_typemap_cast,
          clo_env_typemap_slot, /*isVolatile=*/ false);
    #endif

    // Only store the env in the closure if the env contains entries.
    builder.CreateStore(envValue, clo_env_slot, /*isVolatile=*/ false);
  }

  const llvm::StructType* genStructTy = genericClosureStructTy(fnty);
  Value* genericClo = builder.CreateBitCast(clo,
                              ptrTo(genStructTy), varname + ".hideCloTy");
  return builder.CreateLoad(genericClo, /*isVolatile=*/ false, varname + ".loadClosure");
}

//==================================================================

const llvm::FunctionType*
getLLVMFunctionType(FnTypeAST* t) {
  if (const llvm::PointerType* pt =
   dyn_cast<llvm::PointerType>(getLLVMType(t))) {
    return dyn_cast<FunctionType>(pt->getContainedType(0));
  } else {
    return NULL;
  }
}

llvm::Value* LLProc::codegenProto(CodegenPass* pass) {
  std::string symbolName = foster::getGlobalSymbolName(this->name);

  // Give function literals internal linkage, since we know that they can
  // only be referenced from the function in which they are defined.
  llvm::GlobalValue::LinkageTypes functionLinkage =
      (this->name.find("anon_fnlet_") != string::npos)
        ? Function::InternalLinkage
        : Function::ExternalLinkage;

  this->type->markAsProc();
  const llvm::FunctionType* FT = getLLVMFunctionType(this->type);

  if (symbolName == kFosterMain) {
    // No args, returning void...
    FT = llvm::FunctionType::get(builder.getVoidTy(), false);
  }

  ASSERT(FT) << "expecting top-level proc to have FunctionType!";

  Function* F = Function::Create(FT, functionLinkage, symbolName, pass->mod);

  ASSERT(F) << "function creation failed for proto " << this->name;
  ASSERT(F->getName() == symbolName) << "redefinition of function " << symbolName;

  setFunctionArgumentNames(F, this->argnames);

  if (FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(this->type)) {
    F->setCallingConv(fnty->getCallingConventionID());
  }

  this->value = F;
  return F;
}

llvm::Value* LLProc::codegen(CodegenPass* pass) {
  ASSERT(this->getBody() != NULL);
  ASSERT(this->value) << "LLModule should codegen function protos.";

  Function* F = dyn_cast<Function>(this->value);
  ASSERT(F != NULL) << "unable to codegen function " << getName();

  F->setGC("fostergc");

  BasicBlock* prevBB = builder.GetInsertBlock();
  BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "entry", F);
  builder.SetInsertPoint(BB);

  CodegenPass::ValueScope* scope = pass->valueSymTab.newScope(this->getName());

  // If the body of the function might allocate memory, the first thing
  // the function should do is create stack slots/GC roots to hold
  // dynamically-allocated pointer parameters.
  if (true) { // conservative approximation to MightAlloc
    Function::arg_iterator AI = F->arg_begin();
    ASSERT(F->arg_size() == this->argnames.size());
    for (size_t i = 0; i != F->arg_size(); ++i, ++AI) {
      if (mightContainHeapPointers(AI->getType())) {
#if 0
        std::cout << "marking root for var " << this->getProto()->inArgs[i]->name
            << " of ast type " << *(this->getProto()->inArgs[i]->type)
            << " and value type " << *(AI->getType()) << "\n";
#endif
        // Type could be like i32*, like {i32}* or like {i32*}.
        // arg_addr would be i32**,    {i32}**,  or {i32*}*.
        llvm::outs() << "inserting gcparam " <<AI->getNameStr()<< " in scope\n";
        scope->insert(AI->getNameStr(),
                      storeAndMarkPointerAsGCRoot(AI, NotArray, pass->mod));
      } else {
        llvm::AllocaInst* arg_addr = CreateEntryAlloca(
                                                AI->getType(),
                                                AI->getNameStr() + "_addr");
        builder.CreateStore(AI, arg_addr, /*isVolatile*/ false);
        llvm::outs() << "inserting param " <<AI->getNameStr()<< " in scope\n";
        scope->insert(AI->getNameStr(), arg_addr);
      }
    }
  }

  // Enforce that the main function always returns void.
  if (F->getName() == kFosterMain) {
    std::vector<LLVar*> vars;
    this->body = new LLLetVal("!ignored", this->body, new LLTuple(vars));
  }

  Value* rv = this->getBody()->codegen(pass);

  ASSERT(rv) << "null body value when codegenning function " << this->getName();
  const FunctionType* ft = dyn_cast<FunctionType>(F->getType()->getContainedType(0));

  bool fnReturnsUnit = isVoidOrUnit(ft->getReturnType());

  // If we try to return a tuple* when the fn specifies a tuple, manually insert a load
  if (rv->getType()->isDerivedType()
      && !fnReturnsUnit
      && isPointerToType(rv->getType(), ft->getReturnType())) {
    rv = builder.CreateLoad(rv, false, "structPtrToStruct");
  }

  pass->valueSymTab.popExistingScope(scope);

  if (fnReturnsUnit) {
    builder.CreateRetVoid();
  } else if (isVoidOrUnit(rv->getType())) {
    EDiag() << "unable to return non-void value from "
            << getName() << " given only unit";
  } else {
    builder.CreateRet(rv);
  }
  //llvm::verifyFunction(*F);

  // Restore the insertion point, if there was one.
  if (prevBB) {
    builder.SetInsertPoint(prevBB);
  }

  return F;
}

void addAndEmitTo(Function* f, BasicBlock* bb) {
  f->getBasicBlockList().push_back(bb);
  builder.SetInsertPoint(bb);
}

llvm::Value* LLIf::codegen(CodegenPass* pass) {
  //EDiag() << "Codegen for LLIfs should (eventually) be subsumed by CFG building!";
  Value* cond = this->getTestExpr()->codegen(pass);;
  ASSERT(cond != NULL)
        << "codegen for if expr failed due to missing condition";

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then");
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);

  Value* iftmp = CreateEntryAlloca(getLLVMType(this->type), "iftmp_slot");

  Value* then; Value* else_;
  bool elseNeedsLoad = false;
  Function *F = builder.GetInsertBlock()->getParent();

  { // Codegen the then-branch of the if expression
    addAndEmitTo(F, thenBB);
    then = this->getThenExpr()->codegen(pass);
    ASSERT(then != NULL)
        << "codegen for if expr failed due to missing 'then' branch";

    {
      const Type* valTy = getLLVMType(this->type);
      if (valTy != then->getType()) {
        ASSERT(isPointerToType(then->getType(), valTy))
                << "valTy is " << str(valTy)
                << "; actual type of then branch is "
                << str(then->getType());
         // If we have a code construct like
         //   if cond then { new blah {} } else { new blah {} }
         // then the ast type (and thus valType) will be blah*
         // but the exprs will be stack slots of type blah**,
         // requiring a load...
         then = builder.CreateLoad(then, false, "ifthen_rhs");
         elseNeedsLoad = true;
      }
    }

    builder.CreateStore(then, iftmp, /*isVolatile=*/ false);
    builder.CreateBr(mergeBB);
  }

  { // Codegen the else-branch of the if expression
    addAndEmitTo(F, elseBB);
    else_ = this->getElseExpr()->codegen(pass);
    ASSERT(else_ != NULL)
        << "codegen for if expr failed due to missing 'else' branch";

    if (elseNeedsLoad) {
      else_ = builder.CreateLoad(else_, false, "ifelse_rhs");
    }
    builder.CreateStore(else_, iftmp, /*isVolatile=*/ false);
    builder.CreateBr(mergeBB);
  }

  addAndEmitTo(F, mergeBB);
  return builder.CreateLoad(iftmp, /*isVolatile*/ false, "iftmp");
}


llvm::Value* LLUntil::codegen(CodegenPass* pass) {
  //EDiag() << "Codegen for LLUntils should (eventually) be subsumed by CFG building!";

  BasicBlock* testBB = BasicBlock::Create(getGlobalContext(), "until_test");
  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "until_body");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "until_cont");
  Function *F = builder.GetInsertBlock()->getParent();

  builder.CreateBr(testBB);

  addAndEmitTo(F, testBB);
  Value* cond = this->getTestExpr()->codegen(pass);
  ASSERT(cond != NULL) << "codegen for until loop failed due to missing cond";
  builder.CreateCondBr(cond, mergeBB, thenBB);

  { // Codegen the body of the loop
    addAndEmitTo(F, thenBB);
    Value* v = this->getThenExpr()->codegen(pass);
    ASSERT(v != NULL) << "codegen for until loop failed due to missing body";
    builder.CreateBr(testBB);
  }

  addAndEmitTo(F, mergeBB);
  return getUnitValue();
}

llvm::Value* LLCoroPrim::codegen(CodegenPass* pass) {
  const llvm::Type* r = retType->getLLVMType();
  const llvm::Type* a = typeArg->getLLVMType();
  if (this->primName == "coro_yield") { return pass->emitCoroYieldFn(r, a); }
  if (this->primName == "coro_invoke") { return pass->emitCoroInvokeFn(r, a); }
  if (this->primName == "coro_create") { return pass->emitCoroCreateFn(r, a); }
  ASSERT(false); return NULL;
}

llvm::Value* LLCase::codegen(CodegenPass* pass) {
  llvm::Value* v = this->scrutinee->codegen(pass);
  llvm::AllocaInst* rv_slot = CreateEntryAlloca(getLLVMType(this->type), "case_slot");
  this->dt->codegen(pass, v, rv_slot);
  return builder.CreateLoad(rv_slot, /*isVolatile=*/ false, ".case");
}

llvm::Value* lookupOccs(Occurrence* occ, llvm::Value* v) {
  const std::vector<int>& occs = occ->offsets;
  llvm::Value* rv = v;
  for (size_t i = 0; i < occs.size(); ++i) {
    rv = getElementFromComposite(rv,
             getConstantInt32For(occs[i]), "switch_insp");
  }
  return rv;
}

void DecisionTree::codegen(CodegenPass* pass,
                           llvm::Value* scrutinee,
                           llvm::AllocaInst* rv_slot) {
  if (tag == DecisionTree::DT_FAIL) {
    EDiag() << "DecisionTree codegen, tag = DT_FAIL; v = " << str(scrutinee);
    emitFosterAssert(pass->mod, builder.getInt1(false), "pattern match failure!");
    return;
  }

  if (tag == DecisionTree::DT_LEAF) {
    ASSERT(this->action != NULL);
    Value* rv = NULL;

    for (size_t i = 0; i < binds.size(); ++i) {
       Value* v = lookupOccs(binds[i].second, scrutinee);
       if (!v->getType()->isVoidTy()) {
         v->setName("pat_" + binds[i].first);
       }
       pass->valueSymTab.insert(binds[i].first, v);
    }
    rv = this->action->codegen(pass);
    for (size_t i = 0; i < binds.size(); ++i) {
       pass->valueSymTab.remove(binds[i].first);
    }

    ASSERT(rv != NULL);
    builder.CreateStore(rv, rv_slot, /*isVolatile=*/ false);
    return;
  } // end DT_LEAF

  if (tag == DecisionTree::DT_SWAP) {
    ASSERT(false) << "Should not have DT_SWAP nodes at codegen!";
  } // end DT_SWAP

  if (tag == DecisionTree::DT_SWITCH) {
    sc->codegen(pass, scrutinee, rv_slot);
    return;
  }

  EDiag() << "DecisionTree codegen, tag = " << tag << "; v = " << str(scrutinee);
}

void SwitchCase::codegen(CodegenPass* pass,
                         llvm::Value* scrutinee,
                         llvm::AllocaInst* rv_slot) {
  ASSERT(ctors.size() == trees.size());
  ASSERT(ctors.size() >= 1);

  BasicBlock* defaultBB = NULL;
  if (defaultCase != NULL) {
    defaultBB = BasicBlock::Create(getGlobalContext(), "case_default");
  }

  // Special-case codegen for when there's only one
  // possible case, to avoid superfluous branches.
  if (trees.size() == 1 && !defaultCase) {
    trees[0]->codegen(pass, scrutinee, rv_slot);
    return;
  }

  // Fetch the subterm of the scrutinee being inspected.
  llvm::Value* v = lookupOccs(occ, scrutinee);

  // TODO: switching on a.p. integers: possible at all?
  // If so, it will require manual if-else chaining,
  // not a simple int32 switch...

  BasicBlock* bbEnd = BasicBlock::Create(getGlobalContext(), "case_end");
  BasicBlock* defOrContBB = defaultBB ? defaultBB : bbEnd;
  llvm::SwitchInst* si = builder.CreateSwitch(v, defOrContBB, ctors.size());

  Function *F = builder.GetInsertBlock()->getParent();

  for (size_t i = 0; i < ctors.size(); ++i) {
    CtorId c = ctors[i];
    DecisionTree* t = trees[i];

    ConstantInt* onVal = NULL;
    // Compute the "tag" associated with this branch.
    if (c.first == "Int32") {
      onVal = getConstantInt32For(c.second);
    } else if (c.first == "Bool") {
      onVal = builder.getInt1(c.second);
    } else {
      ASSERT(false) << "SwitchCase ctor " << i << "/" << ctors.size()
             << ": " << c.first << "."  << c.second
             << "\n" << str(v)  << "::" << str(v->getType());
    }

    // Emit the code for the branch expression,
    // ending with a branch to the end of the case-expr.
    std::stringstream ss; ss << "casetest_" << i;
    BasicBlock* destBB = BasicBlock::Create(getGlobalContext(), ss.str());
    addAndEmitTo(F, destBB);
    t->codegen(pass, scrutinee, rv_slot);
    builder.CreateBr(bbEnd);

    si->addCase(onVal, destBB);
  }

  if (defaultCase) {
    addAndEmitTo(F, defaultBB);
    defaultCase->codegen(pass, scrutinee, rv_slot);
    builder.CreateBr(bbEnd);
  }

  addAndEmitTo(F, bbEnd);
}

bool isPointerToStruct(const llvm::Type* ty) {
  if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    if (llvm::dyn_cast<llvm::StructType>(pty->getContainedType(0))) {
      return true;
    }
  }
  return false;
}

llvm::Value* tryBindArray(llvm::Value* base) {
  // {i64, [0 x T]}*
  if (isPointerToStruct(base->getType())) {
    const llvm::Type* sty = base->getType()->getContainedType(0);
    if (sty->getNumContainedTypes() == 2
      && sty->getContainedType(0) == builder.getInt64Ty()) {
      if (const llvm::ArrayType* aty =
        llvm::dyn_cast<llvm::ArrayType>(sty->getContainedType(1))) {
        if (aty->getNumElements() == 0) {
          return getPointerToIndex(base, getConstantInt32For(1), "");
        }
      }
    }
  }
  return NULL;
}

llvm::Value* LLSubscript::codegen(CodegenPass* pass) {
  Value* base = this->base->codegen(pass);
  Value* idx  = this->index->codegen(pass);

  ASSERT(base); ASSERT(idx);

  const llvm::Type* baseTy = base->getType();
  if ((getLLVMType(this->type)
       && isPointerToType(baseTy, getLLVMType(this->type)))
      || (baseTy->isPointerTy()
       && baseTy->getContainedType(0)->isPointerTy())) {
    base = builder.CreateLoad(base, /*isVolatile*/ false, "subload");
  }

  if (llvm::Value* arr = tryBindArray(base)) {
    //EDiag() << "arr = " << str(arr) << " :: " << str(arr->getType());
    return getPointerToIndex( arr, idx, "");
  } else {
    return getElementFromComposite(base, idx, "");
  }
}

////////////////////////////////////////////////////////////////////

LLProc* getClosureVersionOf(LLExpr* arg,
                            const llvm::Type* expectedType,
                            FnTypeAST* fnty,
                            CodegenPass* pass);

bool
isKnownNonAllocating(LLVar* varast) {
  // silly hack for now...
  if (pystring::startswith(varast->getName(), "expect_")) return true;
  if (pystring::startswith(varast->getName(), "print_")) return true;
  return false;
}

////////////////////////////////////////////////////////////////////

void doLowLevelWrapperFnCoercions(const llvm::Type* expectedType,
                                  LLExpr*& arg,
                                  CodegenPass* pass) {
  FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(arg->type);
  if (!fnty) return;

  // FnTypeAST could mean a closure or a raw function...
  const llvm::FunctionType* llvmFnTy = getLLVMFunctionType(fnty);

  // Codegenning   callee( arg )  where arg has raw function type, not closure type!
  if (!llvmFnTy) return;

  // If we still have a bare function type at codegen time, it means
  // the code specified a (top-level) procedure name.
  // Since we made it past type checking, we should have only two
  // possibilities for what kind of function is doing the invoking:
  //
  // 1) A C-linkage function which expects a bare function pointer.
  // 2) A Foster function which expects a closure value.

  bool argExpectedFunctionPointer
          = expectedType->isPointerTy()
         && expectedType->getContainedType(0)->isFunctionTy();
  if (argExpectedFunctionPointer) {
    ASSERT(llvmFnTy == expectedType)
        << "calling a function that expects a bare pointer arg:\n\t"
        << str(expectedType) << " -VS- " << str(llvmFnTy);
    // Do we want to codegen to handle automatic insertion
    // of type-coercion wrappers? For now, we'll require
    // strict type compatibility.
  } else {
  // Case 2 (passing an env-less C function to a context expecting a closure)
  // is not so simple, since a closure code pointer must take the
  // environment pointer as its first argument, and presumably the external
  // caller will not be providing an env pointer. Thus we need a pointer
  // to a forwarding procedure, which acts as the opposite of a trampoline:
  // instead of excising one (implicitly-added) parameter,
  // the wrapper adds one (implicitly-ignored) parameter to the signature.
  //
  // The simplest approach is to lazily generate a "closure version" of any
  // functions we see being passed directly by name; it would forward
  // all parameters to the regular function, except for the env ptr.
    LLProc* wrapper = getClosureVersionOf(arg, expectedType, fnty, pass);
    std::string cloname = ParsingContext::freshName("c-clo");
    std::vector<LLClosure*> closures;
    std::vector<std::string> vars;
    closures.push_back(new LLClosure(cloname, wrapper->getName(), vars));
    LLExpr* clo = new LLClosures(new LLVar(cloname), closures);
    arg = clo;
  }
}

////////////////////////////////////////////////////////////////////

// TODO this shouldn't need to be 200 lines :(
llvm::Value* LLCall::codegen(CodegenPass* pass) {
  ASSERT(base != NULL) << "unable to codegen call due to null base";

  Value* FV = base->codegen(pass);
  ASSERT(FV) << "unable to codegen call due to missing value for base";

  const FunctionType* FT = NULL;
  std::vector<Value*> valArgs;

  // TODO extract directly from FnTypeAST
  llvm::CallingConv::ID callingConv = llvm::CallingConv::GHC; // conspicuous
  bool haveSetCallingConv = false;

  if (Function* F = llvm::dyn_cast<Function>(FV)) {
    // Call to top level function
    FT = F->getFunctionType();
    callingConv = F->getCallingConv(); haveSetCallingConv = true;
  } else if (FnTypeAST* closureFnType = dynamic_cast<FnTypeAST*>(base->type)) {
    // If our base has a Foster-level function type but not a
    // LLVM-level function type, it must mean we're calling a closure.
    callingConv = closureFnType->getCallingConventionID(); haveSetCallingConv = true;

    // The function type here includes a parameter for the
    // generic environment type, e.g. (i32 => i32) becomes
    // i32 (i8*, i32).
    FT = dyn_cast<const FunctionType>(
          genericClosureVersionOf(closureFnType)->getLLVMFnType());

    // Load code and env pointers from closure...
    llvm::Value* envPtr =
         getElementFromComposite(FV, getConstantInt32For(1), "getCloEnv");
    FV = getElementFromComposite(FV, getConstantInt32For(0), "getCloCode");

    // Pass env pointer as first parameter to function.
    ASSERT(valArgs.empty());
    valArgs.push_back(envPtr);
  } else {
    ASSERT(false);
  }

  ASSERT(haveSetCallingConv);
  ASSERT(FT) << "call to uncallable something "
             << base->tag << "\t" << base->type->tag
             << "\nFV: " << str(FV);

  for (size_t i = 0; i < this->args.size(); ++i) {
    ASSERT(i < FT->getNumContainedTypes());
    const llvm::Type* expectedType = FT->getContainedType(i);

    LLExpr* arg = this->args[i];
    doLowLevelWrapperFnCoercions(expectedType, arg, pass);
    Value* argV = arg->codegen(pass);
    ASSERT(argV) << "null codegenned value for arg " << (i - 1) << " of call";

    // Is the formal parameter a pass-by-value struct and the provided argument
    // a pointer to the same kind of struct? If so, load the struct into a virtual
    // register in order to pass it to the function...
    const Type* formalType = FT->getParamType(valArgs.size());
    if (llvm::isa<llvm::StructType>(formalType)) {
      if (llvm::PointerType::get(formalType, 0) == argV->getType()) {
        // This is used when passing closures, for example.
        argV = builder.CreateLoad(argV, "loadStructParam");
      }
    }

    valArgs.push_back(argV);
  }

  // Stack slot loads must be done after codegen for all arguments
  // has taken place, in order to ensure that no allocations will occur
  // between the load and the call.
  for (size_t i = 0; i < valArgs.size(); ++i) {
    llvm::Value*& argV = valArgs[i];

    ASSERT(FT->getNumContainedTypes() > (i+1)) << "i = " << i
        << "; FT->getNumContainedTypes() = " << FT->getNumContainedTypes()
        << "; valArgs.size() = " << valArgs.size()
        << "; FT = " << str(FT); // << "::" << show(this) << "\n";

    // ContainedType[0] is the return type; args start at 1
    const llvm::Type* expectedType = FT->getContainedType(i + 1);

    // If we have a T loaded from a T*, and we expect a T*,
    // use the T* (TODO: make sure the T* isn't stack allocated!)
    // LLVM intrinsics and C functions can take pointer-to-X args,
    // but codegen for variables will have already emitted a load
    // from the variable's implicit address.
    if (argV->getType() != expectedType &&
      isPointerToType(expectedType, argV->getType())) {
      if (llvm::LoadInst* load = llvm::dyn_cast<llvm::LoadInst>(argV)) {
        /*EDiag() << "Have a T = " << str(argV->getType())
                << ", expecting a T* = " << str(expectedType);*/
        argV = load->getPointerOperand();
        load->eraseFromParent();
      }
    }

    bool needsAdjusting = argV->getType() != expectedType;
    if (needsAdjusting) {
      TypeAST* argty = this->args[i]->type;
      EDiag() << "\n" << str(argV) << "->getType() is\n" << str(argV->getType())
              << "; expecting " << str(expectedType)
              << "\n\targty is " << argty->tag << "\t" << str(argty);
      ASSERT(false);
    }

    ASSERT(argV->getType() == expectedType)
              << "type mismatch, " << str(argV->getType())
              << " vs expected type " << str(expectedType)
              << "\nbase is " << str(FV)
              << "\nwith base type " << str(FV->getType());
  }

  ASSERT(FT->getNumParams() == valArgs.size())
            << "function arity mismatch, got " << valArgs.size()
            << " args but expected " << FT->getNumParams();

  // Give the instruction a name, if we can...
  llvm::CallInst* callInst = NULL;
  if (FT->getReturnType()->isVoidTy()) {
    callInst = builder.CreateCall(FV, valArgs.begin(), valArgs.end());
  } else {
    callInst = builder.CreateCall(FV, valArgs.begin(), valArgs.end(), "calltmp");
  }

  callInst->setCallingConv(callingConv);
  if (callingConv == llvm::CallingConv::Fast) {
    callInst->setTailCall(true);
  }

  if (isKnownNonAllocating(base)) {
    markAsNonAllocating(callInst);
  }

  llvm::Value* value = callInst;

  // If we have e.g. a function like   mk-tree :: .... -> ref node
  // that returns a pointer, we assume that the pointer refers to
  // heap-allocated memory and must be stored on the stack and marked
  // as a GC root. In order that updates from the GC take effect,
  // we use the stack slot (of type T**) instead of the pointer (T*) itself
  // as the return value of the call.
  if (value->getType()->isPointerTy()) {
    const llvm::Type* retty = value->getType();
    if (retty->getContainedType(0)->isPointerTy()) {
      // have T**; load T* value so it can be stored in a gcroot slot
      value = builder.CreateLoad(value, /*isVolatile=*/ false, "destack");
    }

    value = storeAndMarkPointerAsGCRoot(value, NotArray, pass->mod);
  }

  return value;
}

llvm::Value*
codegenTupleValues(CodegenPass* pass,
                   std::vector<llvm::Value*> values,
                   CanStackAllocate     canStackAllocate,
                   IsClosureEnvironment isClosureEnvironment) {
  if (values.empty()) {
    return getUnitValue(); // It's silly to allocate a unit value!
  }

  std::vector<const llvm::Type*> loweredTypes;
  for (size_t i = 0; i < values.size(); ++i) {
    loweredTypes.push_back(values[i]->getType());
  }
  llvm::StructType* tupleType = llvm::StructType::get(
            llvm::getGlobalContext(), loweredTypes, /*isPacked=*/false);

  llvm::Value* pt = NULL;

  const char* typeName = (isClosureEnvironment.value) ? "env" : "tuple";
  registerType(tupleType, typeName, pass->mod, NotArray, isClosureEnvironment.value);

  // Allocate tuple space
  if (!canStackAllocate.value) {
    pt = pass->emitMalloc(tupleType);
    pt = builder.CreateLoad(pt, "normalize");
  } else {
    pt = CreateEntryAlloca(tupleType, "s");
  }

  // pt has type tuple*

  for (size_t i = 0; i < values.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    builder.CreateStore(values[i], dst, /*isVolatile*/ false);
  }

  return pt;
}

llvm::Value* LLTuple::codegen(CodegenPass* pass) {
  std::vector<llvm::Value*> values;
  for (size_t i = 0; i < parts.size(); ++i) {
    values.push_back(parts[i]->codegen(pass));
  }

  return codegenTupleValues(pass, values,
                            canStackAllocate(this),
            IsClosureEnvironment(this->isClosureEnvironment));
}


// Create function    fnName({}* env, arg-args) { arg(arg-args) }
// that hard-codes call to fn referenced by arg,
// and is suitable for embedding as the code ptr in a closure pair,
// unlike the given function, which doesn't want the env ptr.
LLProc* getClosureVersionOf(LLExpr* arg,
                            const llvm::Type* expectedType,
                            FnTypeAST* fnty,
                            CodegenPass* pass) {
  static std::map<string, LLProc*> sClosureVersions;

  LLVar* var = dynamic_cast<LLVar*>(arg);
  ASSERT(var != NULL) << "getClosureVersionOf() must be given a LLVar";

  string fnName = "__closureVersionOf__" + var->name;
  if (LLProc* exists = sClosureVersions[fnName]) {
    return exists;
  }

  std::vector<std::string>   inArgNames;
  std::vector<TypeAST*> inArgTypes;
  std::vector<TypeAST*> envTypes;
  std::vector<LLVar*> callArgs;

  inArgNames.push_back(ParsingContext::freshName("__ignored_env__"));
  inArgTypes.push_back(RefTypeAST::get(TupleTypeAST::get(envTypes)));

  for (int i = 0; i < fnty->getNumParams(); ++i) {
    LLVar* a = new LLVar(ParsingContext::freshName("_cv_arg"));
    inArgNames.push_back(a->name);
    inArgTypes.push_back(fnty->getParamType(i));
    callArgs.push_back(a);
  }

  // Create a scope for the new function's values.
  CodegenPass::ValueScope* scope = pass->valueSymTab.newScope(fnName);
  // But don't use it for doing codegen outside the proto.
  pass->valueSymTab.popExistingScope(scope);

  FnTypeAST* newfnty = new FnTypeAST(fnty->getReturnType(),
                                     inArgTypes,
                                     fnty->getAnnots());
  newfnty->markAsProc();
  LLExpr* body = new LLCall(var, callArgs);
  LLProc* proc = new LLProc(newfnty, fnName, inArgNames, body);

  // Regular functions get their proto values added when the module
  // starts codegenning, but we need to do it ourselves here.
  proc->codegenProto(pass);
  pass->valueSymTab.insert(proc->getName(), proc->value);
  proc->codegen(pass);

  sClosureVersions[fnName] = proc;

  return proc;
}
