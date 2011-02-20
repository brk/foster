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
    return "foster__main";
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
    pass->valueSymTab.insert(f->getName(), f->getProto()->codegen(pass));
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

llvm::Value* CodegenPass::lookup(const std::string& fullyQualifiedSymbol) {
  llvm::Value* v =  valueSymTab.lookup(fullyQualifiedSymbol);
  if (v) return v;

  // Otherwise, it should be a function name.
  v = mod->getFunction(fullyQualifiedSymbol);

  if (!v) {
    if (fullyQualifiedSymbol == "coro_create_i32_i32") {
      v = emitCoroCreateFn(builder.getInt32Ty(), builder.getInt32Ty());
    } else if (fullyQualifiedSymbol == "coro_create_i32x2_i32") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroCreateFn(builder.getInt32Ty(),
        llvm::StructType::get(mod->getContext(), argTypes));
    } else if (fullyQualifiedSymbol == "coro_create_i32_i32x2") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroCreateFn(
        llvm::StructType::get(mod->getContext(), argTypes),
        builder.getInt32Ty());
    }

      else if (fullyQualifiedSymbol == "coro_invoke_i32_i32") {
      v = emitCoroInvokeFn(builder.getInt32Ty(), builder.getInt32Ty());
    } else if (fullyQualifiedSymbol == "coro_invoke_i32x2_i32") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroInvokeFn(builder.getInt32Ty(),
        llvm::StructType::get(mod->getContext(), argTypes));
    } else if (fullyQualifiedSymbol == "coro_invoke_i32_i32x2") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroInvokeFn(
        llvm::StructType::get(mod->getContext(), argTypes),
        builder.getInt32Ty());
    }

      else if (fullyQualifiedSymbol == "coro_yield_i32_i32") {
      v = emitCoroYieldFn(builder.getInt32Ty(), builder.getInt32Ty());
    } else if (fullyQualifiedSymbol == "coro_yield_i32x2_i32") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroYieldFn(builder.getInt32Ty(),
        llvm::StructType::get(mod->getContext(), argTypes));
    }  else if (fullyQualifiedSymbol == "coro_yield_i32_i32x2") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroYieldFn(
        llvm::StructType::get(mod->getContext(), argTypes),
        builder.getInt32Ty());
    }
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
    return builder.CreateLoad(ai, /*isVolatile=*/ false, "autoload");
  } else {
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

llvm::Value* LLProto::codegen(CodegenPass* pass) {
  std::string symbolName = foster::getGlobalSymbolName(this->name);

  // Give function literals internal linkage, since we know that they can
  // only be referenced from the function in which they are defined.
  llvm::GlobalValue::LinkageTypes functionLinkage =
      (this->name.find("anon_fnlet_") != string::npos)
        ? Function::InternalLinkage
        : Function::ExternalLinkage;

  const llvm::FunctionType* FT = dyn_cast<FunctionType>(getLLVMType(this->type));
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

llvm::Value* LLLetVal::codegen(CodegenPass* pass) {
  llvm::outs() << "llletval " << name << " = "  << boundexpr->tag << " in " << inexpr->tag << "\n";

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

  for (int i = 0; i < closures.size(); ++i) {
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
  for (int i = 0; i < fnty->getNumParams(); ++i) {
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
  llvm::AllocaInst* clo = CreateEntryAlloca(cloStructTy, "closure");

  // TODO the (stack reference to the) closure should be marked as
  // a GC root IFF the environment has been dynamically allocated.

  // (code*)*
  Value* clo_code_slot = builder.CreateConstGEP2_32(clo, 0, 0, "clo_code");
  builder.CreateStore(proc, clo_code_slot, /*isVolatile=*/ false);

  // (env*)*
  Value* clo_env_slot = builder.CreateConstGEP2_32(clo, 0, 1, "clo_env");


  if (vars.empty()) {
    storeNullPointerToSlot(clo_env_slot);
  } else {
    std::vector<llvm::Value*> values;

    // Ensure that the environment contains space for the type map.
    //const llvm::Type* pi8 = builder.getInt8PtrTy();
    //values.push_back(llvm::ConstantPointerNull::getNullValue(pi8));

    for (int i = 0; i < vars.size(); ++i) {
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
                                       "clo_env_typemap_slot");
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

llvm::outs() << "storing " << str(envValue) << "\n\t :: " << str(envValue->getType()) << "\n";
llvm::outs() << "to " << str(clo_env_slot) << "\n\t :: " << str(clo_env_slot->getType()) << "\n";
    // Only store the env in the closure if the env contains entries.
    builder.CreateStore(envValue, clo_env_slot, /*isVolatile=*/ false);
  }

  const llvm::StructType* genStructTy = genericClosureStructTy(fnty);
  Value* genericClo = builder.CreateBitCast(clo,
                              ptrTo(genStructTy), "hideCloTy");
  return builder.CreateLoad(genericClo, /*isVolatile=*/ false, "loadClosure");
}

//==================================================================

llvm::Value* LLProc::codegen(CodegenPass* pass) {
  ASSERT(this->getBody() != NULL);
  ASSERT(this->getProto()->value) << "LLModule should codegen function protos.";

  Function* F = dyn_cast<Function>(this->getProto()->value);
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
    ASSERT(F->arg_size() == this->proto->argnames.size());
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
                      storeAndMarkPointerAsGCRoot(AI, pass->mod));
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

llvm::Value* LLIf::codegen(CodegenPass* pass) {
  //EDiag() << "Codegen for LLIfs should (eventually) be subsumed by CFG building!";
  Value* cond = this->getTestExpr()->codegen(pass);;
  ASSERT(cond != NULL)
        << "codegen for if expr failed due to missing condition";

  Function *F = builder.GetInsertBlock()->getParent();

  BasicBlock* thenBB = BasicBlock::Create(getGlobalContext(), "then", F);
  BasicBlock* elseBB = BasicBlock::Create(getGlobalContext(), "else");
  BasicBlock* mergeBB = BasicBlock::Create(getGlobalContext(), "ifcont");

  builder.CreateCondBr(cond, thenBB, elseBB);

  Value* then; Value* else_;

  { // Codegen the then-branch of the if expression
    builder.SetInsertPoint(thenBB);
    then = this->getThenExpr()->codegen(pass);
    ASSERT(then != NULL)
        << "codegen for if expr failed due to missing 'then' branch";

    builder.CreateBr(mergeBB);
    thenBB = builder.GetInsertBlock();
  }

  { // Codegen the else-branch of the if expression
    F->getBasicBlockList().push_back(elseBB);
    builder.SetInsertPoint(elseBB);
    else_ = this->getElseExpr()->codegen(pass);
    ASSERT(else_ != NULL)
        << "codegen for if expr failed due to missing 'else' branch";

    builder.CreateBr(mergeBB);
    elseBB = builder.GetInsertBlock();
  }

  { // Codegen the PHI node to merge control flow
    const Type* valTy = getLLVMType(this->type);
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
    return PN;
  }
}

llvm::Value* LLTypeApp::codegen(CodegenPass* pass) {
  //EDiag() << "CodegenPass::visit ETypeAppAST\n" << show(this->parts[0])
  // << "\n\tty arg: " << str(this->typeArg);

  if (LLVar* var = dynamic_cast<LLVar*>(base)) {
    const std::string& fullyQualifiedSymbol = var->getName();

    if (fullyQualifiedSymbol == "coro_invoke") {
      if (TupleTypeAST* args = dynamic_cast<TupleTypeAST*>(this->typeArg)) {
        ASSERT(args->getNumContainedTypes() == 2)
          << "expected 2 arg tuple for coro_invoke, got "
          << str(args);
        return pass->emitCoroInvokeFn(
                          args->getContainedType(0)->getLLVMType(),
                          args->getContainedType(1)->getLLVMType());
      }
    }
 /**
  if (!v) {
    if (fullyQualifiedSymbol == "coro_create_i32_i32") {
      v = emitCoroCreateFn(builder.getInt32Ty(), builder.getInt32Ty());
    } else if (fullyQualifiedSymbol == "coro_create_i32x2_i32") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroCreateFn(builder.getInt32Ty(),
        llvm::StructType::get(mod->getContext(), argTypes));
    } else if (fullyQualifiedSymbol == "coro_create_i32_i32x2") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroCreateFn(
        llvm::StructType::get(mod->getContext(), argTypes),
        builder.getInt32Ty());
    }

      else if (fullyQualifiedSymbol == "coro_invoke_i32_i32") {
      v = emitCoroInvokeFn(builder.getInt32Ty(), builder.getInt32Ty());
    } else if (fullyQualifiedSymbol == "coro_invoke_i32x2_i32") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroInvokeFn(builder.getInt32Ty(),
        llvm::StructType::get(mod->getContext(), argTypes));
    } else if (fullyQualifiedSymbol == "coro_invoke_i32_i32x2") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroInvokeFn(
        llvm::StructType::get(mod->getContext(), argTypes),
        builder.getInt32Ty());
    }

      else if (fullyQualifiedSymbol == "coro_yield_i32_i32") {
      v = emitCoroYieldFn(builder.getInt32Ty(), builder.getInt32Ty());
    } else if (fullyQualifiedSymbol == "coro_yield_i32x2_i32") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroYieldFn(builder.getInt32Ty(),
        llvm::StructType::get(mod->getContext(), argTypes));
    }  else if (fullyQualifiedSymbol == "coro_yield_i32_i32x2") {
      std::vector<const Type*> argTypes;
      argTypes.push_back(builder.getInt32Ty());
      argTypes.push_back(builder.getInt32Ty());
      v = emitCoroYieldFn(
        llvm::StructType::get(mod->getContext(), argTypes),
        builder.getInt32Ty());
    }
  }
  **/
  }
  ASSERT(false) << "falling off the end of LLTypeApp::codegen";
}

llvm::Value* LLNil::codegen(CodegenPass* pass) {
  return llvm::ConstantPointerNull::getNullValue(getLLVMType(this->type));
}

llvm::Value* LLSubscript::codegen(CodegenPass* pass) {
  Value* base = this->base->codegen(pass);
  Value* idx  = this->index->codegen(pass);

  ASSERT(base); ASSERT(idx);

  const llvm::Type* baseTy = base->getType();
  if (getLLVMType(this->type) && isPointerToType(baseTy, getLLVMType(this->type))
      || (baseTy->isPointerTy()
       && baseTy->getContainedType(0)->isPointerTy())) {
    base = builder.CreateLoad(base, /*isVolatile*/ false, "subload");
  }

  return getElementFromComposite(base, idx, "");
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

void doLowLevelWrapperFnCoercions(const llvm::Type* expectedType,
                                  LLExpr*& arg,
                                  CodegenPass* pass) {
  FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(arg->type);
  if (!fnty) return;

  // FnTypeAST could mean a closure or a raw function...
  const llvm::FunctionType* llvmFnTy =
        llvm::dyn_cast<const llvm::FunctionType>(fnty->getLLVMType());
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
    // The function type here includes a parameter for the
    // generic environment type, e.g. (i32 => i32) becomes
    // i32 (i8*, i32).
    callingConv = closureFnType->getCallingConventionID(); haveSetCallingConv = true;
    FT = dyn_cast<const FunctionType>(
          genericClosureVersionOf(closureFnType)->getLLVMFnType());
    llvm::Value* clo = getClosureStructValue(FV);

    ASSERT(clo->getType()->isStructTy())
        << "clo value should be a tuple, not a pointer";
    FV = builder.CreateExtractValue(clo, 0, "getCloCode");
    llvm::Value* envPtr = builder.CreateExtractValue(clo, 1, "getCloEnv");

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
    Value* V = arg->codegen(pass);
    ASSERT(V) << "null codegenned value for arg " << (i - 1) << " of call";

    // Is the formal parameter a pass-by-value struct and the provided argument
    // a pointer to the same kind of struct? If so, load the struct into a virtual
    // register in order to pass it to the function...
    const Type* formalType = FT->getParamType(valArgs.size());
    if (llvm::isa<llvm::StructType>(formalType)) {
      if (llvm::PointerType::get(formalType, 0) == V->getType()) {
        // This is used when passing closures, for example.
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

    ASSERT(FT->getNumContainedTypes() > (i+1)) << "i = " << i
        << "; FT->getNumContainedTypes() = " << FT->getNumContainedTypes()
        << "; valArgs.size() = " << valArgs.size()
        << "; FT = " << str(FT); // << "::" << show(this) << "\n";

    // ContainedType[0] is the return type; args start at 1
    const llvm::Type* expectedType = FT->getContainedType(i + 1);

    // If we have a T loaded from a T*, and we expect a T*,
    // use the T* (TODO: make sure the T* isn't stack allocated!)
    if (V->getType() != expectedType &&
      isPointerToType(expectedType, V->getType())) {
      if (llvm::LoadInst* load = llvm::dyn_cast<llvm::LoadInst>(V)) {
        EDiag() << "Have a T = " << str(V->getType())
                << ", expecting a T* = " << str(expectedType);
        V = load->getPointerOperand();
      }
    }

    V = tempHackExtendInt(V, expectedType);
    bool needsAdjusting = V->getType() != expectedType;
    if (needsAdjusting) {
      LLExpr* arg = this->args[i];
      TypeAST* argty = this->args[i]->type;

      EDiag() << str(V) << "->getType() is " << str(V->getType())
              << "; expecting " << str(expectedType)
              << "\n\targty is " << argty->tag << "\t" << str(argty);

      //if (isPointerToType(expectedType, V->getType())) {
      //  EDiag() << "That is: have T, expected T*";
      //}
      //if (isPointerToType(V->getType(), expectedType)) {
      //  EDiag() << "That is: have T*, expected T";
      //}
    }

    // If we're given a clo** when we expect a clo,
    // automatically load the reference from the stack.
    if (isPointerToPointerToType(V->getType(), expectedType)
     && isGenericClosureType(expectedType)) {
      V = getClosureStructValue(V);
    }

    if (needsAdjusting) {
      currentOuts() << str(V) << "->getType() is " << str(V->getType())
          << "; expected type is " << str(expectedType)
          << "; expect clo? " << isGenericClosureType(expectedType) << "\n";
    }

    // LLVM intrinsics and C functions can take pointer-to-X args,
    // but codegen for variables will have already emitted a load
    // from the variable's implicit address.
    // So, if our expected type is pointer-to-our-value-type, and
    // our value is a load, we'll pull the pointer from the load.
    if (expectedType->isPointerTy()) {
      if (expectedType->getContainedType(0) == V->getType()) {
        if (llvm::LoadInst* load = dyn_cast<llvm::LoadInst>(V)) {
          V = load->getPointerOperand();
          load->eraseFromParent();
        }
      }
    }

    if (V->getType() != expectedType) {
      EDiag() << "type mismatch, " << str(V->getType())
              << " vs expected type " << str(expectedType)
              << "\nbase is " << str(FV)
              << "\nwith base type " << str(FV->getType());
    }
  }

  ASSERT(FT->getNumParams() == valArgs.size())
            << "function arity mismatch, got " << valArgs.size()
            << " args but expected " << FT->getNumParams();

  llvm::CallInst* callInst = NULL;
  if (FT->getReturnType()->isVoidTy()) {
    callInst = builder.CreateCall(FV, valArgs.begin(), valArgs.end());
  } else {
    callInst = builder.CreateCall(FV, valArgs.begin(), valArgs.end(), "calltmp");
  }

  callInst->setCallingConv(callingConv);

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

    value = storeAndMarkPointerAsGCRoot(value, pass->mod);
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
  for (int i = 0; i < values.size(); ++i) {
    llvm::outs() << "tuple value " << i << "\t" << str(values[i]) << " :: " << str(values[i]->getType()) << "\n";
    loweredTypes.push_back(values[i]->getType());
  }
  llvm::StructType* tupleType = llvm::StructType::get(
            llvm::getGlobalContext(), loweredTypes, /*isPacked=*/false);

  llvm::Value* pt = NULL;

  const char* typeName = (isClosureEnvironment.value) ? "env" : "tuple";
  registerType(tupleType, typeName, pass->mod, isClosureEnvironment.value);

  // Allocate tuple space
  if (!canStackAllocate.value) {
    pt = pass->emitMalloc(tupleType);
    pt = builder.CreateLoad(pt, "normalize");
  } else {
    pt = CreateEntryAlloca(tupleType, "s");
  }

  // pt has type tuple*

  for (int i = 0; i < values.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(pt, 0, i, "gep");
    builder.CreateStore(values[i], dst, /*isVolatile*/ false);
  }

  return pt;
}

llvm::Value* LLTuple::codegen(CodegenPass* pass) {
  std::vector<llvm::Value*> values;
  for (int i = 0; i < parts.size(); ++i) {
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

  for (size_t i = 0; i < fnty->getNumParams(); ++i) {
    LLVar* a = new LLVar(ParsingContext::freshName("_cv_arg"));
    inArgNames.push_back(a->name);
    inArgTypes.push_back(fnty->getParamType(i));
    callArgs.push_back(a);
  }

  // Create a scope for the new function's values.
  CodegenPass::ValueScope* scope = pass->valueSymTab.newScope(fnName);
  // But don't use it for doing codegen outside the proto.
  pass->valueSymTab.popExistingScope(scope);

  std::string externalCallingConvention = fnty->getCallingConventionName();
  FnTypeAST* newfnty = FnTypeAST::get(fnty->getReturnType(),
                                       inArgTypes,
                                       externalCallingConvention);

  LLProto* proto = new LLProto(newfnty, fnName, inArgNames);
  LLExpr* body = new LLCall(var, callArgs);
  LLProc* proc = new LLProc(proto, body);

  //proto->type = proc->type = genericClosureVersionOf(fnty);
  proto->codegen(pass);
  proc->codegen(pass);

  // Regular functions get their proto values added when the module
  // starts codegenning, but we need to do it ourselves here.
  pass->valueSymTab.insert(proc->getName(), proc->getProto()->value);

  sClosureVersions[fnName] = proc;

  return proc;
}
