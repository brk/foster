// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterTypeAST.h"

#include "passes/FosterLL.h"
#include "passes/CodegenPass-impl.h"

#include "llvm/Attributes.h"
#include "llvm/CallingConv.h"
#include "llvm/LLVMContext.h"
#include "llvm/Intrinsics.h"

#include "llvm/Metadata.h"
//#include "llvm/Analysis/DIBuilder.h"
//#include "llvm/Support/Dwarf.h"

#include <map>
#include <sstream>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::ConstantInt;
using llvm::Value;
using llvm::dyn_cast;

using foster::builder;
using foster::EDiag;

namespace foster {

void codegenLL(LLModule* prog, llvm::Module* mod) {
  CodegenPass cp(mod);
  prog->codegenModule(&cp);
}

void deleteCodegenPass(CodegenPass* cp) { delete cp; }

} // namespace foster


char kFosterMain[] = "foster__main";
int  kUnknownBitsize = 999; // keep in sync with IntSizeBits in Base.hs

// {{{ Internal helper functions
bool tryBindArray(Value* base, Value*& arr, Value*& len);

namespace foster {
  int8_t bogusCtorId(int8_t c) { return c; }
}

namespace {

llvm::Type* getLLVMType(TypeAST* type) {
  ASSERT(type) << "getLLVMType must be given a non-null type!";
  return type->getLLVMType();
}

llvm::Type* slotType(llvm::Value* v) {
  return v->getType()->getContainedType(0);
}

// TODO (eventually) try emitting masks of loaded/stored heap pointers
// to measure performance overhead of high/low tags.

inline
llvm::Value* emitNonVolatileLoad(llvm::Value* v, llvm::Twine name) {
  return builder.CreateLoad(v, false, name);
}

llvm::Value* emitStore(llvm::Value* val,
                       llvm::Value* ptr) {
  if (val->getType()->isVoidTy()) {
    return getUnitValue(); // Can't store a void!
  }

  if (isPointerToType(ptr->getType(), val->getType())) {
    return builder.CreateStore(val, ptr, /*isVolatile=*/ false);
  }

  builder.GetInsertBlock()->getParent()->dump();
  ASSERT(false) << "ELIDING STORE DUE TO MISMATCHED TYPES:\n"
          << "ptr type: " << str(ptr->getType()) << "\n"
          << "val type: " << str(val->getType()) << "\n"
          << "val is  : " << str(val) << "\n"
          << "ptr is  : " << str(ptr);
  return NULL;
}

llvm::Value* emitStoreWithCast(llvm::Value* val,
                               llvm::Value* ptr) {
  if (!isPointerToType(ptr->getType(), val->getType())) {
    return emitStore(builder.CreateBitCast(val, slotType(ptr)), ptr);
  } else {
    return emitStore(val, ptr);
  }
}

std::vector<llvm::Value*>
codegenAll(CodegenPass* pass, const std::vector<LLVar*>& args) {
  std::vector<llvm::Value*> vals;
  for (size_t i = 0; i < args.size(); ++i) {
    vals.push_back(pass->emit(args[i], NULL));
  }
  return vals;
}

void copyValuesToStruct(const std::vector<llvm::Value*>& vals,
                        llvm::Value* tup_ptr) {
  ASSERT(tup_ptr != NULL);
  for (size_t i = 0; i < vals.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(tup_ptr, 0, i, "gep");
    emitStore(vals[i], dst);
  }
}

llvm::Value* emitFakeComment(std::string s) {
  EDiag() << "emitFakeComment: " << s;
  return new llvm::BitCastInst(builder.getInt32(0), builder.getInt32Ty(), s,
                               builder.GetInsertBlock());
}

bool isEnvPtr(llvm::Value* v) {
  return v->getName().startswith(".env");
}

} // }}} namespace

// Implementation of CodegenPass helpers {{{

CodegenPass::CodegenPass(llvm::Module* m) : mod(m) {
  //dib = new DIBuilder(*mod);
}

llvm::Value* CodegenPass::autoload(llvm::Value* v, const char* suffix) {
  if (this->needsImplicitLoad.count(v) == 1) {
    return emitNonVolatileLoad(v, v->getName() + suffix);
  } else return v;
}

// emit() serves as a wrapper around codegen()
// which inserts implicit loads as needed, and also
// verifies that the expected type matches the generated type.
// In most cases, emit() should be used instead of codegen().
llvm::Value* CodegenPass::emit(LLExpr* e, TypeAST* expectedType) {
  ASSERT(e != NULL) << "null expr passed to emit()!";
  llvm::Value* v = e->codegen(this);
  v = autoload(v);

  if (expectedType) {
    llvm::Type* ty = getLLVMType(expectedType);
    if (!typesEq(v->getType(), ty)) {
      ASSERT(false) << "********* expected type " << str(ty)
                           << "; had type " << str(v->getType())
                           << "\n for value " << str(v);
    }
  }
  ASSERT(v != NULL);
  return v;
}

llvm::Function* CodegenPass::lookupFunctionOrDie(const std::string&
                                                         fullyQualifiedSymbol) {
  // Otherwise, it should be a function name.
  llvm::Function* f = mod->getFunction(fullyQualifiedSymbol);

  if (!f) {
   llvm::errs() << "Unable to find function in module named: "
              << fullyQualifiedSymbol << "\n";
   valueSymTab.dump(llvm::errs());
   ASSERT(false) << "unable to find function " << fullyQualifiedSymbol;
  }
  return f;
}

llvm::Value* CodegenPass::emitFosterStringOfCString(Value* cstr, Value* sz) {
  // Text literals in the code are codegenned as calls to the Text.TextFragment
  // constructor. Currently all strings are heap-allocated, even constant
  // literal strings.
  Value* hstr_slot = this->emitArrayMalloc(builder.getInt8Ty(), sz);
  Value* hstr = emitNonVolatileLoad(hstr_slot, "heap_str");

  Value* hstr_bytes; Value* len;
  if (tryBindArray(hstr, /*out*/ hstr_bytes, /*out*/ len)) {
    llvm::CallInst* mcpy = builder.CreateMemCpy(hstr_bytes,
                              cstr, sz, kDefaultHeapAlignment);
    markAsNonAllocating(mcpy);
  } else { ASSERT(false); }

  // TODO null terminate?
  CtorId frag; frag.typeName = "Text";
               frag.ctorName = "TextFragment";
               frag.smallId  = 0; // TODO fix this hack
  std::vector<LLVar*> args;
  LLValueVar v_hstr(hstr_slot); args.push_back(&v_hstr);
  LLValueVar v_sz(sz);          args.push_back(&v_sz);
  LLAppCtor app(frag, args);
  return app.codegen(this);
}


///}}}//////////////////////////////////////////////////////////////

///{{{//////////////////////////////////////////////////////////////
void codegenCoroPrimitives(CodegenPass* pass) {
  for (CodegenPass::LazyCoroPrimInfoMap::iterator
       it  = pass->lazyCoroPrimInfo.begin();
       it != pass->lazyCoroPrimInfo.end();
       ++it) {
    pass->emitLazyCoroPrimInfo( (*it).first.first.first,
                                (*it).second,
                                (*it).first.first.second,
                                (*it).first.second
                              );
  }
}

void registerKnownDataTypes(const std::vector<LLDecl*> datatype_decls,
                            CodegenPass* pass) {
  for (size_t i = 0; i < datatype_decls.size(); ++i) {
     LLDecl* d = datatype_decls[i];
     const std::string& typeName = d->getName();
     DataTypeAST* dt = dynamic_cast<DataTypeAST*>(d->getType());
     pass->isKnownDataType[typeName] = dt;
  }
}
///}}}//////////////////////////////////////////////////////////////

void LLModule::codegenModule(CodegenPass* pass) {
  registerKnownDataTypes(datatype_decls, pass);
  extendWithImplementationSpecificProcs(pass, procs);

  // Ensure that the llvm::Function*s are created for all the function
  // prototypes, so that mutually recursive function references resolve.
  for (size_t i = 0; i < procs.size(); ++i) {
    // Ensure that the value is in the SymbolInfo entry in the symbol table.
    procs[i]->codegenProto(pass);
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegenProc(pass);
  }

  codegenCoroPrimitives(pass);
}

////////////////////////////////////////////////////////////////////
//////////////// LLProc, LLProto ///////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

bool isReturnTypeOK(llvm::Type* ty) {
  return true; // TODO verify not opaque
}

llvm::FunctionType*
getLLVMFunctionType(FnTypeAST* t, const std::string& procSymbol) {
  if (llvm::PointerType* pt =
   dyn_cast<llvm::PointerType>(getLLVMType(t))) {
    ASSERT(isReturnTypeOK(getLLVMType(t->getReturnType())))
        << "Cannot use opaque return type for proc " << procSymbol;
    return dyn_cast<llvm::FunctionType>(pt->getContainedType(0));
  } else {
    return NULL;
  }
}

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

std::string getGlobalSymbolName(const std::string& sourceName) {
  if (sourceName == "main") {
    // libfoster contains a main() symbol that handles
    // initialization and shutdown/cleanup of the runtime,
    // calling this symbol in between.
    return kFosterMain;
  }
  return sourceName;
}

void LLProc::codegenProto(CodegenPass* pass) {
  std::string symbolName = getGlobalSymbolName(this->getCName());

  this->getFnType()->markAsProc();
  llvm::FunctionType* FT = getLLVMFunctionType(this->getFnType(), symbolName);

  llvm::GlobalValue::LinkageTypes linkage = this->getFunctionLinkage();
  if (symbolName == kFosterMain) {
    // No args, returning void...
    FT = llvm::FunctionType::get(builder.getVoidTy(), false);
    linkage = llvm::GlobalValue::ExternalLinkage;
  }

  ASSERT(FT) << "expecting top-level proc to have FunctionType!";
  this->F = Function::Create(FT, linkage, symbolName, pass->mod);
  ASSERT(F) << "function creation failed for proto " << this->getName();
  ASSERT(F->getName() == symbolName) << "redefinition of function " << symbolName;

  setFunctionArgumentNames(F, this->getFunctionArgNames());
  F->setGC("fostergc");
  F->setCallingConv(this->type->getCallingConventionID());
}

////////////////////////////////////////////////////////////////////

llvm::AllocaInst* ensureImplicitStackSlot(llvm::Value* v, CodegenPass* pass) {
  if (llvm::LoadInst* load = dyn_cast<llvm::LoadInst>(v)) {
    llvm::AllocaInst* slot = dyn_cast<llvm::AllocaInst>(load->getOperand(0));
    if (slot && pass->needsImplicitLoad.count(slot) == 1) {
      return slot;
    }
  }

  if (mightContainHeapPointers(v->getType())) {
    return pass->storeAndMarkPointerAsGCRoot(v);
  } else {
    llvm::AllocaInst* slot = stackSlotWithValue(v, "_addr");
    pass->markAsNeedingImplicitLoads(slot);
    return slot;
  }
}

void LLProc::codegenProc(CodegenPass* pass) {
  ASSERT(this->F != NULL) << "LLModule should codegen proto for " << getName();
  ASSERT(F->arg_size() == this->getFunctionArgNames().size());

  pass->occSlots.clear();
  pass->addEntryBB(F);
  CodegenPass::ValueScope* scope = pass->newScope(this->getName());

  // We begin by creating stack slots/GC roots to hold dynamically-allocated
  // pointer parameters. POSSIBLE OPTIMIZATION: This could be elided if we
  // knew that no observable GC could occur in the function's extent.

  for (Function::arg_iterator AI = F->arg_begin();
                              AI != F->arg_end(); ++AI) {
    if (isEnvPtr(AI)) { // Non-envptr args get stack slots from postalloca phis.
      llvm::Value* slot = ensureImplicitStackSlot(AI, pass);
      pass->insertScopedValue(AI->getName(), slot);
    }
  }

  EDiag() << "codegennign blocks for fn " << F->getName();
  this->codegenToFunction(pass, F);
  pass->popExistingScope(scope);
}

///}}}//////////////////////////////////////////////////////////////

void CodegenPass::scheduleBlockCodegen(LLBlock* b) {
  if (worklistBlocks.tryAdd(b->block_id, b)) {
    // added new block
  } // else block was already scheduled
}

void initializeBlockPhis(LLBlock*);

void LLProcCFG::codegenToFunction(CodegenPass* pass, llvm::Function* F) {
  pass->fosterBlocks.clear();

  // Create all the basic blocks before codegenning any of them.
  for (size_t i = 0; i < blocks.size(); ++i) {
    LLBlock* bi = blocks[i];
    pass->fosterBlocks[bi->block_id] = bi;
    bi->bb = BasicBlock::Create(builder.getContext(), bi->block_id, F);
    ASSERT(bi->block_id == bi->bb->getName())
                     << "function can't have two blocks named " << bi->block_id;
  }

  ASSERT(blocks.size() > 0) << F->getName() << " had no blocks!";
  llvm::BasicBlock* savedBB = builder.GetInsertBlock();
  for (size_t i = 0; i < blocks.size(); ++i) {
    initializeBlockPhis(blocks[i]);
  }

  // Make sure we branch from the entry block to the first 'computation' block
  // which will either be a case analysis on the env parameter, or postalloca.
  builder.SetInsertPoint(savedBB);
  LLBr br(blocks[0]->block_id);
  br.codegenTerminator(pass);

  pass->worklistBlocks.clear();
  pass->scheduleBlockCodegen(blocks[0]);
  while (!pass->worklistBlocks.empty()) {
    LLBlock* b = pass->worklistBlocks.get();
    b->codegenBlock(pass);
  }

  // Redundant pattern matches will produce empty basic blocks;
  // here, we clean up any basic blocks we created but never used.
  llvm::Function::iterator BB_it = F->begin();
  while (BB_it != F->end()) {
    llvm::BasicBlock* bb = BB_it; ++BB_it;
    if (bb->empty()) {
      if (bb->use_empty()) {
        bb->eraseFromParent();
      }
    }
  }
}

////////////////////////////////////////////////////////////////////

void initializeBlockPhis(LLBlock* block) {
  builder.SetInsertPoint(block->bb);
  for (size_t i = 0; i < block->phiVars.size(); ++i) {
    block->phiNodes.push_back(
           builder.CreatePHI(getLLVMType(block->phiVars[i]->type),
                        block->numPreds, block->phiVars[i]->getName()));
  }
}

// When there's only one predecessor, we can avoid creating stack
// slots for phis. But doing so means that we must perform CFG simplification
// in order for us not to have stale GC roots persist through phi nodes!
// The GCRootSafetyChecker pass verifies that use of phi nodes is restricted.
bool needStackSlotForPhis(LLBlock* block) {
  ASSERT(block->numPreds > 0);
  return block->numPreds > 1;
}

Value* maybeStackSlotForPhi(Value* phi, LLBlock* block, CodegenPass* pass) {
  Value* rv = phi;
  if (needStackSlotForPhis(block) && phi->getType()->isPointerTy()) {
    rv = ensureImplicitStackSlot(phi, pass);
  }
  return rv;
}

void LLBlock::codegenBlock(CodegenPass* pass) {
  builder.SetInsertPoint(bb);
  if (!this->phiVars.empty()) {
    EDiag() << bb->getName() << " ; " << numPreds << " preds, in " << bb->getParent()->getName()
        << " ;; "<< needStackSlotForPhis(this);
  }
  for (size_t i = 0; i < this->phiVars.size(); ++i) {
     pass->insertScopedValue(this->phiVars[i]->getName(),
        maybeStackSlotForPhi(this->phiNodes[i], this, pass));
  }
  for (size_t i = 0; i < this->mids.size(); ++i) {
    this->mids[i]->codegenMiddle(pass);
  }
  this->terminator->codegenTerminator(pass);
}

////////////////////////////////////////////////////////////////////
////////////////////////// Terminators /////////////////////////////
/////////////////////////////////////////////////////////////////{{{

void LLRetVoid::codegenTerminator(CodegenPass* pass) {
  builder.CreateRetVoid();
}

void LLRetVal::codegenTerminator(CodegenPass* pass) {
  llvm::Value* rv = pass->emit(this->val, NULL);
  bool returnsVoid =              rv->getType()->isVoidTy() ||
         builder.getCurrentFunctionReturnType()->isVoidTy();
  if (returnsVoid) {
    builder.CreateRetVoid();
  } else {
    builder.CreateRet(rv);
  }
}

void passPhisAndBr(LLBlock* block, const std::vector<llvm::Value*>& args) {
  ASSERT(args.size() == block->phiNodes.size())
        << "from " << builder.GetInsertBlock()->getName().str() << " : "
        << "to " << block->bb->getName().str() << " : "
        << "have " << args.size() << " args; "
        << "need " << block->phiNodes.size();
  for (size_t i = 0; i < args.size(); ++i) {
    llvm::Value* v = args[i];
    if (v->getType()->isVoidTy()) {
      v = getUnitValue(); // Can't pass a void value!
    }
    ASSERT(v->getType() == block->phiNodes[i]->getType())
        << "Can't pass a value of type " << str(v->getType())
        << " to a phi node of type " << str(block->phiNodes[i]->getType())
        << "\n from value " << str(v) << " to block " << (block->block_id);
    block->phiNodes[i]->addIncoming(v, builder.GetInsertBlock());
  }
  builder.CreateBr(block->bb);
}

void LLBr::codegenTerminator(CodegenPass* pass) {
  LLBlock* block = pass->lookupBlock(this->block_id);

  if (this->args.empty() && llvm::StringRef(block_id).startswith("postalloca"))
  { // The "first" branch into the postalloca won't pass any actual args, so we
    // want to use the "real" function args (leaving out the invariant env ptr).
    // Other branches to postalloca will pass the new values for the arg slots.
    std::vector<llvm::Value*> args;
    Function* F = builder.GetInsertBlock()->getParent();
    for (Function::arg_iterator AI = F->arg_begin(); AI != F->arg_end(); ++AI) {
      if (!isEnvPtr(AI)) { args.push_back(AI); }
    }
    passPhisAndBr(block, args);
  } else {
    passPhisAndBr(block, codegenAll(pass, this->args));
  }
}

void addAndEmitTo(Function* f, BasicBlock* bb) {
  f->getBasicBlockList().push_back(bb);
  builder.SetInsertPoint(bb);
}

ConstantInt* maybeGetTagForCtorId(DataTypeAST* dt, const CtorId& c) {
  if (dt) {                           return builder.getInt8(c.smallId);
  } else if (c.typeName == "Bool") {  return builder.getInt1(c.smallId);
  } else if (c.typeName == "Int32") { return builder.getInt32(c.smallId);
  } else { return NULL; }
}

llvm::Value* emitCallGetCtorIdOf(CodegenPass* pass, llvm::Value* v) {
  llvm::Value* foster_ctor_id_of = pass->mod->getFunction("foster_ctor_id_of");
  ASSERT(foster_ctor_id_of != NULL);
  llvm::CallInst* call = builder.CreateCall(foster_ctor_id_of,
                         builder.CreateBitCast(v, builder.getInt8PtrTy()));
  markAsNonAllocating(call);
  return call;
}

void LLSwitch::codegenTerminator(CodegenPass* pass) {
  ASSERT(ctors.size() == blockids.size());
  ASSERT(ctors.size() >= 1);

  BasicBlock* defaultBB = (this->defaultCase.empty())
                ? NULL
                : pass->lookupBlock(this->defaultCase)->bb;

  // All the ctors should have the same data type, now that we have at least
  // one ctor, check if it's associated with a data type we know of.
  DataTypeAST* dt = pass->isKnownDataType[ctors[0].typeName];

  BasicBlock* bbNoDefault = defaultBB ? NULL      :
                       BasicBlock::Create(builder.getContext(), "case_nodefault");
  BasicBlock* defOrContBB = defaultBB ? defaultBB : bbNoDefault;

  // Fetch the subterm of the scrutinee being inspected.
  llvm::Value* inspected = pass->emit(this->occ, NULL);

  // If we're looking at a data type, emit code to get the ctor tag,
  // instead of switching on the pointer value directly.
  if (dt) {    inspected = emitCallGetCtorIdOf(pass, inspected); }

  // Switch on the inspected value and add cases for each ctor considered.
  llvm::SwitchInst* si = builder.CreateSwitch(inspected, defOrContBB, ctors.size());
  for (size_t i = 0; i < ctors.size(); ++i) {
    CtorId& c = ctors[i];

    // Compute the tag for the ctor associated with this branch.
    ConstantInt* onVal = maybeGetTagForCtorId(dt, c);
    ASSERT(onVal) << "SwitchCase ctor " << (i+1) << "/" << ctors.size()
           << ": " << c.typeName << "." << c.ctorName << "#" << c.smallId;
    ASSERT(si->getCondition()->getType() == onVal->getType())
        << "switch case and inspected value had different types!";

    BasicBlock* destBB = pass->lookupBlock(this->blockids[i])->bb;
    ASSERT(destBB != NULL);
    si->addCase(onVal, destBB);
  }

  if (bbNoDefault) {
    Function *F = builder.GetInsertBlock()->getParent();
    addAndEmitTo(F, bbNoDefault);
    emitFosterAssert(pass->mod, llvm::ConstantInt::getTrue(builder.getContext()),
                   "control passed to llvm-generated default block -- bad!");
    builder.CreateUnreachable();
  }
}

///}}}//////////////////////////////////////////////////////////////

void LLRebindId::codegenMiddle(CodegenPass* pass) {
  pass->insertScopedValue(from, to->codegen(pass));
}

void LLBitcast::codegenMiddle(CodegenPass* pass) {
  llvm::Value* v = to->codegen(pass);
  llvm::Type* tgt = getLLVMType(to->type);
  if (v->getType() == tgt) { return; }

  // Apply the bitcast to the value or the slot, as appropriate.
  if (pass->needsImplicitLoad.count(v) == 1) {
    llvm::Value* cast_slot = builder.CreateBitCast(v, ptrTo(tgt));
    pass->markAsNeedingImplicitLoads(cast_slot);
    pass->insertScopedValue(from, cast_slot);
  } else {
    pass->insertScopedValue(from, builder.CreateBitCast(v, tgt));
  }
}

////////////////////////////////////////////////////////////////////
//////////////// LLAlloc, LLDeref, LLStore /////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLAlloc::codegen(CodegenPass* pass) {
  // (alloc base rgn) is equivalent to
  //    let rs  = allocate t rgn;
  //        sv = base;
  //        r   = rs^;
  //     in sv >^ r;
  //        r
  //    end
  ASSERT(this && this->baseVar && this->baseVar->type);

  LLAllocate alloc(this->baseVar->type, foster::bogusCtorId(-4),
                      /*unboxed*/ false, NULL, this->region);
  llvm::Value* ptrSlot   = alloc.codegen(pass); // disable implicit autoload
  llvm::Value* storedVal = pass->emit(baseVar, NULL);
  llvm::Value* ptr       = pass->autoload(ptrSlot, "alloc_slot_ptr");
  emitStore(storedVal, ptr);
  return ptrSlot;
}

llvm::Value* LLDeref::codegen(CodegenPass* pass) {
  return emitNonVolatileLoad(pass->emit(base, NULL), "deref");
}

llvm::Value* LLStore::codegen(CodegenPass* pass) {
  llvm::Value* vv = pass->emit(v, NULL);
  llvm::Value* vr = pass->emit(r, NULL);
  return emitStore(vv, vr);
}

///}}}///////////////////////////////////////////////////////////////

llvm::Value* LLCoroPrim::codegen(CodegenPass* pass) {
  llvm::Type* r = retType->getLLVMType();
  llvm::Type* a = typeArg->getLLVMType();
  if (this->primName == "coro_yield") { return pass->emitCoroYieldFn(r, a); }
  if (this->primName == "coro_invoke") { return pass->emitCoroInvokeFn(r, a); }
  if (this->primName == "coro_create") { return pass->emitCoroCreateFn(r, a); }
  ASSERT(false) << "unknown coro prim: " << this->primName;
  return NULL;
}

////////////////////////////////////////////////////////////////////
//////////////// LLLetVals /////////////////////////////////////////
////////////////////////////////////////////////////////////////////

void trySetName(llvm::Value* v, const string& name) {
  if (v->getType()->isVoidTy()) {
    // Can't assign a name to void values in LLVM.
  } else if (isFunctionPointerTy(v->getType())) {
    // Don't want to rename functions!
  } else {
    v->setName(name);
  }
}

void LLLetVals::codegenMiddle(CodegenPass* pass) {
  for (size_t i = 0; i < exprs.size(); ++i) {
    // We use codegen() instead of pass>emit() because emit inserts
    // implict loads, which we want done as late as possible.
    Value* b = exprs[i]->codegen(pass);
    trySetName(b, (b->hasName()
                   && b->getName().startswith("stackref"))
                ? names[i] + "_slot"
                : names[i]);
    //EDiag() << "inserting " << names[i] << " = " << (exprs[i]->tag) << " -> " << str(b);
    pass->insertScopedValue(names[i], b);
  }
}

////////////////////////////////////////////////////////////////////
//////////////// LLInt, LLBool, LLVar///////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLBool::codegen(CodegenPass* pass) {
  return builder.getInt1(this->boolValue);
}

llvm::Value* LLText::codegen(CodegenPass* pass) {
  Value* gstr = builder.CreateGlobalString(this->stringValue);
  size_t size = this->stringValue.size();
  return pass->emitFosterStringOfCString(gstr, builder.getInt32(size));
}

llvm::Value* LLValueVar::codegen(CodegenPass* pass) {
  return pass->autoload(this->val);
}

llvm::Value* LLGlobalSymbol::codegen(CodegenPass* pass) {
  return pass->lookupFunctionOrDie(this->name);
}

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  // The variable for an environment can be looked up multiple times...
  llvm::Value* v = pass->valueSymTab.lookup(getName());
  if (v) return v;
  //return emitFakeComment("fake " + getName());

  pass->valueSymTab.dump(llvm::errs());
  ASSERT(false) << "Unknown variable name " << this->name << " in CodegenPass";
  return NULL;
}

llvm::Value* allocateIntWithWord(CodegenPass* pass, llvm::Value* small) {
  // Small integers may be initialized immediately.
  llvm::Value* mpint = pass->allocateMPInt();

  // Call mp_int_init_value() (ignore rv for now)
  llvm::Value* mp_init_value = pass->lookupFunctionOrDie("mp_int_init_value");
  builder.CreateCall2(mp_init_value, mpint, small);
  return mpint;
}

llvm::Value* LLInt::codegen(CodegenPass* pass) {
  ASSERT(this->type && this->type->getLLVMType());
  llvm::Type* ty = this->type->getLLVMType();

  llvm::Value* small = ConstantInt::get(ty, this->getAPInt());

  // Our type could be an LLVM type, or an arbitrary precision int type.
  if (ty->isIntegerTy()) {
    return small;
  } else if (false) {
    // MP integer constants that do not fit in 64 bits
    // must be initialized from string data.
    ASSERT(false) << "codegen for int values that don't fit"
                  << " in 64 bits not yet implemented";
    return NULL;
  } else {
    return allocateIntWithWord(pass, small);
  }
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

///}}}//////////////////////////////////////////////////////////////
//////////////// LLAllocate ////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

Value* allocateCell(CodegenPass* pass, TypeAST* type, bool unboxed,
                    LLAllocate::MemRegion region, int8_t ctorId) {
  llvm::Type* ty = type->getLLVMType();
  if (unboxed) {
    if (llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
      ty = pty->getContainedType(0);
    }
  }

  switch (region) {
  case LLAllocate::MEM_REGION_STACK:
    return CreateEntryAlloca(ty, "alloc");

  case LLAllocate::MEM_REGION_GLOBAL_HEAP:
    return pass->emitMalloc(ty, ctorId);

  default:
    ASSERT(false); return NULL;
  }
}

Value* allocateArray(CodegenPass* pass, TypeAST* ty,
                     LLAllocate::MemRegion region,
                     Value* arraySize) {
  llvm::Type* elt_ty = getLLVMType(ty);
  ASSERT(region == LLAllocate::MEM_REGION_GLOBAL_HEAP);
  return pass->emitArrayMalloc(elt_ty, arraySize);
}

llvm::Value* LLAllocate::codegen(CodegenPass* pass) {
  if (this->arraySize != NULL) {
    EDiag() << "allocating array, type = " << str(this->type);
    return allocateArray(pass, this->type, this->region,
                         pass->emit(this->arraySize, NULL));
  } else {
    return allocateCell(pass, this->type, this->unboxed,
                        this->region, this->ctorId);
  }
}

///}}}//////////////////////////////////////////////////////////////
//////////////// Arrays ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

void printAddress(CodegenPass* pass, Value* addr) {
  builder.CreateCall(
    pass->mod->getFunction("print_addr"),
    builder.CreateBitCast(addr, builder.getInt8PtrTy()));
}

bool isPointerToStruct(llvm::Type* ty) {
  if (llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    if (llvm::dyn_cast<llvm::StructType>(pty->getContainedType(0))) {
      return true;
    }
  }
  return false;
}

bool tryBindArray(llvm::Value* base, Value*& arr, Value*& len) {
  // {i64, [0 x T]}*
  if (isPointerToStruct(base->getType())) {
    llvm::Type* sty = slotType(base);
    if (sty->getNumContainedTypes() == 2
      && sty->getContainedType(0) == builder.getInt64Ty()) {
      if (llvm::ArrayType* aty =
        llvm::dyn_cast<llvm::ArrayType>(sty->getContainedType(1))) {
        if (aty->getNumElements() == 0) {
          arr = getPointerToIndex(base, builder.getInt32(1), "arr");
          len = getElementFromComposite(base, 0, "len");
          return true;
        }
      }
    }
  }
  return false;
}

Value* getArraySlot(Value* base, Value* idx, CodegenPass* pass) {
  Value* arr = NULL; Value* len;
  if (tryBindArray(base, arr, len)) {
    emitFosterAssert(pass->mod,
      builder.CreateICmpULT(
                builder.CreateSExt(idx, len->getType()),
                len, "boundscheck"),
      "array index out of bounds!");
    return getPointerToIndex(arr, idx, "arr_slot");
  } else {
    ASSERT(false) << "expected array, got " << str(base);
    return NULL;
  }
}

llvm::Value* LLArrayRead::codegen(CodegenPass* pass) {
  Value* base = pass->emit(this->base , NULL);
  Value* idx  = pass->emit(this->index, NULL);
  Value* slot = getArraySlot(base, idx, pass);
  Value* val  = emitNonVolatileLoad(slot, "arrayslot");
  return ensureImplicitStackSlot(val, pass);
}

  // base could be an array a[i] or a slot for a reference variable r.
  // a[i] should codegen to &a[i], the address of the slot in the array.
  // r    should codegen to the contents of the slot (the ref pointer value),
  //        not the slot address.

llvm::Value* LLArrayPoke::codegen(CodegenPass* pass) {
  Value* val  = pass->emit(this->value, NULL);
  Value* base = pass->emit(this->base , NULL);
  Value* idx  = pass->emit(this->index, NULL);
  Value* slot = getArraySlot(base, idx, pass);
  return builder.CreateStore(val, slot, /*isVolatile=*/ false);
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLTuple ///////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLTuple::codegenStorage(CodegenPass* pass) {
  if (vars.empty()) { return getUnitValue(); }

  ASSERT(this->allocator);
  TupleTypeAST* tuplety = dynamic_cast<TupleTypeAST*>(this->allocator->type);

  ASSERT(tuplety != NULL)
        << "allocator wants to emit type " << str(this->allocator->type)
        << "; var 0 :: " << str(vars[0]->type);

  registerTupleType(tuplety, this->typeName, foster::bogusCtorId(-2), pass->mod);

  return allocator->codegen(pass);
}

llvm::Value* LLTuple::codegen(CodegenPass* pass) {
  if (vars.empty()) { return getUnitValue(); }

  llvm::Value* slot = codegenStorage(pass);

  // Heap-allocated things codegen to a stack slot, which
  // is the Value we want the overall tuple to codegen as, but
  // we need temporary access to the pointer stored in the slot.
  // Otherwise, bad things happen.
  llvm::Value* pt = allocator->isStackAllocated()
           ? slot
           : emitNonVolatileLoad(slot, "normalize");
  codegenTo(pass, pt);
  return slot;
}

void LLTuple::codegenTo(CodegenPass* pass, llvm::Value* tup_ptr) {
  copyValuesToStruct(codegenAll(pass, this->vars), tup_ptr);
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLClosures ////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

  void LLClosures::codegenMiddle(CodegenPass* pass) {
    // This AST node binds a mutually-recursive set of functions,
    // represented as closure values.

    std::vector<llvm::Value*> envSlots;
    for (size_t i = 0; i < closures.size(); ++i) {
      envSlots.push_back(closures[i]->env->codegenStorage(pass));
    }

    // Allocate storage for the closures and populate 'em with code/env values.
    for (size_t i = 0; i < closures.size(); ++i) {
      llvm::Value* clo = closures[i]->codegenClosure(pass, envSlots[i]);
      pass->insertScopedValue(closures[i]->varname, clo);
    }

    // Stick each closure environment in the symbol table.
    std::vector<llvm::Value*> envPtrs;
    for (size_t i = 0; i < closures.size(); ++i) {
      // Make sure we close over generic versions of our pointers...
      llvm::Value* envPtr = pass->autoload(envSlots[i]);
      llvm::Value* genPtr = builder.CreateBitCast(envPtr,
                                  builder.getInt8PtrTy(),
                                  closures[i]->envname + ".generic");
      pass->insertScopedValue(closures[i]->envname, genPtr);

      envPtrs.push_back(envPtr);
    }

    // Now that all the env pointers are in scope,
    // store the appropriate values through each pointer.
    for (size_t i = 0; i < closures.size(); ++i) {
      closures[i]->env->codegenTo(pass, envPtrs[i]);
    }

    // And clean up env names.
    for (size_t i = 0; i < closures.size(); ++i) {
      pass->valueSymTab.remove(closures[i]->envname);
    }
  }

  bool tryBindClosureFunctionTypes(llvm::Type*          origType,
                                   llvm::FunctionType*& fnType,
                                   llvm::StructType*  & cloStructTy) {
    fnType = NULL; cloStructTy = NULL;

    llvm::PointerType* pfnty = llvm::dyn_cast<llvm::PointerType>(origType);
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
    llvm::PointerType* maybeEnvType =
                  llvm::dyn_cast<llvm::PointerType>(fnType->getParamType(0));
    if (!maybeEnvType) return false;

    cloStructTy = getStructType(pfnty, maybeEnvType);
    return true;
  }

  // Converts { r({...}*, ----), {....}* }
  // to       { r( i8*,   ----),   i8*   }.
  // Used when choosing a type to allocate for a closure pair.
  llvm::StructType*
  genericClosureStructTy(llvm::FunctionType* fnty) {
    Type* retty = fnty->getReturnType();
    std::vector<llvm::Type*> argTypes;
    for (size_t i = 0; i < fnty->getNumParams(); ++i) {
       argTypes.push_back(fnty->getParamType(i));
    }
    argTypes[0] = builder.getInt8PtrTy();

    return getStructType(ptrTo(llvm::FunctionType::get(retty, argTypes, false)),
                         builder.getInt8PtrTy());
  }

  llvm::Value* LLClosure::codegenClosure(
                          CodegenPass* pass,
                          llvm::Value* envPtrOrSlot) {
    llvm::Value* proc = pass->lookupFunctionOrDie(procname);

    llvm::FunctionType* fnty;
    llvm::StructType* cloStructTy;

    if (!tryBindClosureFunctionTypes(proc->getType(), fnty, cloStructTy)) {
      ASSERT(false) << "proc " << procname
                    << " with type " << str(proc->getType())
                    << " not closed??";
    }

    llvm::Value* clo = NULL; llvm::Value* rv = NULL;
    bool closureEscapes = true;
    if (closureEscapes) {
      // // { code*, env* }**
      llvm::AllocaInst* clo_slot = pass->emitMalloc(genericClosureStructTy(fnty),
                                                    foster::bogusCtorId(-5));
      clo = emitNonVolatileLoad(clo_slot, varname + ".closure"); rv = clo_slot;
    } else { // { code*, env* }*
      clo = CreateEntryAlloca(cloStructTy, varname + ".closure"); rv = clo;
    }

    // TODO register closure type

    emitStoreWithCast(proc,
                    builder.CreateConstGEP2_32(clo, 0, 0, varname + ".clo_code"));
    Value* env_slot = builder.CreateConstGEP2_32(clo, 0, 1, varname + ".clo_env");
    if (env->vars.empty()) {
      storeNullPointerToSlot(env_slot);
    } else {
      // Only store the env in the closure if the env contains entries.
      llvm::Value* envPtr = pass->autoload(envPtrOrSlot);
      emitStoreWithCast(envPtr, env_slot);
    }

    return rv;
  }

///}}}//////////////////////////////////////////////////////////////

TupleTypeAST* getDataCtorType(DataCtor* dc) {
  return TupleTypeAST::get(dc->types);
}

////////////////////////////////////////////////////////////////////
//////////////// Decision Trees ////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

TupleTypeAST* maybeGetCtorStructType(CodegenPass* pass, CtorId c) {
  DataTypeAST* dt = pass->isKnownDataType[c.typeName];
  return (dt) ? getDataCtorType(dt->getCtor(c.smallId)) : NULL;
}

// Create at most one stack slot per subterm.
llvm::AllocaInst*
getStackSlotForOcc(CodegenPass* pass, llvm::Value* v, llvm::AllocaInst*& slot) {
  ASSERT(v != NULL);
  if (slot) {
    emitStore(v, slot);
  } else {
    slot = ensureImplicitStackSlot(v, pass);
  }
  return slot;
}

// Returns an implicit stack slot.
llvm::Value* LLOccurrence::codegen(CodegenPass* pass) {
  ASSERT(ctors.size() == offsets.size());

    std::stringstream ss; ss << "occ(";
    for (size_t i = 0; i < offsets.size(); ++i) {
      ss << offsets[i] << ":";
      ss << ctors[i].ctorName << "::";
    }
    ss << ")--";

    emitFakeComment(ss.str());


  llvm::Value* v  = this->var->codegen(pass);
  if (offsets.empty()) return v;

  llvm::Value* rv = pass->autoload(v);
  for (size_t i = 0; i < offsets.size(); ++i) {
    // If we know that the subterm at this position was created with
    // a particular data constructor, emit a cast to that ctor's type.
    if (TupleTypeAST* tupty = maybeGetCtorStructType(pass, ctors[i])) {
      rv = builder.CreateBitCast(rv, tupty->getLLVMType());
    }

    rv = getElementFromComposite(rv, offsets[i], "switch_insp");
  }

  // If we've loaded some possible-pointers from memory, make sure they
  // get their own implicit stack slots.
  llvm::AllocaInst*& slot = pass->occSlots[this];
  getStackSlotForOcc(pass, rv, slot);
  trySetName(slot, "pat_" + this->var->getName() + "_slot");
  return slot;
}

///}}}//////////////////////////////////////////////////////////////

llvm::Value* LLAppCtor::codegen(CodegenPass* pass) {
  DataTypeAST* dt = pass->isKnownDataType[this->ctorId.typeName];
  ASSERT(dt) << "unable to find data type for " << this->ctorId.typeName;
  DataCtor* dc = dt->getCtor(this->ctorId.smallId);
  TupleTypeAST* ty = getDataCtorType(dc);

  // This basically duplicates LLTuple::codegen and should eventually
  // be properly implemented in terms of it.
  registerTupleType(ty, this->ctorId.typeName + "." + this->ctorId.ctorName,
                    this->ctorId.smallId, pass->mod);
  bool yesUnboxed = true;
  LLAllocate a(ty, this->ctorId.smallId, yesUnboxed, NULL,
               LLAllocate::MEM_REGION_GLOBAL_HEAP);
  llvm::Value* obj_slot = a.codegen(pass);
  llvm::Value* obj = emitNonVolatileLoad(obj_slot, "obj");

  copyValuesToStruct(codegenAll(pass, this->args), obj);

  llvm::Type* dtype = dt->getLLVMType();
  // TODO fix to use a stack slot properly
  return builder.CreateBitCast(obj, dtype);
}

////////////////////////////////////////////////////////////////////
//////////////// Term Application //////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLCallPrimOp::codegen(CodegenPass* pass) {
  return codegenPrimitiveOperation(this->op, builder, codegenAll(pass, this->args));
}

bool isGenericClosureEnvType(Type* ty) {
  return ty == builder.getInt8PtrTy();
}

// Returns null if no bitcast is needed, else returns the type to bitcast to.
bool isPointerToUnknown(Type* ty) {
  if (llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    return pty->getContainedType(0)->isIntegerTy(kUnknownBitsize);
  }
  return false;
}

bool matchesExceptForUnknownPointers(Type* aty, Type* ety) {
  //EDiag() << "matchesExceptForUnknownPointers ? " << str(aty) << " =?= " << str(ety);
  if (aty == ety) return true;
  if (aty->isPointerTy() && ety->isPointerTy()) {
    if (isPointerToUnknown(ety)) { return true; }
    return matchesExceptForUnknownPointers(aty->getContainedType(0),
                                           ety->getContainedType(0));
  }
  if (aty->getTypeID() != ety->getTypeID()) return false;

  if (aty->isIntegerTy() && ety->isIntegerTy()) {
    return llvm::cast<llvm::IntegerType>(aty)->getBitWidth()
        == llvm::cast<llvm::IntegerType>(ety)->getBitWidth();
  }
  // TODO vector types? metadata? floating point?
  if (aty->getNumContainedTypes() != ety->getNumContainedTypes()) return false;
  for (size_t i = 0; i < aty->getNumContainedTypes(); ++i) {
    if (! matchesExceptForUnknownPointers(aty->getContainedType(i),
                                          ety->getContainedType(i))) return false;
  }
  return true;
}

llvm::Value* LLCall::codegen(CodegenPass* pass) {
  ASSERT(base != NULL) << "unable to codegen call due to null base";

  Value* FV = pass->emit(base, NULL);
  ASSERT(FV) << "unable to codegen call due to missing value for base";

  llvm::FunctionType* FT = NULL;
  std::vector<Value*> valArgs;

  // TODO extract directly from FnTypeAST
  llvm::CallingConv::ID callingConv = llvm::CallingConv::GHC; // conspicuous
  bool haveSetCallingConv = false;

  if (Function* F = llvm::dyn_cast<Function>(FV)) {
    // Call to top level function
    FT = F->getFunctionType();
    callingConv = F->getCallingConv(); haveSetCallingConv = true;
  } else if (FnTypeAST* fnType = dynamic_cast<FnTypeAST*>(base->type)) {
    callingConv = fnType->getCallingConventionID(); haveSetCallingConv = true;
    if (fnType->isMarkedAsClosure()) {
      // Load code and env pointers from closure...
      llvm::Value* envPtr =
           getElementFromComposite(FV, 1, "getCloEnv");
      FV = getElementFromComposite(FV, 0, "getCloCode");

      FT = dyn_cast<llvm::FunctionType>(FV->getType()->getContainedType(0));
      // Pass env pointer as first parameter to function.
      ASSERT(valArgs.empty());
      valArgs.push_back(envPtr);
    } else {
      FT = fnType->getLLVMFnType();
    }
  } else {
    ASSERT(false) << "expected either direct llvm::Function value or else "
                  << "something of FnType; had " << (base->tag)
                  << " of type " << str(base->type);
  }

  ASSERT(haveSetCallingConv);
  ASSERT(FT) << "call to uncallable something "
             << base->tag << "\t" << base->type->tag
             << "\nFV: " << str(FV);

  // Collect the args, performing coercions if necessary.
  for (size_t i = 0; i < this->args.size(); ++i) {
    llvm::Type* expectedType = FT->getParamType(valArgs.size());

    llvm::Value* argV = pass->emit(this->args[i], NULL);

    // This is a an artifact produced by the mutual recursion
    // of the environments of mutually recursive closures.
    if (isGenericClosureEnvType(argV->getType())
      && argV->getType() != expectedType) {
      EDiag() << "emitting bitcast gen2spec " << str(expectedType);
      argV = builder.CreateBitCast(argV, expectedType, "gen2spec");
    }

    if ((argV->getType() != expectedType)
        && matchesExceptForUnknownPointers(argV->getType(), expectedType)) {
      EDiag() << "matched " << str(argV->getType()) << " to " << str(expectedType);
      argV = builder.CreateBitCast(argV, expectedType, "spec2gen");
    }

    valArgs.push_back(argV);

    ASSERT(argV->getType() == expectedType)
              << "type mismatch, " << str(argV->getType())
              << " vs expected type " << str(expectedType)
              << "\nbase is " << str(FV)
              << "\nwith base type " << str(FV->getType())
              << "\nargV = " << str(argV);
  }

  ASSERT(FT->getNumParams() == valArgs.size())
            << "function arity mismatch for " << FV->getName()
            << "; got " << valArgs.size()
            << " args but expected " << FT->getNumParams();

  // Give the instruction a name, if we can...

  llvm::CallInst* callInst = builder.CreateCall(FV, llvm::makeArrayRef(valArgs));
  callInst->setCallingConv(callingConv);
  trySetName(callInst, "calltmp");

  if (callingConv == llvm::CallingConv::Fast) {
    // In order to mark this call as a tail call, we must know that
    // none of the args being passed are pointers into this stack frame.
    // Because we don't do this analysis, we don't enable TCO for now.
    //callInst->setTailCall(true);
  }

  if (!this->callMightTriggerGC) {
    markAsNonAllocating(callInst);
  }

  // If we have e.g. a function like   mk-tree :: .... -> ref node
  // that returns a pointer, we assume that the pointer refers to
  // heap-allocated memory and must be stored on the stack and marked
  // as a GC root. In order that updates from the GC take effect,
  // we use the stack slot (of type T**) instead of the pointer (T*) itself
  // as the return value of the call.
  if ( callingConv == llvm::CallingConv::Fast
    && callInst->getType()->isPointerTy()) {
    // As a sanity check, we shouldn't ever get a pointer-to-pointer,
    // at least not from Foster code...
    ASSERT(!slotType(callInst)->isPointerTy());

    return pass->storeAndMarkPointerAsGCRoot(callInst);
  } else {
    return callInst;
  }
}

/// }}}
