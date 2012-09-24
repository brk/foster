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
#include <fstream>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::ConstantInt;
using llvm::Value;
using llvm::dyn_cast;

using foster::builder;
using foster::EDiag;

using std::vector;

namespace foster {

void codegenLL(LLModule* prog, llvm::Module* mod, CodegenPassConfig config) {
  CodegenPass cp(mod, config);
  prog->codegenModule(&cp);
}

void deleteCodegenPass(CodegenPass* cp) { delete cp; }

} // namespace foster


char kFosterMain[] = "foster__main";
int  kUnknownBitsize = 999; // keep in sync with IntSizeBits in Base.hs

// {{{ Internal helper functions
bool tryBindArray(Value* base, Value*& arr, Value*& len);

namespace {

llvm::Type* getLLVMType(TypeAST* type) {
  ASSERT(type) << "getLLVMType must be given a non-null type!";
  return type->getLLVMType();
}

llvm::Type* slotType(llvm::Type* t) { return t->getContainedType(0); }
llvm::Type* slotType(llvm::Value* v) { return slotType(v->getType()); }

bool isLargishStructPointerTy(llvm::Type* ty) {
  if (llvm::PointerType* pt = llvm::dyn_cast<llvm::PointerType>(ty)) {
    if (llvm::StructType* st = llvm::dyn_cast<llvm::StructType>(pt->getElementType())) {
      return st->getNumElements() >= 2;
    }
  }
  return false;
}

llvm::Value* emitBitcast(llvm::Value* v, llvm::Type* dstTy, llvm::StringRef msg = "") {
  llvm::Type* srcTy = v->getType();
  if (isFunctionPointerTy(srcTy) && isLargishStructPointerTy(dstTy)) {
    ASSERT(false) << "cannot cast " << str(srcTy) << " to " << str(dstTy) << "\n" << str(v);
  }
  if (dstTy->isPointerTy() != srcTy->isPointerTy()) {
    builder.GetInsertBlock()->getParent()->dump();
    ASSERT(false) << "cannot cast non-pointer " << str(srcTy) << " to " << str(dstTy) << "\n" << str(v);
  }
  return builder.CreateBitCast(v, dstTy, msg);
}

// TODO (eventually) try emitting masks of loaded/stored heap pointers
// to measure performance overhead of high/low tags.

inline llvm::Value* emitNonVolatileLoad(llvm::Value* v, llvm::Twine name) {
  return builder.CreateLoad(v, false, name);
}

llvm::Value* emitStore(llvm::Value* val,
                       llvm::Value* ptr) {
  ASSERT(!val->getType()->isVoidTy());
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

std::vector<llvm::Value*>
codegenAll(CodegenPass* pass, const std::vector<LLVar*>& args) {
  std::vector<llvm::Value*> vals;
  for (size_t i = 0; i < args.size(); ++i) {
    vals.push_back(args[i]->codegen(pass));
  }
  return vals;
}

bool isPointerToStruct(llvm::Type* ty) {
  return ty->isPointerTy() && llvm::isa<llvm::StructType>(slotType(ty));
}

llvm::Value* emitFakeComment(std::string s) {
  return new llvm::BitCastInst(builder.getInt32(0), builder.getInt32Ty(), s,
                               builder.GetInsertBlock());
}

bool isEnvPtr(llvm::Value* v) {
  return v->getName().startswith(".env");
}


////////////////////////////////////////////////////////////////////
//////////////////// Out-Of-Line Assertions ////////////////////////
/////////////////////////////////////////////////////////////////{{{

void assertRightNumberOfArgnamesForFunction(llvm::Function* F,
                                   const std::vector<std::string>& argnames) {
  ASSERT(argnames.size() == F->arg_size())
            << "error when codegenning proto " << F->getName()
            << "\n of type " << str(F->getType())
            << "; inArgs.size: " << argnames.size()
            << "; F.arg_size: " << F->arg_size() << "\n" << str(F);
}

void assertRightNumberOfArgsForFunction(llvm::Value* FV,
           llvm::FunctionType* FT, const std::vector<llvm::Value*>& valArgs) {
  ASSERT(FT->getNumParams() == valArgs.size())
            << "function arity mismatch for " << FV->getName()
            << "; got " << valArgs.size()
            << " args but expected " << FT->getNumParams();
}

void assertValueHasExpectedType(llvm::Value* argV, llvm::Type* expectedType,
                                llvm::Value* FV) {
    ASSERT(typesEq(argV->getType(), expectedType))
              << "type mismatch, " << str(argV->getType())
              << " vs expected type " << str(expectedType)
              << "\nbase is " << str(FV)
              << "\nwith base type " << str(FV->getType())
              << "\nargV = " << str(argV);
}

void assertValueHasExpectedType(llvm::Value* v, TypeAST* expectedType) {
  ASSERT(v);
  if (expectedType) {
    llvm::Type* ty = getLLVMType(expectedType);
    if (!typesEq(v->getType(), ty)) {
      ASSERT(false) << "********* expected type " << str(ty)
                           << "; had type " << str(v->getType())
                           << "\n for value " << str(v);
    }
  }
}

void assertHaveCallableType(LLExpr* base, llvm::Type* FT, llvm::Value* FV) {
  ASSERT(FT) << "call to uncallable something "
             << base->tag << "\t" << base->type->tag
             << " of type " << str(base->type)
             << "\nFV: " << str(FV);
}

void assertHaveFunctionNamed(llvm::Function* f,
                             const std::string& fullyQualifiedSymbol,
                             CodegenPass* pass) {
  if (!f) {
   llvm::errs() << "Unable to find function in module named: "
                << fullyQualifiedSymbol << "\n";
   pass->valueSymTab.dump(llvm::errs());
   ASSERT(false) << "unable to find function " << fullyQualifiedSymbol;
  }
}

void assertCurrentFunctionReturnsUnitType() {
  ASSERT(getUnitValue()->getType() == builder.getCurrentFunctionReturnType())
     << "\n\tunit: " << str(getUnitValue()->getType())
     << "\n\tret: " << str(builder.getCurrentFunctionReturnType());
}

void assertHaveSameNumberOfArgsAndPhiNodes(const vector<llvm::Value*>& args,
                                           LLBlock* block) {
  ASSERT(args.size() == block->phiNodes.size())
        << "from " << builder.GetInsertBlock()->getName().str() << " : "
        << "to " << block->bb->getName().str() << " : "
        << "have " << args.size() << " args; "
        << "need " << block->phiNodes.size();
}

void assertValueHasSameTypeAsPhiNode(llvm::Value* v, LLBlock* block, int i) {
  ASSERT(v->getType() == block->phiNodes[i]->getType())
      << "Can't pass a value of type " << str(v->getType())
      << " to a phi node of type " << str(block->phiNodes[i]->getType())
      << "\n from value " << str(v) << " to block " << (block->block_id);
}

/// }}}

} // }}} namespace

// Implementation of CodegenPass helpers {{{

CodegenPass::CodegenPass(llvm::Module* m, CodegenPassConfig config)
                                                      : config(config), mod(m) {
  //dib = new DIBuilder(*mod);
}

llvm::Value* emitLoad(llvm::Value* v, llvm::StringRef suffix) {
  return emitNonVolatileLoad(v, v->getName() + suffix);
}

llvm::Function* CodegenPass::lookupFunctionOrDie(const std::string&
                                                       fullyQualifiedSymbol) {
  llvm::Function* f = mod->getFunction(fullyQualifiedSymbol);
  assertHaveFunctionNamed(f, fullyQualifiedSymbol, this);
  return f;
}

llvm::Value* CodegenPass::emitFosterStringOfCString(Value* cstr, Value* sz) {
  // Text literals in the code are codegenned as calls to the
  // Text.TextFragment constructor. Currently all strings are heap-allocated,
  // even constant literal strings.
  bool init = false; // because we'll immediately memcpy.
  Value* hstr = this->emitArrayMalloc(TypeAST::i(8), sz, init);
  // This variable is dead after being passed to the TextFragment function,
  // so it does not need a GC root.

  Value* hstr_bytes; Value* len;
  if (tryBindArray(hstr, /*out*/ hstr_bytes, /*out*/ len)) {
    markAsNonAllocating(builder.CreateMemCpy(hstr_bytes,
                              cstr, sz, /*alignment*/ 4));
  } else { ASSERT(false); }

  // TODO null terminate?

  llvm::Function* textfragment = lookupFunctionOrDie("TextFragment");
  llvm::CallInst* call = builder.CreateCall2(textfragment, hstr, sz);
  call->setCallingConv(llvm::CallingConv::Fast);
  return call;
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
     pass->dataTypeTagReprs[typeName] = CTR_OutOfLine;
  }
}

void createGCMapsSymbolIfNeeded(CodegenPass* pass) {
  if (!pass->config.useGC) {
    // The runtime needs a "foster__gcmaps" symbol for linking to succeed.
    // If we're not letting the GC plugin run, we'll need to emit it ourselves.
    new llvm::GlobalVariable(
    /*Module=*/      *(pass->mod),
    /*Type=*/        builder.getInt32Ty(),
    /*isConstant=*/  true,
    /*Linkage=*/     llvm::GlobalValue::ExternalLinkage,
    /*Initializer=*/ llvm::ConstantInt::get(builder.getInt32Ty(), 0),
    /*Name=*/        "foster__gcmaps",
    /*InsertBefore=*/NULL,
    /*ThreadLocal=*/ false);
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
    // Associate the LLProc with its name so we can get its type later on.
    pass->procs[procs[i]->getCName()] = procs[i];
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegenProc(pass);
  }

  codegenCoroPrimitives(pass);

  createGCMapsSymbolIfNeeded(pass);
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
    return dyn_cast<llvm::FunctionType>(slotType(pt));
  } else {
    return NULL;
  }
}

void setFunctionArgumentNames(llvm::Function* F,
              const std::vector<std::string>& argnames) {
  assertRightNumberOfArgnamesForFunction(F, argnames);
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
  if (pass->config.useGC) { F->setGC("fostergc"); }
  F->setCallingConv(this->type->getCallingConventionID());
}

////////////////////////////////////////////////////////////////////

void LLProc::codegenProc(CodegenPass* pass) {
  ASSERT(this->F != NULL) << "LLModule should codegen proto for " << getName();
  assertRightNumberOfArgnamesForFunction(F, this->getFunctionArgNames());

  pass->addEntryBB(F);
  CodegenPass::ValueScope* scope = pass->newScope(this->getName());

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

// We shouldn't get any such things from the middle-end.
void checkForUnusedEmptyBasicBlocks(llvm::Function* F) {
  for(llvm::Function::iterator BB_it = F->begin();
                               BB_it != F->end(); ++BB_it) {
    ASSERT(! (BB_it->empty() && BB_it->use_empty()) );
  }
}

void initializeBlockPhis(LLBlock* block) {
  builder.SetInsertPoint(block->bb);
  for (size_t i = 0; i < block->phiVars.size(); ++i) {
    block->phiNodes.push_back(
           builder.CreatePHI(getLLVMType(block->phiVars[i]->type),
                        block->numPreds, block->phiVars[i]->getName()));
  }
}

void LLProcCFG::codegenToFunction(CodegenPass* pass, llvm::Function* F) {
  pass->fosterBlocks.clear();

  // Pre-allocate all our GC roots.
  for (size_t i = 0; i < gcroots.size(); ++i) {
    llvm::AllocaInst* slot = CreateEntryAlloca(getLLVMType(gcroots[i]->type),
                                               gcroots[i]->getName());
    if (pass->config.useGC) { markGCRoot(slot, pass); }
    pass->insertScopedValue(gcroots[i]->getName(), slot);
  }

  // Create all the basic blocks before codegenning any of them.
  for (size_t i = 0; i < blocks.size(); ++i) {
    LLBlock* bi = blocks[i];
    pass->fosterBlocks[bi->block_id] = bi;
    bi->bb = BasicBlock::Create(builder.getContext(), bi->block_id, F);
    ASSERT(bi->block_id == bi->bb->getName())
                     << "function can't have two blocks named " << bi->block_id;
  }

  ASSERT(blocks.size() > 0) << F->getName() << " had no blocks!";

  // Create phi nodes in all the blocks,
  // and make them available via block->phiNodes.
  llvm::BasicBlock* savedBB = builder.GetInsertBlock();
  for (size_t i = 0; i < blocks.size(); ++i) {
    initializeBlockPhis(blocks[i]);
  }

  // Make sure we branch from the entry block to the first 'computation' block
  // which will either be a case analysis on the env parameter, or postalloca.
  builder.SetInsertPoint(savedBB);
  LLBr br(blocks[0]->block_id);
  if (isEnvPtr(F->arg_begin())) {
    br.args.push_back(new LLValueVar(F->arg_begin()));
  }
  br.codegenTerminator(pass);

  pass->worklistBlocks.clear();
  pass->scheduleBlockCodegen(blocks[0]);
  while (!pass->worklistBlocks.empty()) {
    LLBlock* b = pass->worklistBlocks.get();
    b->codegenBlock(pass);
  }

  checkForUnusedEmptyBasicBlocks(F);
}

////////////////////////////////////////////////////////////////////

void LLBlock::codegenBlock(CodegenPass* pass) {
  builder.SetInsertPoint(bb);
  for (size_t i = 0; i < this->phiVars.size(); ++i) {
     pass->insertScopedValue(this->phiVars[i]->getName(), this->phiNodes[i]);
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
  llvm::Value* rv = this->val->codegen(pass);
  bool fnReturnsVoid = builder.getCurrentFunctionReturnType()->isVoidTy();
  if (!fnReturnsVoid && rv->getType()->isVoidTy()) {
     // Assumption is that our return type might be {}* (i.e. unit)
     // but the last thing we called returned void.
     assertCurrentFunctionReturnsUnitType();
     rv = getUnitValue();
  }

  if (fnReturnsVoid) {
    builder.CreateRetVoid();
  } else {
    builder.CreateRet(rv);
  }
}

void passPhisAndBr(LLBlock* block, const vector<llvm::Value*>& args) {
  assertHaveSameNumberOfArgsAndPhiNodes(args, block);
  std::stringstream ss; ss << "br args:";
  for (size_t i = 0; i < args.size(); ++i) {
    llvm::Value* v = args[i];
    if (v->getType()->isVoidTy()) {
      v = getUnitValue(); // Can't pass a void value!
    }
    assertValueHasSameTypeAsPhiNode(v, block, i);
    block->phiNodes[i]->addIncoming(v, builder.GetInsertBlock());
    ss << " " << v->getName().str() << ";";
  }
  emitFakeComment(ss.str());
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

////////////////////////////////////////////////////////////////////

void addAndEmitTo(Function* f, BasicBlock* bb) {
  f->getBasicBlockList().push_back(bb);
  builder.SetInsertPoint(bb);
}

ConstantInt* getTagForCtorId(const CtorId& c) {
         if (c.typeName == "Bool")  { return builder.getInt1(c.smallId);
  } else if (c.typeName == "Int32") { return builder.getInt32(c.smallId);
  } else                            { return builder.getInt8(c.smallId); }
}

llvm::Value* emitCallGetCtorIdOf(CodegenPass* pass, llvm::Value* v) {
  llvm::Value* foster_ctor_id_of = pass->mod->getFunction("foster_ctor_id_of");
  ASSERT(foster_ctor_id_of != NULL);
  return markAsNonAllocating(builder.CreateCall(foster_ctor_id_of,
                             emitBitcast(v, builder.getInt8PtrTy())));
}

void codegenSwitch(CodegenPass* pass, LLSwitch* sw, llvm::Value* insp_tag) {
  BasicBlock* defaultBB = (sw->defaultCase.empty())
                ? NULL
                : pass->lookupBlock(sw->defaultCase)->bb;

  BasicBlock* bbNoDefault = defaultBB ? NULL      :
                     BasicBlock::Create(builder.getContext(), "case_nodefault");
  BasicBlock* defOrContBB = defaultBB ? defaultBB : bbNoDefault;

  // Switch on the inspected value and add cases for each ctor considered.
  llvm::SwitchInst* si = builder.CreateSwitch(insp_tag, defOrContBB, sw->ctors.size());

  for (size_t i = 0; i < sw->ctors.size(); ++i) {
    BasicBlock* destBB = pass->lookupBlock(sw->blockids[i])->bb;
    ASSERT(destBB != NULL);

    // Compute the tag for the ctor associated with this branch.
    const CtorId& c = sw->ctors[i];
    ConstantInt* onVal = getTagForCtorId(c);

    ASSERT(si->getCondition()->getType() == onVal->getType())
        << "switch case and inspected value had different types!"
        << "SwitchCase ctor " << (i+1) << "/" << sw->ctors.size()
           << ": " << c.typeName << "." << c.ctorName << "#" << c.smallId;

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

void LLSwitch::codegenTerminator(CodegenPass* pass) {
  ASSERT(ctors.size() == blockids.size());
  ASSERT(ctors.size() >= 1);

  // Fetch the subterm of the scrutinee being inspected.
  llvm::Value* inspected = this->occ->codegen(pass);
  llvm::Value* tag = NULL;

  // All the ctors should have the same data type, now that we have at least
  // one ctor, lookup its tag representation based on its associated type.
  CtorTagRepresentation ctr = pass->dataTypeTagReprs[ctors[0].typeName];

  switch (ctr) {
  case CTR_BareValue: tag = inspected; break;
  case CTR_OutOfLine: tag = emitCallGetCtorIdOf(pass, inspected); break;
  case CTR_MaskWith3: ASSERT(false) << "inline ctor tag bits not yet supported"; break;
  default: ASSERT(false) << "unknown tag representation in LLSwitch::codegen!";
  }

  codegenSwitch(pass, this, tag);
}

///}}}//////////////////////////////////////////////////////////////

llvm::Value* LLBitcast::codegen(CodegenPass* pass) {
  llvm::Value* v = var->codegen(pass);
  llvm::Type* tgt = getLLVMType(this->type);
  return (v->getType() == tgt) ? v : emitBitcast(v, tgt);
}

void LLGCRootInit::codegenMiddle(CodegenPass* pass) {
  llvm::Value* v    = src->codegen(pass);
  llvm::Value* slot = root->codegen(pass);
  if (pass->config.emitLifetimeInfo) {
    markAsNonAllocating(builder.CreateLifetimeStart(slot));
  }
  emitStore(v, slot);
}

void LLGCRootKill::codegenMiddle(CodegenPass* pass) {
  llvm::Value* slot = root->codegen(pass);
  if (this->doNullOutSlot &&
      pass->config.killDeadSlots) { storeNullPointerToSlot(slot); }
  if (pass->config.emitLifetimeInfo) {
     markAsNonAllocating(builder.CreateLifetimeEnd(slot));
  }
}

void LLRebindId::codegenMiddle(CodegenPass* pass) {
  pass->insertScopedValue(from, to->codegen(pass));
}

////////////////////////////////////////////////////////////////////
/////////////// LLDeref, LLStore, LLLetVals ////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLDeref::codegen(CodegenPass* pass) {
  llvm::Value* ptr = base->codegen(pass);
  return emitNonVolatileLoad(ptr, "deref");
}

llvm::Value* LLStore::codegen(CodegenPass* pass) {
  llvm::Value* vv = v->codegen(pass);
  llvm::Value* vr = r->codegen(pass);
  return emitStore(vv, vr);
}

llvm::Value* LLObjectCopy::codegen(CodegenPass* pass) {
  llvm::Value* vv = from->codegen(pass);
  llvm::Value* vr =   to->codegen(pass);
  // TODO assert that object tags are equal?

  llvm::Value* from_obj = emitNonVolatileLoad(vv, "from_obj");
  return emitStore(from_obj, vr);
}

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
    Value* b = exprs[i]->codegen(pass);
    trySetName(b, names[i]);
    pass->insertScopedValue(names[i], b);
  }
}

///}}}///////////////////////////////////////////////////////////////

llvm::Value* LLCoroPrim::codegen(CodegenPass* pass) {
  llvm::Type* r = retType->getLLVMType();
  llvm::Type* a = typeArg->getLLVMType();
  if (this->primName == "coro_yield") { return pass->emitCoroYieldFn(r, a); }
  if (this->primName == "coro_invoke") { return pass->emitCoroInvokeFn(r, a); }
  if (this->primName == "coro_create") { return pass->emitCoroCreateFn(retType, typeArg); }
  ASSERT(false) << "unknown coro prim: " << this->primName;
  return NULL;
}

////////////////////////////////////////////////////////////////////
//////////////////// Literals and variables ////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLBool::codegen(CodegenPass* pass) {
  return builder.getInt1(this->boolValue);
}

llvm::Value* LLFloat::codegen(CodegenPass* pass) {
  ASSERT(this->type) << "LLFloat was missing its type...";
  return llvm::ConstantFP::get(getLLVMType(this->type), this->doubleValue);
}

llvm::Value* LLText::codegen(CodegenPass* pass) {
  Value* gstr = pass->getGlobalString(this->stringValue);
  size_t size = this->stringValue.size();
  return pass->emitFosterStringOfCString(gstr, builder.getInt32(size));
}

llvm::Value* LLValueVar::codegen(CodegenPass* pass) {
  return this->val;
}

llvm::Value* LLGlobalSymbol::codegen(CodegenPass* pass) {
  return pass->lookupFunctionOrDie(this->name);
}

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  llvm::Value* v = pass->valueSymTab.lookup(getName());
  if (!v) {
    builder.GetInsertBlock()->getParent()->dump();
    pass->valueSymTab.dump(llvm::errs());
    ASSERT(false) << "Unknown variable name " << this->name << " in CodegenPass";
  }
  return v;
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

llvm::Value* LLKillProcess::codegen(CodegenPass* pass) {
  emitFosterAssert(pass->mod, builder.getFalse(), this->stringValue.c_str());
  return llvm::UndefValue::get(this->type->getLLVMType());
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLAllocate ////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

Value* allocateCell(CodegenPass* pass, TypeAST* type,
                    LLAllocate::MemRegion region,
                    int8_t ctorId, std::string srclines, bool init) {
  llvm::Type* ty = type->getLLVMType();

  switch (region) {
  case LLAllocate::MEM_REGION_STACK:
    // TODO this allocates a slot, not a cell...
    // TODO init
    //
    ASSERT(!containsGCablePointers(type, ty));
    // If the allocated type is POD, this is fine.
    // But if the allocated type can contain pointers which must be treated
    // as roots by the GC, we must enforce a few extra invariants (which are
    // not currently enforced):
    //  1) We must allocate a cell, not a slot, to store the type.
    //  2) We must allocate a slot, pointing to the stack cell, marked gcroot.
    //  3) We must ensure that no load from the cell persists across a safe pt.
    //  4) We must ensure that the GC does update the pointers within the cell.
    //  5) We must(?) ensure that the GC does not attempt to copy the stack
    //     cell to the heap.
    return CreateEntryAlloca(ty, "stackref");

  case LLAllocate::MEM_REGION_GLOBAL_HEAP:
    return pass->emitMalloc(type, ctorId, srclines, init);

  default:
    ASSERT(false); return NULL;
  }
}

llvm::Value* LLAllocate::codegen(CodegenPass* pass) {
  if (this->arraySize != NULL) {
    Value* array_size = this->arraySize->codegen(pass);
    ASSERT(this->region == LLAllocate::MEM_REGION_GLOBAL_HEAP);
    return pass->emitArrayMalloc(this->type, array_size, this->zero_init);
  } else {
    if (StructTypeAST* sty = dynamic_cast<StructTypeAST*>(this->type)) {
      registerStructType(sty, this->type_name,          this->ctorId, pass->mod);
    }
    return allocateCell(pass, this->type, this->region, this->ctorId,
                              this->srclines, this->zero_init);
  }
}

///}}}//////////////////////////////////////////////////////////////
//////////////// Arrays ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

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

Value* getArraySlot(Value* base, Value* idx, CodegenPass* pass,
                    bool dynCheck, const std::string& srclines) {
  Value* arr = NULL; Value* len;
  if (tryBindArray(base, arr, len)) {
    if (dynCheck) {
      emitFosterArrayBoundsCheck(pass->mod, idx, len, srclines);
    }
    return getPointerToIndex(arr, idx, "arr_slot");
  } else {
    ASSERT(false) << "expected array, got " << str(base);
    return NULL;
  }
}


llvm::Value* LLArrayIndex::codegenARI(CodegenPass* pass) {
  Value* base = this->base ->codegen(pass);
  Value* idx  = this->index->codegen(pass);
  ASSERT(static_or_dynamic == "static" || static_or_dynamic == "dynamic");
  return getArraySlot(base, idx, pass, this->static_or_dynamic == "dynamic",
                                       this->srclines);
}

llvm::Value* LLArrayRead::codegen(CodegenPass* pass) {
  Value* slot = ari->codegenARI(pass);
  Value* val  = emitNonVolatileLoad(slot, "arrayslot");
  ASSERT(this->type) << "LLArrayRead with no type?";
  ASSERT(this->type->getLLVMType() == val->getType());
  return val;
}

  // base could be an array a[i] or a slot for a reference variable r.
  // a[i] should codegen to &a[i], the address of the slot in the array.
  // r    should codegen to the contents of the slot (the ref pointer value),
  //        not the slot address.

llvm::Value* LLArrayPoke::codegen(CodegenPass* pass) {
  Value* val  = this->value->codegen(pass);
  Value* slot = ari->codegenARI(pass);
  return builder.CreateStore(val, slot, /*isVolatile=*/ false);
}

llvm::Value* LLArrayLength::codegen(CodegenPass* pass) {
  Value* val  = this->value->codegen(pass);
  Value* _bytes; Value* len;
  if (tryBindArray(val, /*out*/ _bytes, /*out*/ len)) {
    // len already assigned.
  } else { ASSERT(false); }
  return len;
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLTupleStore //////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLUnitValue::codegen(CodegenPass* pass) {
  return getUnitValue();
}

void copyValuesToStruct(const std::vector<llvm::Value*>& vals,
                        llvm::Value* tup_ptr) {
  ASSERT(tup_ptr != NULL);
  ASSERT(isPointerToStruct(tup_ptr->getType()))
        << "copyValuesToStruct can't copy values to non-ptr-to-struct type "
        << str(tup_ptr->getType())
        << "\n" << str(tup_ptr);

  for (size_t i = 0; i < vals.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(tup_ptr, 0, i, "gep");
    emitStore(vals[i], dst);
  }
}

void LLTupleStore::codegenMiddle(CodegenPass* pass) {
  if (vars.empty()) return;
  llvm::Value* tup_ptr = this->storage->codegen(pass);
  copyValuesToStruct(codegenAll(pass, this->vars), tup_ptr);
}

///}}}//////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//////////////// Decision Trees ////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLOccurrence::codegen(CodegenPass* pass) {
  ASSERT(ctors.size() == offsets.size());

    std::stringstream ss; ss << "occ["<<this->var->getName()<<"](";
    for (size_t i = 0; i < offsets.size(); ++i) {
      ss << offsets[i] << ":";
      ss << ctors[i].ctorId.ctorName << "::";
    }
    ss << ")--";

    emitFakeComment(ss.str());


  llvm::Value* v = this->var->codegen(pass);

  for (size_t i = 0; i < offsets.size(); ++i) {
    // If we know that the subterm at this position was created with
    // a particular data constructor, emit a cast to that ctor's type.
    if (ctors[i].ctorStructType) {
      v = emitBitcast(v, ptrTo(ctors[i].ctorStructType->getLLVMType()));
    }

    v = getElementFromComposite(v, offsets[i], "switch_insp");
  }

  // Consider code like         case v of Some x -> ... x ...
  // when there's a type definition Maybe a = None | Some a.
  // v's source type is Maybe X, which (since we erase type parameters)
  // corresponds to the LLVM type Maybe.DT*. This will be refined to
  // { i999* }* when computing the occurrence for x. But x's physical type then
  // remains i999*, while it ought to be the translation of its source type, X.
  // This bitcast fixes the mismatch.
  return emitBitcast(v, getLLVMType(this->type), "occty");
}

///}}}//////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//////////////// Term Application //////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLCallPrimOp::codegen(CodegenPass* pass) {
  return pass->emitPrimitiveOperation(this->op, builder,
                                      codegenAll(pass, this->args));
}

// Returns null if no bitcast is needed, else returns the type to bitcast to.
bool isPointerToUnknown(Type* ty) {
  return ty->isPointerTy() &&
         slotType(ty)->isIntegerTy(kUnknownBitsize);
}

bool matchesExceptForUnknownPointers(Type* aty, Type* ety) {
  //EDiag() << "matchesExceptForUnknownPointers ? " << str(aty) << " =?= " << str(ety);
  if (aty == ety) return true;
  if (aty->isPointerTy() && ety->isPointerTy()) {
    if (isPointerToUnknown(ety)) { return true; }
    return matchesExceptForUnknownPointers(slotType(aty), slotType(ety));
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

llvm::Value* emitFnArgCoercions(llvm::Value* argV, llvm::Type* expectedType) {
  // This is a an artifact produced by the mutual recursion
  // of the environments of mutually recursive closures.
  if (  argV->getType() != expectedType
    &&  argV->getType() == getGenericClosureEnvType()->getLLVMType()) {
    EDiag() << "emitting bitcast gen2spec (exp: " << str(expectedType)
            << "); (actual: " << str(argV->getType()) << ")";
    argV = emitBitcast(argV, expectedType, "gen2spec");
  }

  // This occurs in polymorphic code.
  if ((argV->getType() != expectedType)
      && matchesExceptForUnknownPointers(argV->getType(), expectedType)) {
    EDiag() << "matched " << str(argV->getType()) << " to " << str(expectedType);
    argV = emitBitcast(argV, expectedType, "spec2gen");
  }

  return argV;
}

llvm::CallingConv::ID parseCallingConv(std::string cc) {
  if (cc == "fastcc") { return llvm::CallingConv::Fast; }
  ASSERT(cc == "ccc") << "unknown calling convention " << cc;
  return llvm::CallingConv::C;
}

llvm::Value* LLCall::codegen(CodegenPass* pass) {
  ASSERT(base != NULL) << "unable to codegen call due to null base";
  Value* FV = base->codegen(pass);
  ASSERT(FV) << "unable to codegen call due to missing value for base";

  llvm::FunctionType* FT = NULL;
  std::vector<Value*> valArgs;

  llvm::CallingConv::ID callingConv = parseCallingConv(this->callconv);

  if (Function* F = llvm::dyn_cast<Function>(FV)) {
    // Call to top level function
    ASSERT(callingConv == F->getCallingConv());
    FT = F->getFunctionType();
  } else if (isFunctionPointerTy(FV->getType())) {
    FT = dyn_cast<llvm::FunctionType>(slotType(FV));
  } else {
    ASSERT(isPointerToStruct(FV->getType()));
    // Load code and env pointers from closure...
    llvm::Value* envPtr =
         getElementFromComposite(FV, 1, "getCloEnv");
    FV = getElementFromComposite(FV, 0, "getCloCode");
    FT = dyn_cast<llvm::FunctionType>(slotType(FV));
    // Pass env pointer as first parameter to function.
    valArgs.push_back(envPtr);
  }

  assertHaveCallableType(base, FT, FV);

  // Collect the args, performing coercions if necessary.
  for (size_t i = 0; i < this->args.size(); ++i) {
    llvm::Type* expectedType = FT->getParamType(valArgs.size());
    llvm::Value* argV = this->args[i]->codegen(pass);
    argV = emitFnArgCoercions(argV, expectedType);
    assertValueHasExpectedType(argV, expectedType, FV);
    valArgs.push_back(argV);
  }

  assertRightNumberOfArgsForFunction(FV, FT, valArgs);

  // Give the instruction a name, if we can...

  llvm::CallInst* callInst = builder.CreateCall(FV, llvm::makeArrayRef(valArgs));
  callInst->setCallingConv(callingConv);
  trySetName(callInst, "calltmp");

  if (this->okToMarkAsTailCall) {
    ASSERT(callingConv == llvm::CallingConv::Fast);
    callInst->setTailCall(true);
  }

  if (!this->callMightTriggerGC) {
    markAsNonAllocating(callInst);
  } else {
    emitFakeComment("ABOVE CALL MAY TRIGGER GC...");
  }

  return callInst;
}

/// }}}

