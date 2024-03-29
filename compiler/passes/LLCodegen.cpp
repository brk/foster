// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#define DEBUG_TYPE "foster-codegen"

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterTypeAST.h"

#include "passes/FosterLL.h"
#include "passes/CodegenPass-impl.h"

#include "llvm/IR/Attributes.h"
#include "llvm/IR/AttributeMask.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/DataLayout.h"

#include "llvm/IR/Metadata.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
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
using foster::DDiag;

using std::vector;

STATISTIC(MEMCPY_FROM_GLOBAL_TO_HEAP, "[foster] statically emitted memcpy operations");

namespace foster {

void codegenLL(LLModule* prog, llvm::Module* mod, /*llvm::DataLayout dl,*/ CodegenPassConfig config) {
  CodegenPass cp(mod, /*dl,*/ config);
  prog->codegenModule(&cp);
  cp.emitTypeMapListGlobal();
}

void deleteCodegenPass(CodegenPass* cp) { delete cp; }

} // namespace foster


char kFosterMain[] = "foster__main";
int  kUnknownBitsize = 999; // keep in sync with IntSizeBits in Base.hs

// {{{ Internal helper functions
bool tryBindArray(CodegenPass* pass, llvm::Type* sty, Value* base, Value*& arr, Value*& len);

namespace {

llvm::Type* getLLVMType(const TypeAST* type) {
  ASSERT(type) << "getLLVMType must be given a non-null type!";
  return type->getLLVMType();
}

llvm::Value* emitGCWrite(CodegenPass* pass, Value* val, Value* base, Value* slot) {
  if (!base) base = getNullOrZero(builder.getPtrTy());
  auto gcwrite_fn = pass->mod->getFunction("foster_write_barrier_with_obj_generic");

  if (llvm::isa<llvm::ConstantExpr>(val)) {
    // We can elide barriers for writes of constant values
    // (because we don't need to keep track of lost references, only added ones).
    return builder.CreateStore(val, slot, /*isVolatile=*/ false);
  } else {
    return builder.CreateCall(gcwrite_fn, { val, base, slot });
  }
}

// TODO (eventually) try emitting masks of loaded/stored heap pointers
// to measure performance overhead of high/low tags.

inline llvm::Value* emitNonVolatileLoad(llvm::Type* ty, llvm::Value* v, llvm::Twine name) {
  return builder.CreateLoad(ty, v, false, name);
}

enum WriteSelector {
  WriteUnspecified,
  WriteKnownNonGC
};

llvm::Value* emitGCWriteOrStore(CodegenPass* pass,
                       llvm::Value* val,
                       llvm::Value* base,
                       llvm::Value* ptr,
                       WriteSelector w = WriteUnspecified) {
  //llvm::outs() << "logging write of " << *val <<
  //              "\n              to " << *ptr <<
  //              "\n     isNonGC = " << (w == WriteKnownNonGC) << "; val is ptr ty? " << val->getType()->isPointerTy() << "\n";
  bool useBarrier = val->getType()->isPointerTy()
        && !llvm::isa<llvm::AllocaInst>(ptr)
        && w != WriteKnownNonGC;
  //maybeEmitCallToLogPtrWrite(pass, ptr, val, useBarrier);

  if (useBarrier) {
    return emitGCWrite(pass, val, base, ptr);
  } else {
    return builder.CreateStore(val, ptr, /*isVolatile=*/ false);
  }
}

llvm::Value* substituteUnitForVoid(Value* argV) {
  // If we're calling a C function that returns void, conjure up a unit value.
  if (argV->getType()->isVoidTy()) {
    return getUnitValue();
  }

  return argV;
}

llvm::Value* emitStore(CodegenPass* pass,
                       llvm::Value* val,
                       llvm::Value* ptr,
                       llvm::Value* base,
                       WriteSelector w = WriteUnspecified) {
  return emitGCWriteOrStore(pass, substituteUnitForVoid(val), base, ptr, w);
}

Value* emitCallToInspectPtr(CodegenPass* pass, Value* ptr) {
   llvm::Function* rmc = pass->mod->getFunction("inspect_ptr_for_debugging_purposes");
   ASSERT(rmc) << "couldnt find inspect_ptr_for_debugging_purposes";
   return builder.CreateCall(from(rmc), ptr);
}

std::vector<llvm::Value*>
codegenAll(CodegenPass* pass, const std::vector<LLVar*>& args) {
  std::vector<llvm::Value*> vals;
  for (size_t i = 0; i < args.size(); ++i) {
    vals.push_back(args[i]->codegen(pass));
  }
  return vals;
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
    if (!typesEq(argV->getType(), expectedType)) {
      //builder.GetInsertBlock()->getParent()->dump();
      //llvm::errs() << str(builder.GetInsertBlock()->getParent()) << "\n";
      llvm::errs() << *(builder.GetInsertBlock()->getParent()->getParent()) << "\n";
    }
    ASSERT(typesEq(argV->getType(), expectedType))
              << "\ntype mismatch: "
              << "\n had type         " << str(argV->getType())
              << "\n vs expected type " << str(expectedType)
              << "\nargV = " << str(argV)
              << "\nand base type " << str(FV->getType())
              << "\nfor base " << str(FV) << "\n";
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
      << "\n from value " << str(v) << " to block " << (block->block_id)
      << "\n in function " << block->phiNodes[i]->getParent()->getParent()->getName() << "\n";
}

/// }}}

} // }}} namespace

// Implementation of CodegenPass helpers {{{

Value* getElementFromComposite(CodegenPass* pass, Type* compositePointeeTy, Value* compositeValue,
                               int indexValue, const std::string& msg, bool assumeImmutable=false) {
  ASSERT(indexValue >= 0);
  Value* idxValue = builder.getInt32(indexValue);
  Type* compositeType = compositeValue->getType();
  // To get an element from an in-memory object, compute the address of
  // the appropriate struct field and emit a load.
  
  if (llvm::isa<llvm::PointerType>(compositeType)) {
    Value* gep = getPointerToIndex(compositePointeeTy, compositeValue, idxValue, (msg + ".subgep").c_str());

#if 0
    if (assumeImmutable) {
      if (auto C = dyn_cast<llvm::ConstantExpr>(gep)) {
        if (auto GEP = llvm::cast<llvm::GetElementPtrInst>(C->getAsInstruction())) {
          if (auto GV = llvm::dyn_cast<llvm::GlobalVariable>(GEP->getPointerOperand())) {
            /*
            auto V = llvm::ConstantFoldLoadThroughGEPConstantExpr(GV->getInitializer(), C);
            if (V) {
              GEP->deleteValue();
              return V;
            }
            */
          }
          GEP->deleteValue();
        }
      }
    }
    #endif

    //maybeEmitCallToLogPtrRead(pass, gep);
    std::string loadname;
    if (gep->hasName()) { loadname = std::string(gep->getName()) + std::string("_ld"); }
    else { loadname  = msg + ".subgep.ld"; }

    return emitNonVolatileLoad(compositePointeeTy->getContainedType(indexValue), gep, loadname);
  } else if (llvm::isa<llvm::StructType>(compositeType)) {
    return builder.CreateExtractValue(compositeValue, indexValue, (msg + "subexv").c_str());
  } else if (llvm::isa<llvm::VectorType>(compositeType)) {
    return builder.CreateExtractElement(compositeValue, idxValue, (msg + "simdexv").c_str());
  } else {
    EDiag() << "Cannot index into value type " << str(compositeType)
            << " with non-constant index " << str(idxValue);
  }
  return NULL;
}


CodegenPass::CodegenPass(llvm::Module* m,/*llvm::DataLayout dl,*/ CodegenPassConfig config)
    : config(config), mod(m), /*datalayout(dl),*/ currentProcName("<no proc yet>") {
  //dib = new DIBuilder(*mod);

  // N.B. we assume here that the input module m has already been linked
  // with the runtime library. We want to copy the function attributes that
  // Clang decorated the stdlib functions with, because we need some of the
  // attributes (such as "target-features=+sse2") to match, otherwise we'll
  // get incorrect results.
  if (llvm::Function* f = mod->getFunction("memalloc_cell")) {
    // No attribute mangling for functions outside the runtime.
    llvm::AttributeList attrs = f->getAttributes();

    llvm::AttributeMask toremove;
    toremove.addAttribute(
        llvm::Attribute::get(f->getContext(), "stack-protector-buffer-size", "8"));
    toremove.addAttribute(
        llvm::Attribute::get(f->getContext(), "frame-pointer", "none"));
    toremove.addAttribute(
        llvm::Attribute::get(f->getContext(), "norecurse"));
    toremove.addAttribute(
        llvm::Attribute::get(f->getContext(), "uwtable"));  
    attrs = attrs.removeFnAttributes(f->getContext(), toremove);

    llvm::AttrBuilder toadd(f->getContext());
    toadd.addAttribute(
        llvm::Attribute::get(f->getContext(), "foster-fn"));
    toadd.addAttribute(
        llvm::Attribute::get(f->getContext(), "frame-pointer", "all")); // TODO non-leaf
    attrs = attrs.addFnAttributes(f->getContext(), toadd);

    // 
    attrs = attrs.removeAttributeAtIndex(f->getContext(), llvm::AttributeList::FirstArgIndex,
                                         llvm::Attribute::NoUndef);

    this->fosterFunctionAttributes = attrs;
  }
}

llvm::FunctionCallee CodegenPass::lookupFunctionOrDie(const std::string&
                                                       fullyQualifiedSymbol) {
  llvm::Function* f = mod->getFunction(fullyQualifiedSymbol);
  assertHaveFunctionNamed(f, fullyQualifiedSymbol, this);
  return llvm::FunctionCallee(f->getFunctionType(), f);
}

llvm::CallingConv::ID parseCallingConv(std::string cc) {
  if (cc == "fastcc") { return llvm::CallingConv::Fast; }
  ASSERT(cc == "ccc") << "unknown calling convention " << cc;
  return llvm::CallingConv::C;
}

llvm::Value* CodegenPass::emitFosterStringOfCString(Value* cstr, Value* sz) {
  bool init = false; // because we'll immediately memcpy.
  Value* hstr = this->emitArrayMalloc(TypeAST::i(8), sz, init);
  // This variable is dead after being passed to the TextFragment function,
  // so it does not need a GC root.

  auto sty = ArrayTypeAST::getZeroLengthType(TypeAST::i(8));

  Value* hstr_bytes; Value* len;
  if (tryBindArray(this, sty, hstr, /*out*/ hstr_bytes, /*out*/ len)) {
    builder.CreateMemCpy(hstr_bytes, /* dst align */ llvm::MaybeAlign(4),
                               cstr, /* src align */ llvm::MaybeAlign(4),
                               sz);
  } else { ASSERT(false); }

  // TODO null terminate?

  llvm::FunctionCallee textfragment = lookupFunctionOrDie("TextFragment");
  llvm::CallInst* call = builder.CreateCall(textfragment, { hstr, sz });
  call->setCallingConv(parseCallingConv("fastcc"));
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

void createCompilerFlagsGlobalString(CodegenPass* pass) {
  std::stringstream ss;
  ss << "{";
  ss << "'disableAllArrayBoundsChecks':" << pass->config.disableAllArrayBoundsChecks;
  ss << "}";
  auto gv = builder.CreateGlobalString(ss.str(), "__foster_fosterlower_config");
  gv->setLinkage(llvm::GlobalValue::ExternalLinkage);
}

void addExternDecls(const std::vector<LLDecl*> decls,
                    CodegenPass* pass) {
  for (auto d : decls) {
    if (d->isForeign) {
      const std::string& declName = d->getName();
      TypeAST* fosterType = d->getType();

      //llvm::outs() << "addExternDecls() saw " << declName << " :: " << str(fosterType) << "\n";

      if (const FnTypeAST* fnty = fosterType->castFnTypeAST()) {
        
        std::string autowrappedName = declName + std::string("__autowrap");
        if (auto existing = pass->mod->getFunction(autowrappedName)) {
          // If we import ``foo`` and we have a symbol ``foo__autowrap``, use it.
          codegenAutoWrapper(existing, fnty->getLLVMFnType(), declName, pass);
        } else if (llvm::Function* target = pass->mod->getFunction(declName)) {
          // We have ``foo`` but no ``foo__autowrap``.

          if ((!target->isDeclaration()) &&
                str(target->getType()->getContainedType(0))
                        != str(fnty->getLLVMFnType())) {
            // If the function we import has a different type than we expected,
            // automatically generate a wrapper to resolve the differences in types.
            // The original function gets renamed; the new function wraps the original
            // to provide the expected types to Foster code.
            // We only generate a wrapper when we can rename the definition;
            // renaming a declaration only causes problems when we link against the
            // real definition.
            target->setName(declName + std::string("__autowrap"));
            codegenAutoWrapper(target, fnty->getLLVMFnType(), declName, pass);
          } else {
            // Nothing to do; either the imported symbol already has the right type,
            // or it's a declaration instead a definition, so we can't rename it.
          }
        } else {
          // Unable to find either ``foo`` or ``foo__autowrap``; insert a declaration.
          pass->mod->getOrInsertFunction(declName, fnty->getLLVMFnType());
        }

      } else { // Not a function type, must be a regular global.

        auto g = pass->mod->getOrInsertGlobal(declName, getLLVMType(fosterType));
        if (d->autoDeref) {
          pass->autoDerefs[declName] = g;
        }
      }

    }
  }
}

///}}}//////////////////////////////////////////////////////////////
llvm::GlobalVariable* emitPrivateGlobal(CodegenPass* pass,
                                 llvm::Constant* val,
                                 const std::string& name);
llvm::Constant* mkGlobalNonArrayCellConstant(CodegenPass* pass,
                                     llvm::GlobalVariable* typemap,
                                     llvm::Constant* body);

void LLModule::codegenModule(CodegenPass* pass) {
  registerKnownDataTypes(datatype_decls, pass);

  addExternDecls(extern_val_decls, pass);

  extendWithImplementationSpecificProcs(pass, procs);

  // Ensure that the llvm::Function*s are created for all the function
  // prototypes, so that mutually recursive function references resolve,
  // and any globals can reference functions.
  for (size_t i = 0; i < procs.size(); ++i) {
    // Ensure that the value is in the SymbolInfo entry in the symbol table.
    procs[i]->codegenProto(pass);
    // Associate the LLProc with its name so we can get its type later on.
    pass->procs[procs[i]->getCName()] = procs[i];
  }

  for (size_t i = 0; i < procs.size(); ++i) {
    // Codegen a global cell containing a closure pair for top-level functions.
    // The middle-end detects top-level functions which are used as closures
    // in a higher order way, and uses the name F.func instead of F, which
    // (at the end of this loop) gets mapped to the contents of the global cell.
    if (procs[i]->getCName() == "main") continue;

    std::vector<llvm::Constant*> cell_vals;
    auto Ffunc = pass->mod->getFunction(procs[i]->getCName() + ".proc");
    ASSERT(Ffunc) << "Couldn't find a closure wrapper for " << procs[i]->getCName();
    cell_vals.push_back(Ffunc);
    cell_vals.push_back(getNullOrZero(builder.getPtrTy()));
    auto const_cell = llvm::ConstantStruct::getAnon(cell_vals);

    std::string cloname = procs[i]->getCName();

    CtorRepr ctorRepr; ctorRepr.smallId = -1;
    auto globalCellConstant = mkGlobalNonArrayCellConstant(pass,
                          pass->getTypeMapForType(TypeAST::i(64), ctorRepr, pass->mod, NotArray),
                          const_cell);
    auto globalCell = emitPrivateGlobal(pass, globalCellConstant, cloname + ".closure.cell");

    pass->globalValues[cloname] = builder.CreateConstGEP2_32(globalCellConstant->getType(),
                                                             globalCell, 0, 2);
  }

  for (auto& item : items) {
    //llvm::errs() << "Adding " << item->name << " to pass->globalValues\n";

    if (item->arrlit) {
      pass->globalValues[item->name] = item->arrlit->codegen(pass);
    } else {
      pass->globalValues[item->name] = item->lit->codegen(pass);
      pass->insertScopedValue(item->name, pass->globalValues[item->name]);
    }
  }

  // Codegen all the function bodies, now that we can resolve mutually-recursive
  // function references without needing to store prototypes in call nodes.
  for (size_t i = 0; i < procs.size(); ++i) {
    procs[i]->codegenProc(pass);
  }

  codegenCoroPrimitives(pass);

  createCompilerFlagsGlobalString(pass);
}

////////////////////////////////////////////////////////////////////
//////////////// LLProc, LLProto ///////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

bool isReturnTypeOK(llvm::Type* ty) {
  return true; // TODO verify not opaque
}

llvm::FunctionType*
getLLVMFunctionType(FnTypeAST* t, const std::string& procSymbol) {
  ASSERT(isReturnTypeOK(getLLVMType(t->getReturnType())))
        << "Cannot use opaque return type for proc " << procSymbol;
  return t->getLLVMFnType();
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

template<typename T>
void vectorAppend(std::vector<T>& target, const std::vector<T>& other) {
  target.insert(target.end(), other.begin(), other.end());
}

// We'll generate a wrapper for every toplevel procedure, even if it's not
// needed, and rely on LLVM's dead value elimination to remove the cruft.
void codegenClosureWrapper(llvm::Function* F, llvm::CallingConv::ID cc,
                           llvm::GlobalValue::LinkageTypes linkage,
                           std::string symbolName, CodegenPass* pass) {
    auto FT = F->getFunctionType();
    std::vector<llvm::Type*> argTys;
    argTys.push_back(builder.getPtrTy());
    for (size_t i = 0; i < FT->getNumParams(); ++i) { argTys.push_back(FT->getParamType(i)); }
    auto FfuncT = llvm::FunctionType::get(FT->getReturnType(), argTys, false);
    std::string funcSymbolName = symbolName + ".proc";
    auto Ffunc = Function::Create(FfuncT, linkage, funcSymbolName, pass->mod);

    Ffunc->setCallingConv(parseCallingConv("fastcc"));

    Ffunc->arg_begin()->setName("env");
    pass->addEntryBB(Ffunc);
    std::vector<llvm::Value*> args;
    auto skipEnv = Ffunc->arg_begin(); skipEnv++;
    while (skipEnv != Ffunc->arg_end()) { args.push_back(&*skipEnv); ++skipEnv; }

    auto callInst = builder.CreateCall(F, args);
    callInst->setTailCall(true);
    callInst->setCallingConv(cc);

    if (callInst->getType()->isVoidTy()) {
      builder.CreateRetVoid();
    } else {
      builder.CreateRet(callInst);
    }
    pass->markFosterFunction(Ffunc);
}

void LLProc::codegenProto(CodegenPass* pass) {
  std::string symbolName = getGlobalSymbolName(this->getCName());

  llvm::FunctionType* FT = getLLVMFunctionType(this->getFnType(), symbolName);

  llvm::GlobalValue::LinkageTypes linkage = this->getFunctionLinkage();
  llvm::CallingConv::ID cc = this->type->getCallingConventionID();
  if (symbolName == kFosterMain) {
    // No args, returning void...
    FT = llvm::FunctionType::get(builder.getVoidTy(), false);
    linkage = llvm::GlobalValue::ExternalLinkage;
    cc      = llvm::CallingConv::C;
  }

  ASSERT(FT) << "expecting top-level proc to have FunctionType!";
  this->F = Function::Create(FT, linkage, symbolName, pass->mod);
  ASSERT(F) << "function creation failed for proto " << this->getName();
  ASSERT(F->getName() == symbolName) << "redefinition of function " << symbolName;

  setFunctionArgumentNames(F, this->getFunctionArgNames());

  F->setCallingConv(cc);

  codegenClosureWrapper(F, cc, linkage, symbolName, pass);
}

////////////////////////////////////////////////////////////////////

void LLProc::codegenProc(CodegenPass* pass) {
  ASSERT(this->F != NULL) << "LLModule should codegen proto for " << getName();
  pass->currentProcName = getName();

  assertRightNumberOfArgnamesForFunction(F, this->getFunctionArgNames());

  pass->addEntryBB(F);
  CodegenPass::ValueScope* scope = pass->newScope(this->getName());

  //DDiag() << "codegennign blocks for fn " << F->getName();
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
  for(auto& BB : *F) {
    ASSERT(! (BB.empty() && BB.use_empty()) );
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

Value* createUnboxedTuple(const std::vector<Value*>& vals);

llvm::Value* allocateSlot(CodegenPass* pass, LLVar* rootvar) {
  llvm::Type* ty = getLLVMType(rootvar->type);
  if (ty->isPointerTy()) {
    llvm::AllocaInst* slot = CreateEntryAlloca(ty, rootvar->getName());
    return slot;
  } else {
    // We need to wrap the non-pointer type with its metadata so the GC will
    // know how to trace the stack slot.
    CtorRepr ctorRepr; ctorRepr.smallId = -1;
    if (const StructTypeAST* sty = rootvar->type->castStructTypeAST()) {
      registerStructType(sty, "unboxed_tuple", ctorRepr, pass->mod/*, pass->datalayout*/);
    }
    llvm::GlobalVariable* typemap = pass->getTypeMapForType(rootvar->type, ctorRepr, pass->mod, NotArray);
    auto padded_ty = llvm::StructType::get(foster::fosterLLVMContext,
                                            { builder.getInt64Ty(), builder.getInt64Ty(), ty });
    llvm::AllocaInst* slot = CreateEntryAlloca(padded_ty, rootvar->getName());
    slot->setAlignment(llvm::Align(16));
    builder.CreateStore(builder.CreatePtrToInt(typemap, builder.getInt64Ty()),
                        getPointerToIndex(padded_ty, slot, builder.getInt32(1), ""));
    return getPointerToIndex(padded_ty, slot, builder.getInt32(2), "past_tymap");
  }

}

void LLProcCFG::codegenToFunction(CodegenPass* pass, llvm::Function* F) {
  pass->fosterBlocks.clear();

  // Create all the basic blocks before codegenning any of them.
  for (size_t i = 0; i < blocks.size(); ++i) {
    LLBlock* bi = blocks[i];
    pass->fosterBlocks[bi->block_id] = bi;
    bi->bb = BasicBlock::Create(builder.getContext(), bi->block_id, F);
    ASSERT(bi->block_id == bi->bb->getName().str())
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
  if (!F->arg_empty()) {
    llvm::Argument* firstArg = &*F->arg_begin();
    if (isEnvPtr(firstArg)) {
      br.args.push_back(new LLValueVar(firstArg));
    }
  }
  br.codegenTerminator(pass);

  pass->worklistBlocks.clear();
  pass->scheduleBlockCodegen(blocks[0]);
  while (!pass->worklistBlocks.empty()) {
    LLBlock* b = pass->worklistBlocks.get();
    b->codegenBlock(pass);
  }

  checkForUnusedEmptyBasicBlocks(F);

  pass->markFosterFunction(F);
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
  if (!args.empty()) { emitFakeComment(ss.str()); }
  builder.CreateBr(block->bb);
}

void LLBr::codegenTerminator(CodegenPass* pass) {
  LLBlock* block = pass->lookupBlock(this->block_id);

  if (false && this->args.empty()) {
    llvm::outs() << "{{{ Empty args!";
    llvm::outs() << "    block_id: " << block_id << "\n";
    llvm::outs() << "    parent: " <<  builder.GetInsertBlock()->getParent()->getName() << "\n";
    llvm::outs() << "}}}\n";
  }
  if (this->args.empty() && (llvm::StringRef(block_id).startswith(
                        builder.GetInsertBlock()->getParent()->getName().str())
                          || llvm::StringRef(block_id).startswith("loophdr.")
                          || llvm::StringRef(block_id).startswith("effect_handler.go")))
  { // The "first" branch into the postalloca won't pass any actual args, so we
    // want to use the "real" function args (leaving out the invariant env ptr).
    // Other branches to postalloca will pass the new values for the arg slots.
    std::vector<llvm::Value*> args;
    Function* F = builder.GetInsertBlock()->getParent();
    for (Function::arg_iterator AI = F->arg_begin(); AI != F->arg_end(); ++AI) {
      if (!isEnvPtr(&*AI)) { args.push_back(&*AI); }
    }
    passPhisAndBr(block, args);
  } else {
    passPhisAndBr(block, codegenAll(pass, this->args));
  }
}

////////////////////////////////////////////////////////////////////

void addAndEmitTo(Function* f, BasicBlock* bb) {
  f->insert(f->end(), bb);
  builder.SetInsertPoint(bb);
}

ConstantInt* getTagForCtorId(const CtorId& c) {
         if (c.typeName == "Bool")  { return builder.getInt1( c.ctorRepr.smallId);
  } else if (c.typeName == "Int16") { return builder.getInt16(c.ctorRepr.smallId);
  } else if (c.typeName == "Int32") { return builder.getInt32(c.ctorRepr.smallId);
  } else if (c.typeName == "Int64") { return builder.getInt64(c.ctorRepr.smallId);
  } else if (c.typeName == "Word")  { return is32Bit()
                                           ? builder.getInt32(c.ctorRepr.smallId)
                                           : builder.getInt64(c.ctorRepr.smallId);
  } else                            { return builder.getInt8( c.ctorRepr.smallId); }
}

llvm::Value* emitCallGetCtorIdOf(CodegenPass* pass, llvm::Value* v) {
  llvm::Function* foster_ctor_id_of = pass->mod->getFunction("foster_ctor_id_of");
  ASSERT(foster_ctor_id_of != NULL);
  return builder.CreateCall(from(foster_ctor_id_of), { v });
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
        << "switch case and inspected value had different types!\n"
        << "SwitchCase ctor " << (i+1) << " of " << sw->ctors.size()
           << ": " << c.typeName << "." << c.ctorName << "#" << c.ctorRepr.smallId
        << "\ncond type: " << str(si->getCondition()->getType())
                      << "; val type: " << str(onVal->getType());

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

llvm::Value* emitTagOfValue(CodegenPass* pass, llvm::Value* inspected,
                            CtorTagRepresentation ctr) {
  switch (ctr) {
  case CTR_BareValue: return inspected;
  case CTR_OutOfLine: return emitCallGetCtorIdOf(pass, inspected);
  case CTR_MaskWith3: {
    llvm::Value* truncated = builder.CreatePtrToInt(inspected, builder.getInt8Ty());
                      return builder.CreateAnd(truncated, 0x7); }
  }
  ASSERT(false) << "unknown tag representation in LLSwitch::codegen!"; return NULL;
}

void LLSwitch::codegenTerminator(CodegenPass* pass) {
  ASSERT(ctors.size() == blockids.size());
  ASSERT(ctors.size() >= 1);

  llvm::Value* inspected = this->var->codegen(pass);
  codegenSwitch(pass, this, emitTagOfValue(pass, inspected, this->ctr));
}

///}}}//////////////////////////////////////////////////////////////

llvm::Value* LLBitcast::codegen(CodegenPass* pass) {
  llvm::Value* v = var->codegen(pass);
  llvm::Type* tgt = getLLVMType(this->type);
  if (v->getType()->isVoidTy() && tgt->isPointerTy()) {
    // Can't cast a void value to a unit value,
    // but we can manufacture a unit ptr...
    return llvm::ConstantPointerNull::getNullValue(tgt);
  } else return v;
}

void LLRebindId::codegenMiddle(CodegenPass* pass) {
  pass->insertScopedValue(from, to->codegen(pass));
}

////////////////////////////////////////////////////////////////////
/////////////// LLDeref, LLStore, LLLetVals ////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* emitGCRead(CodegenPass* pass, Value* base, Type* slotty, Value* slot) {
  return emitNonVolatileLoad(slotty, slot, "deref");
}

llvm::Value* LLDeref::codegen(CodegenPass* pass) {
  llvm::Value* ptr = base->codegen(pass);
  ASSERT(this->type) << "LLDeref was missing its type...\n";
  if (isTraced && !llvm::isa<llvm::AllocaInst>(ptr)) {
    return emitGCRead(pass, nullptr, getLLVMType(this->type), ptr);
  } else {
    return emitNonVolatileLoad(getLLVMType(this->type), ptr, "deref");
  }
}

llvm::Value* LLStore::codegen(CodegenPass* pass) {
  llvm::Value* val  = v->codegen(pass);
  llvm::Value* slot = r->codegen(pass);
  if (isTraced) {
    return emitGCWrite(pass, val, slot, slot);
  } else {
    return emitStore(pass, val, slot, slot, WriteKnownNonGC);
  }
}

////////////////////////////////////////////////////////////////////

void trySetName(llvm::Value* v, const string& name) {
  if (v->getType()->isVoidTy()) {
    // Can't assign a name to void values in LLVM.
  } else if (llvm::isa<llvm::Function>(v)) {
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
  llvm::Type* r = getLLVMType(retType);
  llvm::Type* a = getLLVMType(typeArg);
  if (this->primName == "coro_yield") { return pass->emitCoroYieldFn(r, a); }
  if (this->primName == "coro_invoke") { return pass->emitCoroInvokeFn(r, a); }
  if (this->primName == "coro_create") { return pass->emitCoroCreateFn(retType, typeArg); }
  if (this->primName == "coro_isdead") { 
    return pass->mod->getFunction("foster_coro_isdead");
  }
  if (this->primName == "coro_parent") {
    auto fn = Function::Create(
      /*Type=*/    llvm::FunctionType::get(
                    /*Result=*/   getHeapPtrTo(foster_generic_coro_t),
                    /*Params=*/   { },
                    /*isVarArg=*/ false),
      /*Linkage=*/ llvm::GlobalValue::InternalLinkage,
      /*Name=*/    ".coro_parent", pass->mod);

    fn->setCallingConv(llvm::CallingConv::Fast);
    pass->markFosterFunction(fn);

      
    BasicBlock* prevBB = builder.GetInsertBlock();
    pass->addEntryBB(fn);
    builder.CreateRet(pass->getCurrentCoroParent());
    if (prevBB) {
      builder.SetInsertPoint(prevBB);
    }

    return fn;
  }
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

llvm::Constant* emitConstantArrayTidy(uint64_t size,
                                      llvm::Constant* arrValues) {
    std::vector<llvm::Constant*> tidy_vals;
    tidy_vals.push_back(llvm::ConstantInt::get(builder.getInt64Ty(), size));
    tidy_vals.push_back(arrValues);
    return llvm::ConstantStruct::getAnon(tidy_vals);
}

llvm::GlobalVariable* emitPrivateGlobal(CodegenPass* pass,
                                 llvm::Constant* val,
                                 const std::string& name) {  
  llvm::GlobalVariable* globalVar = new llvm::GlobalVariable(
      /*Module=*/      *(pass->mod),
      /*Type=*/        val->getType(),
      /*isConstant=*/  true,
      /*Linkage=*/     llvm::GlobalValue::PrivateLinkage,
      /*Initializer=*/ val,
      /*Name=*/        name);
  globalVar->setAlignment(llvm::MaybeAlign(16));
  return globalVar;
}


llvm::Constant* mkGlobalArrayCellConstant(CodegenPass* pass,
                                     llvm::GlobalVariable* typemap,
                                     llvm::Constant* body) {
  std::vector<llvm::Constant*> cell_vals;
  std::vector<llvm::Constant*> pad_vals;
  if (is32Bit()) {
    pad_vals.push_back(builder.getInt64(0)); // alignment padding
    pad_vals.push_back(typemap);
    pad_vals.push_back(builder.getInt32(0)); // padding for typemap
  } else {
    pad_vals.push_back(builder.getInt64(0)); // alignment padding
    pad_vals.push_back(typemap);
  }
  cell_vals.push_back(llvm::ConstantStruct::getAnon(pad_vals));
  cell_vals.push_back(body);
  return llvm::ConstantStruct::getAnon(cell_vals);
}

llvm::Constant* mkGlobalNonArrayCellConstant(CodegenPass* pass,
                                     llvm::GlobalVariable* typemap,
                                     llvm::Constant* body) {
  std::vector<llvm::Constant*> cell_vals;
  cell_vals.push_back(builder.getInt64(0));
  cell_vals.push_back(typemap);
  cell_vals.push_back(body);
  return llvm::ConstantStruct::getAnon(cell_vals);
}

// Returns a tidy pointer.
llvm::Value* emitByteArray(CodegenPass* pass, llvm::StringRef bytes, llvm::StringRef cellname) {
  auto const_arr_tidy = emitConstantArrayTidy(bytes.size(), getConstantArrayOfString(bytes));

  CtorRepr ctorRepr; ctorRepr.smallId = -1;
  auto typemap = pass->getTypeMapForType(TypeAST::i(8), ctorRepr, pass->mod, YesArray);
  auto arrayGlobalConstant = mkGlobalArrayCellConstant(pass, typemap, const_arr_tidy);
  auto arrayGlobal = emitPrivateGlobal(pass, arrayGlobalConstant, cellname.str());

  return getPointerToIndex(arrayGlobalConstant->getType(), arrayGlobal, builder.getInt32(1), "cellptr");
}

llvm::Value* LLText::codegen(CodegenPass* pass) {
  Value* hstr = emitByteArray(pass, this->stringValue, ".txt_cell");
  llvm::FunctionCallee textfragment = pass->lookupFunctionOrDie("TextFragment");
  auto call = builder.CreateCall(textfragment,
                     { hstr, builder.getInt32(this->stringValue.size()) });
  call->setCallingConv(parseCallingConv("fastcc"));
  return call;
}

llvm::Value* LLValueVar::codegen(CodegenPass* pass) {
  return this->val;
}

llvm::Value* LLGlobalSymbol::codegen(CodegenPass* pass) {
  // Closure conversion emits variables with procedure type; we'd be quite
  // remiss to use the nullary global closure wrapper instead of the proc!
  bool isProc = NULL != this->type->castFnTypeAST();

  if (auto v = pass->autoDerefs[this->name]) {
    return builder.CreateLoad(getLLVMType(this->type), v, this->name);
  }

  auto v = pass->globalValues[this->name];
  if (!v || isProc) {
    if (!v) llvm::errs() << "falling back to global proc instead of closure for " << this->name << "\n";
    v = pass->lookupFunctionOrDie(this->name).getCallee();
  }
  return v;
}


llvm::Value* LLGlobalSymbol::codegenCallee(CodegenPass* pass) {
  // But if we know we're codegenning for a call site, we can use the global
  // procedure directly, instead of its closure wrapper.
  return pass->lookupFunctionOrDie(this->name).getCallee();
}

llvm::Value* LLVar::codegen(CodegenPass* pass) {
  llvm::Value* v = pass->valueSymTab.lookup(getName());
  if (!v) {
    llvm::errs() << builder.GetInsertBlock()->getParent() << "\n";
    pass->valueSymTab.dump(llvm::errs());
    ASSERT(false) << "\n\n\t\tUnknown variable name " << this->name << " in CodegenPass"
                  << " in block " << builder.GetInsertBlock()->getName()
                  << " of function " << pass->currentProcName;
  }
  return v;
}

// APInt's toString() method doesn't implement base 256 conversion.
// The returned bytes are "reversed", with the least significant
// stored at index zero, instead of the most significant.
std::string APInt_toBase256_lsb0(llvm::APInt tmp) {
  std::string rv;
  while (tmp.getBoolValue()) {
    uint8_t digit = uint8_t(tmp.getRawData()[0]);
    rv.push_back(digit);
    tmp.lshrInPlace(8);
  }
  return rv;
}

llvm::Value* LLInt::codegen(CodegenPass* pass) {
  ASSERT(this->type && getLLVMType(this->type));
  llvm::Type* ty = getLLVMType(this->type);
  auto arb = this->getAPInt();

  // Our type could be an LLVM type, or an arbitrary precision int type.

  // Common case: small fixnums.
  if (ty->isIntegerTy()) {
    return ConstantInt::get(ty, arb);
  }

  int targetWidth = getWordTySize(); // TODO be less conservative
  llvm::Type* targetTy = getWordTy(builder);

  if (arb.isSignedIntN(targetWidth - 1)) {
    // Small integer constants can be constructed cheaply by tagging a machine word.
    auto small = ConstantInt::getSigned(targetTy, arb.getSExtValue());
    return createIntOfSmall(builder, small);
  } else {
    // Large integer constants must be initialized from binary data.
    std::string bytes = APInt_toBase256_lsb0(arb);
    Value* base256 = emitByteArray(pass, bytes, ".intlit_");
    Function* Int_ofBase256 = pass->mod->getFunction("Int-ofBase256");
    ASSERT (Int_ofBase256) << "Arbitrary-precision integers need a constructor in scope!" << "\n"
                           << "\n"
                           << "Try importing \"prelude/int\"."
                           << "\n";
    auto call = builder.CreateCall(from(Int_ofBase256), { base256, builder.getInt1(this->negated) });
    call->setCallingConv(parseCallingConv("fastcc"));
    return call;
  }

}

llvm::Value* LLKillProcess::codegen(CodegenPass* pass) {
  emitFosterAssert(pass->mod, builder.getFalse(), this->stringValue.c_str());
  return llvm::UndefValue::get(getLLVMType(this->type));
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLAllocate ////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

Value* allocateCell(CodegenPass* pass, TypeAST* type,
                    LLAllocate::MemRegion region,
                    CtorRepr ctorRepr, std::string typedesc,
                    SourceLoc loc, bool init) {
  llvm::Type* ty = getLLVMType(type);

  switch (region) {
  case LLAllocate::MEM_REGION_STACK: {
    // TODO We could optimize the treatment of stack-allocated pointer-free data
    // by *not* using a gcroot, and allocating a slot instead of a cell (i.e. no
    // type map).

    //ASSERT(!containsGCablePointers(type, ty));

    // We enforce the invariant that the GC will scan but not attempt to copy
    // stack-allocated cells to the heap, by marking stack memory regions
    // as "stable" in foster_gc.cpp.
    llvm::GlobalVariable* ti = pass->getTypeMapForType(type, ctorRepr, pass->mod, NotArray);
    llvm::Type* typemap_type = ti->getType();
    // We include padding in order for the padding plus the typemap pointer to
    // be 16 bytes wide. This, in turn, ensures that we will align the payload
    // field to the necessary 16 bytes as well.
    // Also, because the heap_cell type in foster_gc_utils effectively treats
    // the header as a union of a pointer with uint64_t, we must include padding
    // after the typemap if the pointer is 32 bits.
    int ptrsize = builder.GetInsertBlock()->getModule()->getDataLayout().getPointerSize();
    llvm::Type* pad8 = llvm::ArrayType::get(builder.getInt8Ty(), 8);
    llvm::Type* pad  = llvm::ArrayType::get(builder.getInt8Ty(), 8 - ptrsize);
    llvm::StructType* sty = llvm::StructType::get(builder.getContext(), { pad8, typemap_type, pad, ty });
    llvm::AllocaInst* cell = CreateEntryAlloca(sty, "stackref");
    cell->setAlignment(llvm::Align(16));
    llvm::Value* slot = getPointerToIndex(sty, cell, builder.getInt32(3), "stackref_slot");
    builder.CreateStore(ti, getPointerToIndex(sty, cell, builder.getInt32(1), "stackref_meta"));
    return slot;
  }
  case LLAllocate::MEM_REGION_GLOBAL_HEAP: {
    std::string s;
    std::stringstream ss(s);
    ss << loc.file << ":" << loc.line << ":" << loc.col;
    return pass->emitMalloc(type, ctorRepr, typedesc, ss.str(), init);
  }

  default:
    ASSERT(false); return NULL;
  }
}

llvm::Value* emitNullaryCtor(CtorRepr ctorRepr, llvm::Type* ptrty) {
  llvm::Value* val = builder.getInt8(ctorRepr.smallId);
  return builder.CreateIntToPtr(val, ptrty);
}

// If we represent a constant array as a globally-allocated/static value,
// we simply won't call this function.
llvm::Value* LLAllocate::codegen(CodegenPass* pass) {
  if (this->arraySize != NULL) {
    Value* array_size = this->arraySize->codegen(pass);
    return pass->emitArrayMalloc(this->type, array_size, this->zero_init);
  } else {
    if (const StructTypeAST* sty = this->type->castStructTypeAST()) {
      registerStructType(const_cast<StructTypeAST*>(sty),
                         this->type_name, this->ctorRepr, pass->mod/*, pass->datalayout*/);
    }
    if (this->ctorRepr.isNullary) {
      emitFakeComment("nullary ctor!");
      return emitNullaryCtor(this->ctorRepr, getHeapPtrTo(getLLVMType(this->type)));
      // return null pointer, or'ed with ctor smallId, bitcast to appropriate result.
    } else {
      return allocateCell(pass, this->type, this->region, this->ctorRepr,
                                this->typedesc, this->loc, this->zero_init);
    }
  }
}

///}}}//////////////////////////////////////////////////////////////
//////////////// Arrays ////////////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

bool tryBindArray(CodegenPass* pass, llvm::Type* sty, llvm::Value* base, Value*& arr, Value*& len) {
  // {i64, [0 x T]}*
  if (base->getType()->isPointerTy()) {
    if (sty->getNumContainedTypes() == 2
      && sty->getContainedType(0) == builder.getInt64Ty()) {
      if (llvm::isa<llvm::ArrayType>(sty->getContainedType(1))) {
        arr = getPointerToIndex(sty, base, builder.getInt32(1), "arr");
        len = getElementFromComposite(pass, sty, base, 0, "len");
        return true;
      }
    }
  }
  return false;
}

Value* getArraySlot(Value* base, Value* idx, CodegenPass* pass, Type* ty,
                    bool dynCheck, const std::string& srclines) {
  Value* arr = NULL; Value* len;

  auto arrayType = ArrayTypeAST::getSizedArrayType(ty, 0);

  if (tryBindArray(pass, arrayType, base, arr, len)) {
    if (dynCheck && !pass->config.disableAllArrayBoundsChecks) {
      emitFosterArrayBoundsCheck(pass->mod, idx, len, srclines);
    }
    ASSERT(idx->getType() != llvm::Type::getInt1Ty(builder.getContext()))
      << "Indexing using a boolean subscript is probably not what you want!";
    return getPointerToIndex(arrayType->getContainedType(1), arr, idx, "arr_slot");
  } else {
    ASSERT(false) << "expected array, got " << str(base);
    return NULL;
  }
}


llvm::Value* LLArrayIndex::codegenARI(CodegenPass* pass, Value** outbase, Type* ty) {
  *outbase    = this->base ->codegen(pass);
  Value* idx  = this->index->codegen(pass);
  idx = builder.CreateZExt(idx, llvm::Type::getInt64Ty(builder.getContext()));
  ASSERT(static_or_dynamic == "static" || static_or_dynamic == "dynamic");
  return getArraySlot(*outbase, idx, pass, ty,
                      this->static_or_dynamic == "dynamic", this->srclines);
}

llvm::Value* LLArrayRead::codegen(CodegenPass* pass) {
  ASSERT(this->type) << "LLArrayRead with no type?";

  Type* ty = getLLVMType(this->type);
  Value* base = NULL;
  Value* slot = ari->codegenARI(pass, &base, ty);
  //Value* val  = emitGCRead(pass, base, slot);
  Value* val  = emitNonVolatileLoad(ty, slot, "arrayslot");
  return val;
}

  // base could be an array a[i] or a slot for a reference variable r.
  // a[i] should codegen to &a[i], the address of the slot in the array.
  // r    should codegen to the contents of the slot (the ref pointer value),
  //        not the slot address.

llvm::Value* LLArrayPoke::codegen(CodegenPass* pass) {
  Value* val  = this->value->codegen(pass);
  Value* base = NULL;
  Value* slot = ari->codegenARI(pass, &base, val->getType());

  emitGCWriteOrStore(pass, val, base, slot);
  return getNullOrZero(builder.getPtrTy());
}


llvm::Value* LLArrayLength::codegen(CodegenPass* pass) {
  Value* val  = this->value->codegen(pass);
  auto ety = getLLVMType(this->type);
  auto sty = ArrayTypeAST::getSizedArrayType(ety, 0);
  Value* _bytes; Value* len;
  if (tryBindArray(pass, sty, val, /*out*/ _bytes, /*out*/ len)) {
    // len already assigned.
  } else { ASSERT(false); }
  return len;
}

llvm::Value* LLByteArray::codegen(CodegenPass* pass) {
  return emitByteArray(pass, this->bytes, ".bytes_cell");
}

llvm::Value* LLArrayLiteral::codegen(CodegenPass* pass) {
  // Allocate a global array, with zeros/nulls for non-literal elements.
  //
  std::vector<llvm::Constant*> vals;
  std::vector<std::pair<llvm::Value*, unsigned> > ncvals;
  llvm::Type* elt_ty = getLLVMType(this->elem_type);
  
  for (unsigned i = 0; i < this->args.size(); ++i) {
    llvm::Value* v = this->args[i]->codegen(pass);
    if (llvm::Constant* c = llvm::dyn_cast<llvm::Constant>(v)) {
      vals.push_back(c);
    } else {
      vals.push_back(getNullOrZero(elt_ty));
      ncvals.push_back(std::make_pair(v, i));
    }
  }
  llvm::ArrayType* ty = llvm::ArrayType::get(elt_ty, vals.size());
  llvm::Constant* const_arr = llvm::ConstantArray::get(ty, vals);

  bool isImmutable = false;

  llvm::errs() << "LLArrayLiteral elt_ty = " << str(elt_ty) << "\n";

  // If there are no non-constant values, then the array can be
  // allocated globally instead of on the heap, and we won't need
  // to copy any values.
  if (!arr || (ncvals.empty() && isImmutable)) {
    auto const_arr_tidy = emitConstantArrayTidy(vals.size(), const_arr);

    CtorRepr ctorRepr; ctorRepr.smallId = -1;
    auto typemap = pass->getTypeMapForType(this->elem_type, ctorRepr, pass->mod, YesArray);
    auto arrayGlobalConstant = mkGlobalArrayCellConstant(pass, typemap, const_arr_tidy);
    auto arrayGlobal = emitPrivateGlobal(pass, arrayGlobalConstant, ".arr_cell");

    return getPointerToIndex(arrayGlobalConstant->getType(), arrayGlobal, builder.getInt32(1), "cellptr");
  } else {
    llvm::GlobalVariable* arrayGlobal = emitPrivateGlobal(pass, const_arr, ".arr");

    // Load the heap array which our forebears allocated unto us.
    llvm::Value* heap_arr = this->arr->codegen(pass);
    auto arrty = ArrayTypeAST::getSizedArrayType(elt_ty, 0);

    Value* heapmem; Value* _lenx;
    if (tryBindArray(pass, arrty, heap_arr, /*out*/ heapmem, /*out*/ _lenx)) {
      MEMCPY_FROM_GLOBAL_TO_HEAP++;
      // Memcpy from global to heap.

      int64_t size_in_bytes = pass->mod->getDataLayout().getTypeAllocSize(elt_ty)
                                  * int64_t(this->args.size());
      
      builder.CreateMemCpy(heapmem, llvm::MaybeAlign(1),
                           arrayVariableToPointer(arrayGlobal), llvm::MaybeAlign(1),
                           size_in_bytes);

      // Copy any non-constant values to the heap array
      //
      llvm::Type* i32 = builder.getInt32Ty();
      for (unsigned i = 0; i < ncvals.size(); ++i) {
        unsigned k  = ncvals[i].second;
        Value* val  = ncvals[i].first;
        Value* slot = getPointerToIndex(ty, heapmem, llvm::ConstantInt::get(i32, k), "arr_slot");
        bool useBarrier = val->getType()->isPointerTy();
        //maybeEmitCallToLogPtrWrite(pass, slot, val, useBarrier);
        if (useBarrier) {
          emitGCWrite(pass, val, heapmem, slot);
        } else {
          builder.CreateStore(val, slot, /*isVolatile=*/ false);
        }
      }
    } else { ASSERT(false); }

    return heap_arr;
  }
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLRecordIndex /////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

Value* LLRecordIndex::codegen(CodegenPass* pass) {
  Value* val = this->base->codegen(pass);
  Type* ty = getLLVMType(this->type);
  if (auto t = this->type->castPtrTypeAST()) {
    ty = getLLVMType(t->getElementTypeC());
  }
  llvm::outs() << "LLRecordIndex: offset" << this->offset << " ; val " << str(val) << "; ty = " << str(this->type) << "\n";
  if (this->offset >= 0) {
    bool assumeImmutable = false;
    return getElementFromComposite(pass, ty, val, this->offset, "rcd-idx", assumeImmutable);
  } else {
    llvm::errs() << "WARNING: record index with negative offset!" << "\n";
    return val;
  }
}

///}}}//////////////////////////////////////////////////////////////
//////////////// LLTupleStore //////////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLUnitValue::codegen(CodegenPass* pass) {
  return getUnitValue();
}

void copyValuesToStruct(CodegenPass* pass,
                        const std::vector<llvm::Value*>& vals,
                        llvm::Value* tup_ptr) {
  ASSERT(tup_ptr != NULL);

  std::vector<llvm::Type*> tys;
  for (auto v : vals) { tys.push_back(v->getType()); }
  auto tupty = llvm::StructType::get(builder.getContext(), tys);

  for (size_t i = 0; i < vals.size(); ++i) {
    Value* dst = builder.CreateConstGEP2_32(tupty, tup_ptr, 0, i, "gep");
    emitStore(pass, vals[i], dst, tup_ptr, WriteUnspecified);
  }
}

void LLTupleStore::codegenMiddle(CodegenPass* pass) {
  if (vars.empty()) return;
  llvm::Value* tup_ptr = this->storage->codegen(pass);
  copyValuesToStruct(pass, codegenAll(pass, this->vars), tup_ptr);
}

Value* createUnboxedTuple(const std::vector<Value*>& vals) {
  std::vector<llvm::Constant*> undefs;
  for (auto val : vals) { undefs.push_back(llvm::UndefValue::get(val->getType())); }
  // Rather than copying values to memory with GEP + store,
  // we "copy" values to a struct value which starts out with undef members.
  Value* rv = llvm::ConstantStruct::getAnon(undefs);
  for (size_t i = 0; i < vals.size(); ++i) { rv = builder.CreateInsertValue(rv, vals[i], i); }
  return rv;
}

Value* LLUnboxedTuple::codegen(CodegenPass* pass) {
  if (this->isStatic) {
    if (this->vars.empty()) {
        return getUnitValue();
    } else {
        std::vector<llvm::Constant*> consts;
        for (auto v : this->vars) {
          auto gv = pass->globalValues[v->getName()];
          if (auto cgv = dyn_cast<llvm::Constant>(gv)) {
            consts.push_back(cgv);
          } else {
            llvm::errs() << "var  " << v->getName() << " was not constant! ... " << *gv << "\n";
            exit(2);
          }
        }

        auto ct = llvm::ConstantStruct::getAnon(consts);
        CtorRepr ctorRepr; ctorRepr.smallId = 126;
        // TODO merge type maps for similar types?
        
        std::vector<int> noSkippedIndices;
        registerStructType(this->type->castStructTypeAST(), "cstupty", ctorRepr, pass->mod/*, pass->datalayout*/);
        auto typemap = pass->getTypeMapForType(this->type, ctorRepr, pass->mod, NotArray);
        auto globalCellConstant = mkGlobalNonArrayCellConstant(pass, typemap, ct);
        auto globalCell = emitPrivateGlobal(pass, globalCellConstant, "cstup");
        return builder.CreateConstGEP2_32(globalCellConstant->getType(), globalCell, 0, 2);
    }
  } else {
    return createUnboxedTuple(codegenAll(pass, this->vars));
  }
}


Value* LLGlobalAppCtor::codegen(CodegenPass* pass) {
  llvm::Type* ty = getLLVMType(this->type);
  llvm::errs() << "LLGlobalAppCtor ty = " << str(ty) << "\n";
  if (this->args.empty()) {
    return emitNullaryCtor(this->ctor.ctorId.ctorRepr, ty);
  }

  std::vector<llvm::Constant*> consts;
  for (auto v : this->args) {
    auto gv = pass->globalValues[v->getName()];
    if (!gv) {
      gv = pass->globalValues[v->getName() + ".closure.cell"];
    }
    if (gv) {
      if (auto cgv = dyn_cast<llvm::Constant>(gv)) {
        consts.push_back(cgv);
      } else {
        llvm::errs() << "var  " << v->getName() << " was not constant! ... " << *gv << "\n";
        exit(2);
      }
    } else {
      llvm::errs() << "var  " << v->getName() << " wasn't found in pass->globalValues[]!\n";
      exit(2);
    }
  }

  llvm::GlobalVariable* ti = pass->getTypeMapForType(type, this->ctor.ctorId.ctorRepr, pass->mod, NotArray);
  auto ct = llvm::ConstantStruct::getAnon(consts);
  auto globalCellConstant = mkGlobalNonArrayCellConstant(pass, ti, ct);
  auto globalCell = emitPrivateGlobal(pass, globalCellConstant, "csctor");
  return builder.CreateConstGEP2_32(globalCellConstant->getType(), globalCell, 0, 2);
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
      if (!v->getType()->isPointerTy()) {
        const CtorRepr& r = ctors[i].ctorId.ctorRepr;
        if (r.isTransparent && !r.isBoxed) {
        } else {
          EDiag() << "not bitcasting for occ with repr " << str(ctors[i].ctorId.ctorRepr) << " because of type mismatch between"
                  << str(v) << " :: " << str(v->getType()) << " and ptr to " << str(ctors[i].ctorStructType);
        }
      }
    }

    if (ctors[i].ctorId.ctorRepr.isTransparent && ctors[i].ctorId.ctorRepr.isBoxed) {
      emitFakeComment("eliding dereference due to transparent ctor representation of " + ctors[i].ctorId.ctorName);
      continue;
    }

    llvm::Type* ty = getLLVMType(ctors[i].ctorStructType);
    v = getElementFromComposite(pass, ty, v, offsets[i], "switch_insp");
  }

  // Consider code like         case v of Some x -> ... x ...
  // when there's a type definition Maybe a = None | Some a.
  // v's source type is Maybe X, which (since we erase type parameters)
  // corresponds to the LLVM type Maybe.DT*. This will be refined to
  // { i999* }* when computing the occurrence for x. But x's physical type then
  // remains i999*, while it ought to be the translation of its source type, X.
  // This bitcast fixes the mismatch.
  //return emitBitcast(v, getLLVMType(this->type), "occty");
  return v;
}

///}}}//////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//////////////// Term Application //////////////////////////////////
/////////////////////////////////////////////////////////////////{{{

llvm::Value* LLCallPrimOp::codegen(CodegenPass* pass) {
  if (this->op == "lookup_handler_for_effect") {
    // Special cased because it's the only operation that needs tag.
    llvm::Function* fn = pass->mod->getFunction("foster__lookup_handler_for_effect");
    ASSERT(fn != NULL) << "NO foster__lookup_handler_for_effect IN MODULE! :(";

    llvm::ArrayRef<Value*> args = { builder.getInt64(this->tag) };
    llvm::CallInst* handler = builder.CreateCall(from(fn), args, "handler");
    return handler;
  }
  return pass->emitPrimitiveOperation(this->op, builder, this->type,
                                      codegenAll(pass, this->args));
}

llvm::Value* LLCallInlineAsm::codegen(CodegenPass* pass) {
  auto vs = codegenAll(pass, this->args);
  auto iasm = llvm::InlineAsm::get(this->ty->getLLVMFnType(),
                                   this->asmString,
                                   this->constraints,
                                   this->hasSideEffects);
  return builder.CreateCall(iasm, llvm::ArrayRef(vs), "asmres");
}

llvm::FunctionType* getClosureFnType(llvm::Type* retTy, const std::vector<Value*>& nonEnvArgs) {
  std::vector<llvm::Type*> argTys;
  argTys.push_back(builder.getPtrTy());
  for (auto arg : nonEnvArgs) { argTys.push_back(arg->getType()); }
  return llvm::FunctionType::get(retTy, argTys, false);
}

llvm::StructType* getClosureTypeForFn(llvm::FunctionType* fnty) {
  return llvm::StructType::get(foster::fosterLLVMContext,
              { rawPtrTo(fnty), builder.getPtrTy() });
}

llvm::Value* LLCall::codegen(CodegenPass* pass) {
  ASSERT(base != NULL) << "unable to codegen call due to null base";
  Value* FV = base->codegenCallee(pass);
  ASSERT(FV) << "unable to codegen call due to missing value for base";

  llvm::FunctionType* FT = NULL;
  std::vector<Value*> valArgs;
  bool fromClosure = false;

  llvm::CallingConv::ID callingConv = parseCallingConv(this->callconv);

  std::vector<Value*> nonEnvArgs;
  // Collect the args, performing coercions if necessary.
  for (auto arg : this->args) {
    nonEnvArgs.push_back(arg->codegen(pass));
  }

  if (Function* F = llvm::dyn_cast<Function>(FV)) {
    // Call to top level function
    callingConv = F->getCallingConv();
    FT = F->getFunctionType();
  //} else if (isFunctionPointerTy(FV->getType())) {
  //  FT = llvm::dyn_cast<llvm::FunctionType>(FV->getType()->getContainedType(0));
  } else {
    ASSERT (this->base->type != nullptr) << "missing base type for call to " << str(FV) << "; base tag = " << base->tag;
    if (auto t = this->base->type->castPtrTypeAST()) {
      if (auto sty = t->getElementTypeC()->castStructTypeAST()) {
        auto cloty = getLLVMType(sty);
        // Load code and env pointers from closure...
        llvm::Value* envPtr =
            getElementFromComposite(pass, cloty, FV, 1, "getCloEnv");
        FV = getElementFromComposite(pass, cloty, FV, 0, "getCloCode", true);

        auto subty = sty->getContainedType(0);
        if (auto fnty = subty->castFnTypeAST()) {
          FT = fnty->getLLVMFnType();  
        } else {
          ASSERT(false) << "unable to codegen call due to non-function type for base";
        }

        // Pass env pointer as first parameter to function.
        valArgs.push_back(envPtr);
        fromClosure = true;
      } else {
        FT = getClosureFnType(getLLVMType(this->type), nonEnvArgs);
        auto cloty = getClosureTypeForFn(FT);
        llvm::errs() << "NOTE: base type was non-struct; " << str(t->getElementTypeC())
                     << " ;; so using instead synthesized FT = " << str(FT) << "\n";
        llvm::errs() << "cloty = " << str(cloty) << "\n"; 
        //llvm::errs() << "this->type = " << str(this->type) << "\n";
        llvm::errs() << "getLLVMType(this->type) = " << str(getLLVMType(this->type)) << "\n";

        // Load code and env pointers from closure...
        llvm::Value* envPtr =
            getElementFromComposite(pass, cloty, FV, 1, "getCloEnv");
        FV = getElementFromComposite(pass, cloty, FV, 0, "getCloCode", true);

        // Pass env pointer as first parameter to function.
        valArgs.push_back(envPtr);
        fromClosure = true;
      }
    } else {
      ASSERT(false) << "unable to codegen call of " << str(FV) << " due to non-ref type " << str(this->type);
    }
  }

  if (pass->config.countClosureCalls && fromClosure) {
    auto f  = pass->mod->getFunction("foster__record_closure_call");
    auto ci = builder.CreateCall(f);
  }

  assertHaveCallableType(base, FT, FV);

  // Collect all args, performing coercions if needed.
  for (auto arg : nonEnvArgs) {
    llvm::Type* expectedType = FT->getParamType(valArgs.size());
    llvm::Value* argV = substituteUnitForVoid(arg);
    assertValueHasExpectedType(argV, expectedType, FV);
    valArgs.push_back(argV);
  }

  assertRightNumberOfArgsForFunction(FV, FT, valArgs);

  // Give the instruction a name, if we can...

  auto callInst = builder.CreateCall(llvm::FunctionCallee(FT, FV),
                                     llvm::ArrayRef(valArgs));
  callInst->setCallingConv(callingConv);
  trySetName(callInst, "calltmp");

  // See CapnpIL.hs for a note on tail call marker safety.
  if (this->okToMarkAsTailCall && callingConv == llvm::CallingConv::Fast) {
    callInst->setTailCall(true);
  }

  return callInst;
}

/// }}}

