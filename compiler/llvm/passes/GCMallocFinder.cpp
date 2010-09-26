// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/LLVMContext.h"
#include "llvm/Instructions.h"

#include "llvm/CallGraphSCCPass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/System/TimeValue.h"

#include "base/GenericGraph.h"
#include "parse/FosterUtils.h"

#include <set>
#include <map>
#include <string>

using namespace llvm;

// This pass examines the LLVM call graph to determine
// which functions might lead to garbage collection.
// Calls which cannot lead to GC may be optimized more
// heavily than those which may.
// Specifically, only calls which may trigger GCs
// force pointers to be stored in gcroot-marked stack
// slots.

// TODO better handling of SCCs of size > 1
// TODO export this information!
// TODO have gcroot-improver use this information.

namespace {
struct GCMallocFinder : public CallGraphSCCPass {
  static char ID;
  GCMallocFinder() : CallGraphSCCPass(ID) {}

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }

  virtual bool doInitialization(CallGraph &CG) {
    knownNonAllocatingFQNames.insert("print_i32");
    knownNonAllocatingFQNames.insert("expect_i32");
    knownNonAllocatingFQNames.insert("print_i1");
    knownNonAllocatingFQNames.insert("expect_i1");
    knownNonAllocatingFQNames.insert("read_i32");
    knownNonAllocatingFQNames.insert("mp_int_zero");
    knownNonAllocatingFQNames.insert("mp_int_clear");
    knownNonAllocatingFQNames.insert("mp_int_init_value");

    return false;
  }

  virtual bool doFinalization(CallGraph &CG) {
    return false;
  }

  enum GCMallocStatus {
    kStatusUnknownGCBehavior,
    kStatusWillNotTriggerGC,
    kStatusMayTriggerGC
  };

  std::set<std::string> knownNonAllocatingFQNames;

  bool isKnownNotToAllocate(Function* fn) {
    static std::map<Function*, GCMallocStatus> cache;
    GCMallocStatus status = cache[fn];
    if (status == kStatusUnknownGCBehavior) {
      status = kStatusMayTriggerGC;
      if (knownNonAllocatingFQNames.count(fn->getNameStr()) == 1
       || fn->isIntrinsic()) {
        status = kStatusWillNotTriggerGC;
      }
      cache[fn] = status;
    }
    return status == kStatusWillNotTriggerGC;
  }

  std::map<const CallGraphNode*, GCMallocStatus> cgnStatus;

  std::string callGraphNodeFuncName(const CallGraphNode* cgn) {
    Function* fn = cgn->getFunction();
    std::string fnName = fn ? "<unknown function>" : "<NULL fn!>";
    if (fn && fn->hasName()) {
      fnName = fn->getNameStr();
    }
    return fnName;
  }

  virtual bool runOnSCC(CallGraphSCC& scc) {
    std::vector<CallGraphNode::CallRecord> callsToMark;

    for (CallGraphSCC::iterator sccit = scc.begin(), sccend = scc.end();
                        sccit != sccend; ++sccit) {
       const CallGraphNode* cgn = *sccit;
       if (!cgn) { continue; }

       Function* fn = cgn->getFunction();

       if (!fn) {
         // There are (at least) two CallGraphNodes which have no
         // function. One represents unknown external functions
         // called from this module; the other represents external
         // functions which could call into functions from this module.
         //
         // We conservatively mark these call graph nodes as
         // potential GC triggers.
         cgnStatus[cgn] = kStatusMayTriggerGC;
         continue;
       }

       // External functions (like those in the standard library)
       // all have edges to the phantom sink node, which we marked
       // above as may-allocate.
       // But we know better for many library functions.
       // If we recognize an external function here as non-allocating,
       // mark it as such and don't bother looking at what LLVM says
       // it might call.
       if (isKnownNotToAllocate(fn)) {
         cgnStatus[cgn] = kStatusWillNotTriggerGC;
         continue;
       }

       cgnStatus[cgn] = kStatusUnknownGCBehavior;

       //std::string fnName = callGraphNodeFuncName(cgn);

       for (CallGraphNode::const_iterator cgnit = cgn->begin(),
                         cgnend = cgn->end(); cgnit != cgnend; ++cgnit) {
         CallGraphNode::CallRecord cr = *cgnit;
         Value* maybeV = cr.first;
         CallGraphNode* called = cr.second;

         // Record call graph record if status was may-allocate.
         // We need to wait until the SCC is finished processing
         // in order to avoid marking something as non-allocating
         // if its status might be updated from further processing.
         if (maybeV && cgnStatus[called] != kStatusMayTriggerGC) {
           callsToMark.push_back(cr);
         }

         GCMallocStatus status = std::max(cgnStatus[cgn], cgnStatus[called]);
         cgnStatus[cgn] = status;

         /*
         llvm::outs() << "cgn " << cgn << "(" << status << ") = " << fnName
         << "; maybeV: " << maybeV << " :: " << llvmValueTag(maybeV) << "; dst: " << called
                << "\tcgn:name = " << callGraphNodeFuncName(called) << "\t; status of called node: "
                << cgnStatus[called] << "\n";
                */

         if (status == kStatusMayTriggerGC) {
           break;
         }
       }
    }

    // Now that the SCC has been processed, we can mark
    // all the calls in it which we have identified
    // as conservatively non-allocating.
    for (unsigned i = 0; i < callsToMark.size(); ++i) {
      CallGraphNode::CallRecord cr = callsToMark[i];
      Value* V = cr.first;
      CallGraphNode* called = cr.second;

      if (cgnStatus[called] != kStatusWillNotTriggerGC) {
        continue;
      }

      if (CallInst* ci = dyn_cast<CallInst>(V)) {
        markAsNonAllocating(ci);
      } else {
        llvm::outs() << "GCMallocFinder saw non-CallInst value "
                << llvmValueTag(V) << "; " << *V << "\n";
      }
    }
    return false;
  }
};

char GCMallocFinder::ID = 0;
RegisterPass<GCMallocFinder> X("foster-gcmallocfinder",
                              "Identifies (non-)allocating functions.");
} // unnamed namespace

namespace foster {

  Pass* createGCMallocFinderPass() {
    return new GCMallocFinder();
  }

}
