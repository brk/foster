// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

// Based off of the example GC plugin from the LLVM documentation:
// http://llvm.org/docs/GarbageCollection.html

#include "llvm/CodeGen/GCs.h"
#include "llvm/CodeGen/GCStrategy.h"
#include "llvm/CodeGen/GCMetadata.h"
#include "llvm/CodeGen/GCMetadataPrinter.h"
#include "llvm/CodeGen/AsmPrinter.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCSymbol.h"

#include "llvm/Target/Mangler.h"
#include "llvm/DataLayout.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetLoweringObjectFile.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/Statistic.h"

#include "llvm/MC/MCSymbol.h"

using llvm::MCSymbol;
using llvm::GCFunctionInfo;

#include <set>
#include <map>

#define DEBUG_TYPE "foster"
STATISTIC(sNumStackMapsEmitted,     "Number of stack maps emitted");
STATISTIC(sNumStackMapBytesEmitted, "Number of stack map bytes emitted");
#undef DEBUG_TYPE

namespace foster {
  void linkFosterGC() {}
}

namespace {

class FosterGC : public llvm::GCStrategy {
public:
  FosterGC() {
    UsesMetadata = true;
    NeededSafePoints = 1 << llvm::GC::PostCall;
  }
};

llvm::GCRegistry::Add<FosterGC>
X1("fostergc", "Foster GC");

/////////////////////////////////////////////////////////////////////

const char kFosterGCMapsSymbolName[]      = "foster__gcmaps";
const char kFosterGCMapSymbolNamePrefix[] = "fos\"ter__gcmap>";

void EmitSymbol(const llvm::Twine& symStr,
                llvm::AsmPrinter& AP,
                const llvm::MCAsmInfo& MAI) {

  llvm::SmallString<128> mangledName;
  AP.Mang->getNameWithPrefix(mangledName, symStr);

  MCSymbol* sym = AP.OutContext.GetOrCreateSymbol(mangledName);
  AP.OutStreamer.EmitSymbolAttribute(sym, llvm::MCSA_Global);
  AP.OutStreamer.EmitLabel(sym);
}

typedef std::set<MCSymbol*> Labels;
typedef std::set<int> RootOffsets;
typedef std::pair<int,const llvm::Constant*> OffsetWithMetadata;
typedef std::set<OffsetWithMetadata> RootOffsetsWithMetadata;
typedef std::pair<RootOffsets, RootOffsetsWithMetadata> Roots;
typedef std::pair<int, Roots> FrameInfo; // .first=frame size

void collectLiveOffsets(GCFunctionInfo& MD,
                        GCFunctionInfo::iterator PI,
                        RootOffsets& offsets,
                        RootOffsetsWithMetadata& offsetsWithMetadata) {
  for (GCFunctionInfo::live_iterator LI = MD.live_begin(PI),
                                     LE = MD.live_end(PI); LI != LE; ++LI) {
    if (LI->Metadata) {
      offsetsWithMetadata.insert(
              OffsetWithMetadata(LI->StackOffset, LI->Metadata));
    } else {
      offsets.insert(LI->StackOffset);
    }
  }
}

typedef std::map<FrameInfo, Labels> ClusterMap;

ClusterMap computeClusters(GCFunctionInfo& MD) {
  ClusterMap clusters;

  for (GCFunctionInfo::iterator PI = MD.begin(),
                                PE = MD.end(); PI != PE; ++PI) {
    RootOffsets offsets;
    RootOffsetsWithMetadata offsetsWithMetadata;
    collectLiveOffsets(MD, PI, offsets, offsetsWithMetadata);
    FrameInfo fi(MD.getFrameSize(),
                 std::make_pair(offsets, offsetsWithMetadata));
    clusters[fi].insert(PI->Label);
  }

  return clusters;
}

class FosterGCPrinter : public llvm::GCMetadataPrinter {
public:
  void beginAssembly(llvm::AsmPrinter &AP) {
  }

  void finishAssembly(llvm::AsmPrinter &AP) {
    const llvm::MCAsmInfo &MAI = *(AP.MAI);

    // Set up for emitting addresses.
    const char *AddressDirective;
    int AddressAlignLog;
    if (AP.TM.getDataLayout()->getPointerSize() == sizeof(int32_t)) {
      AddressDirective = MAI.getData32bitsDirective();
      AddressAlignLog = 2;
    } else {
      AddressDirective = MAI.getData64bitsDirective();
      AddressAlignLog = 3;
    }

    // Put this in the data section.
    AP.OutStreamer.SwitchSection(AP.getObjFileLowering().getDataSection());

    // Emit a label and count of function maps
    AP.EmitAlignment(AddressAlignLog);
    EmitSymbol(kFosterGCMapsSymbolName, AP, MAI);
    AP.OutStreamer.AddComment("number of function gc maps");
    AP.EmitInt32(end() - begin());

    // For each function...
    for (iterator FI = begin(), FE = end(); FI != FE; ++FI) {
      sNumStackMapsEmitted++;

      GCFunctionInfo &MD = **FI;

      // Emit this data structure:
      //
      // struct {
      //   int32_t PointClusterCount;
      //   struct {
      //     int32_t FrameSize;
      //     int32_t AddressCount;
      //     int32_t LiveCountWithMetadata;
      //     int32_t LiveCountWithoutMetadata;
      //     {int32_t,
      //      void*} LiveOffsetsWithMetadata[LiveCountWithMetadata];
      //     int32_t LiveOffsets[LiveCountWithoutMetadata];
      //     void*   SafePointAddress[AddressCount];
      //   } PointCluster[PointClusterCount];
      // } __foster_gcmap_<FUNCTIONNAME>;

      // Align to address width.
      AP.EmitAlignment(AddressAlignLog);

      // Emit the symbol by which the stack map entry can be found.
      EmitSymbol(kFosterGCMapSymbolNamePrefix + MD.getFunction().getName(),
                 AP, MAI);

      // Compute the safe point clusters for this function.
      ClusterMap clusters = computeClusters(MD);

      // Emit PointClusterCount.
      AP.OutStreamer.AddComment("safe point cluster count");
      AP.EmitInt32(clusters.size());

      size_t i32sForThisFunction = 1; // above
      size_t voidPtrsForThisFunction = 0;

      for (ClusterMap::iterator it = clusters.begin();
                                it != clusters.end(); ++it) {
        const FrameInfo& fi = (*it).first;
        int frameSize = fi.first;
        const RootOffsets& offsets = fi.second.first;
        const RootOffsetsWithMetadata& offsetsWithMetadata = fi.second.second;
        const Labels& labels = (*it).second;

        // TODO on x86_64 this makes the generated binary crash while
        // registering stackmaps, but the testing infrastructure currently
        // doesn't detect the crash as abnormal termination.
        //AP.EmitAlignment(AddressAlignLog);

        // Emit the stack frame size.
        AP.OutStreamer.AddComment("stack frame size");
        AP.EmitInt32(frameSize);
        i32sForThisFunction++;

        // Emit the count of addresses in the cluster.
        AP.OutStreamer.AddComment("count of addresses");
        AP.EmitInt32(labels.size());
        i32sForThisFunction++;

        // Emit the count of live roots in the cluster.
        AP.OutStreamer.AddComment("count of live roots with metadata");
        AP.EmitInt32(offsetsWithMetadata.size());
        i32sForThisFunction++;

        AP.OutStreamer.AddComment("count of live roots w/o metadata");
        AP.EmitInt32(offsets.size());
        i32sForThisFunction++;

        // Emit the stack offsets for the metadata-imbued roots in the cluster.
        for (RootOffsetsWithMetadata::iterator
                                   rit = offsetsWithMetadata.begin();
                                   rit != offsetsWithMetadata.end(); ++rit) {
          AP.OutStreamer.AddComment("metadata");
          AP.EmitGlobalConstant((*rit).second);
          voidPtrsForThisFunction++;

          AP.OutStreamer.AddComment("stack offset for metadata-imbued root");
          AP.EmitInt32((*rit).first);
          i32sForThisFunction++;
        }

        // Emit the stack offsets for the metadata-less roots in the cluster.
        for (RootOffsets::iterator rit = offsets.begin();
                                   rit != offsets.end(); ++rit) {
          AP.OutStreamer.AddComment("stack offset for no-metadata root");
          AP.EmitInt32(*rit);
          i32sForThisFunction++;
        }

        unsigned IntPtrSize = AP.TM.getDataLayout()->getPointerSize();

        // Emit the addresses of the safe points in the cluster.
        for (Labels::iterator lit = labels.begin();
                              lit != labels.end(); ++lit) {
          AP.OutStreamer.AddComment("safe point address");
          const unsigned addrSpace = 0;
          AP.OutStreamer.EmitSymbolValue(*lit, IntPtrSize, addrSpace);
          voidPtrsForThisFunction++;
        }
      }
      sNumStackMapBytesEmitted += i32sForThisFunction * sizeof(int32_t)
                                + voidPtrsForThisFunction * sizeof(void*);
    }
  }
};

llvm::GCMetadataPrinterRegistry::Add<FosterGCPrinter>
X2("fostergc", "Foster GC printer");

} // unnamed namespace

