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
#include "llvm/Target/Mangler.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetLoweringObjectFile.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"

using llvm::GCFunctionInfo;

#include <set>
#include <map>

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

void EmitSymbol(const llvm::Twine& sym,
                llvm::raw_ostream& OS,
                llvm::AsmPrinter& AP,
                const llvm::MCAsmInfo& MAI) {
  std::string symbol = (MAI.getGlobalPrefix() + sym).str();

  llvm::SmallVectorImpl<char> mangledName(symbol.size());
  AP.Mang->getNameWithPrefix(mangledName, symbol);
  symbol = std::string(mangledName.begin(), mangledName.end());
  if (const char *GlobalDirective = MAI.getGlobalDirective()) {
    OS << GlobalDirective << symbol << "\n";
  }
  OS << symbol << ":\n";
}

typedef std::set<unsigned> Labels;
typedef std::set<int> RootOffsets;
typedef std::pair<int, llvm::Constant*> OffsetWithMetadata;
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
    clusters[fi].insert(PI->Num);
  }

  return clusters;
}

class FosterGCPrinter : public llvm::GCMetadataPrinter {
public:
  virtual void beginAssembly(llvm::raw_ostream &OS,
                             llvm::AsmPrinter &AP,
                             const llvm::MCAsmInfo &MAI) {
  }

  virtual void finishAssembly(llvm::raw_ostream &OS,
                              llvm::AsmPrinter &AP,
                              const llvm::MCAsmInfo &MAI) {
    // Set up for emitting addresses.
    const char *AddressDirective;
    int AddressAlignLog;
    if (AP.TM.getTargetData()->getPointerSize() == sizeof(int32_t)) {
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
    EmitSymbol("__foster_gcmaps", OS, AP, MAI);
    AP.OutStreamer.AddComment("number of function gc maps");
    AP.EmitInt32(end() - begin()); 

    // For each function...
    for (iterator FI = begin(), FE = end(); FI != FE; ++FI) {
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
      //     void*   SafePointAddress[AddressCount];
      //     {int32_t,
      //      void*} LiveOffsetsWithMetadata[LiveCountWithMetadata];
      //     int32_t LiveOffsets[LiveCountWithoutMetadata];
      //   } PointCluster[PointClusterCount];
      // } __foster_gcmap_<FUNCTIONNAME>;

      // Align to address width.
      AP.EmitAlignment(AddressAlignLog);

      // Emit the symbol by which the stack map entry can be found.
      EmitSymbol("__foster_gcmap_" + MD.getFunction().getName(),
                 OS, AP, MAI);

      // Compute the safe point clusters for this function.
      ClusterMap clusters = computeClusters(MD);

      // Emit PointClusterCount.
      AP.OutStreamer.AddComment("safe point cluster count");
      AP.EmitInt32(clusters.size());

      for (ClusterMap::iterator it = clusters.begin();
                                it != clusters.end(); ++it) {
        const FrameInfo& fi = (*it).first;
        int frameSize = fi.first;
        const RootOffsets& offsets = fi.second.first;
        const RootOffsetsWithMetadata& offsetsWithMetadata = fi.second.second;
        const Labels& labels = (*it).second;

        // Align to address width.
        AP.EmitAlignment(AddressAlignLog);

        // Emit the stack frame size.
        AP.OutStreamer.AddComment("stack frame size");
        AP.EmitInt32(MD.getFrameSize());

        // Emit the count of addresses in the cluster.
        AP.OutStreamer.AddComment("count of addresses");
        AP.EmitInt32(labels.size());

        // Emit the count of live roots in the cluster.
        AP.OutStreamer.AddComment("count of live roots with metadata");
        AP.EmitInt32(offsetsWithMetadata.size());

        AP.OutStreamer.AddComment("count of live roots w/o metadata");
        AP.EmitInt32(offsets.size());

        // Emit the stack offsets for the metadata-less roots in the cluster.
        for (RootOffsetsWithMetadata::iterator
                                   rit = offsetsWithMetadata.begin();
                                   rit != offsetsWithMetadata.end(); ++rit) {
          AP.OutStreamer.AddComment("metadata");
          AP.EmitGlobalConstant((*rit).second);

          AP.OutStreamer.AddComment("stack offset for root");
          AP.EmitInt32((*rit).first);
        }

        // Emit the stack offsets for the metadata-less roots in the cluster.
        for (RootOffsets::iterator rit = offsets.begin();
                                   rit != offsets.end(); ++rit) {
          AP.OutStreamer.AddComment("stack offset for root");
          AP.EmitInt32(*rit);
        }

        // Emit the addresses of the safe points in the cluster.
        for (Labels::iterator lit = labels.begin();
                              lit != labels.end(); ++lit) {
	  OS << AddressDirective
	     << MAI.getPrivateGlobalPrefix() << "label" << (*lit);
	  AP.OutStreamer.AddComment("safe point address");
	  AP.OutStreamer.AddBlankLine();
        }
      }
    }
  }
};

llvm::GCMetadataPrinterRegistry::Add<FosterGCPrinter>
X2("fostergc", "Foster GC printer");
  
} // unnamed namespace

