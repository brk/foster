// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "foster_gc_utils.h"
#include <cstdio>
#include <map>

namespace foster {
namespace runtime {
namespace gc {

extern FILE* gclog;

template <typename T>
intptr_t byte_distance(T* a, T* b) {
  return ((char*) a) - ((char*) b);
}

// This symbol is emitted by the fostergc LLVM GC plugin to the
// final generated assembly.
extern "C" {
  extern stackmap_table foster__gcmaps;
}

// Stack map registration walks through the stack maps emitted
// by the Foster LLVM GC plugin
void register_stackmaps(std::map<void*, const stackmap::PointCluster*>& clusterForAddress) {
  int32_t numStackMaps = foster__gcmaps.numStackMaps;
  fprintf(gclog, "num stack maps: %d\n", numStackMaps); fflush(gclog);

  void* ps = (void*) foster__gcmaps.stackmaps;
  size_t totalOffset = 0;

  for (int32_t m = 0; m < numStackMaps; ++m) {
    // Compute a properly aligned stackmap pointer.
    const stackmap* unaligned_stackmap_ptr = (const stackmap*) offset(ps, totalOffset);
    const stackmap* stackmap_ptr = roundUpToNearestMultipleWeak(unaligned_stackmap_ptr, sizeof(void*));
    totalOffset += byte_distance(stackmap_ptr, unaligned_stackmap_ptr);

    fprintf(gclog, "  %d stackmap_ptr: %p; unaligned = %p\n", m, stackmap_ptr, unaligned_stackmap_ptr); fflush(gclog);
    const stackmap& s = *stackmap_ptr;
    int32_t numClusters = s.pointClusterCount;
    fprintf(gclog, "  num clusters: %d\n", numClusters); fflush(gclog);

    totalOffset += sizeof(s.pointClusterCount);

    for (int32_t i = 0; i < numClusters; ++i) {
      const stackmap::PointCluster* pc =
        (const stackmap::PointCluster*) offset(ps, totalOffset);
      //fprintf(gclog, "  pointcluster*: %p\n", pc); fflush(gclog);

      const stackmap::PointCluster& c = *pc;
      totalOffset += sizeof(int32_t) * 4 // sizes + counts
                   + sizeof(int32_t) * c.liveCountWithoutMetadata
                   + OFFSET_WITH_METADATA_SIZE * c.liveCountWithMetadata;

      void** safePointAddresses = (void**) offset(ps, totalOffset);
      totalOffset += sizeof(void*)   * c.addressCount;

      fprintf(gclog, "  safePointAddrs: "); fflush(gclog);
      for (int i = 0; i < c.addressCount; ++i) {
        fprintf(gclog, " %p ,", safePointAddresses[i]);
      }
      fprintf(gclog, "\n");
      //fprintf(gclog, "  sizeof(stackmap::OffsetWithMetadata): %lu\n", sizeof(stackmap::OffsetWithMetadata));
      //fprintf(gclog, "  OFFSET_WITH_METADATA_SIZE: %lu\n", OFFSET_WITH_METADATA_SIZE);
      //fprintf(gclog, "  c.liveCountWithMetadata: %d\n", c.liveCountWithMetadata);
      //fprintf(gclog, "  c.liveCountWithoutMetadata: %d\n", c.liveCountWithoutMetadata);

      for (int32_t i = 0; i < c.addressCount; ++i) {
        void* safePointAddress = safePointAddresses[i];
        clusterForAddress[safePointAddress] = pc;
      }

      fprintf(gclog, "    cluster fsize %d, & %d, live: %d + %d\n\n",
                     c.frameSize, c.addressCount,
                     c.liveCountWithMetadata, c.liveCountWithoutMetadata);
    }
  }
  fprintf(gclog, "--------- gclog stackmap registration complete ----------\n");
  fflush(gclog);
}

} } } // namespace foster::runtime::gc

