// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <inttypes.h>
#include <string>

namespace foster {
namespace runtime {
namespace gc {

typedef void (*gc_visitor_fn)(void** root, const void* meta);

void visitGCRootsWithStackMaps(void* start_frame,
                               gc_visitor_fn visitor);

void copying_gc_root_visitor(void **root, const void *meta);
bool isMetadataPointer(const void* meta);

const unsigned int FOSTER_GC_DEFAULT_ALIGNMENT = 16;      // 0b0..010000
const unsigned int FOSTER_GC_DEFAULT_ALIGNMENT_MASK = 15; // 0b0..001111


// E.g. if powerOf2 is 4, performs the following mapping:
// 0 -> 0      1 -> 4
// 2 -> 4      3 -> 4
// 4 -> 4      5 -> 8
template <typename T>
inline T* roundUpToNearestMultipleWeak(T* v, intptr_t powerOf2) {
  uintptr_t mask = powerOf2 - 1;
  return (T*) ((uintptr_t(v) + mask) & ~mask);
}


// Performs byte-wise addition on void pointer base
inline void* offset(void* base, intptr_t off) {
  return (void*) (((char*) base) + off);
}

const uint64_t FORWARDED_BIT = 0x02; // 0b000..00010

// This should remain synchronized with getHeapCellHeaderTy()
// in Codegen-typemaps.cpp
#define HEAP_CELL_HEADER_TYPE int64_t
#define HEAP_CELL_HEADER_SIZE (sizeof(HEAP_CELL_HEADER_TYPE))

struct heap_cell {
  HEAP_CELL_HEADER_TYPE size;
  unsigned char         body[0];
  //======================================
  void* body_addr() { return (void*) &body; }
  int64_t cell_size() { return size; }
  void* get_meta() { return (void*) size; }

  void set_meta(void* meta) { size = (HEAP_CELL_HEADER_TYPE) meta; }
  void set_cell_size(int64_t sz) { size = sz; }

  bool is_forwarded() {
    return (((uint64_t) cell_size()) & FORWARDED_BIT) != 0;
  }
  void set_forwarded_body(void* newbody) {
    size = ((HEAP_CELL_HEADER_TYPE) newbody) | FORWARDED_BIT;
  }
  void* get_forwarded_body() {
    return (void*) (((uint64_t) cell_size()) & ~FORWARDED_BIT);
  }

  static heap_cell* for_body(void* ptr) {
    return (heap_cell*) offset(ptr, -((int)HEAP_CELL_HEADER_SIZE));
  }
};

struct heap_array {
  HEAP_CELL_HEADER_TYPE meta;
  int64_t               arsz;
  unsigned char         elts[0];
  //======================================
  void* body_addr() { return (void*) &arsz; }
  void* elts_addr() { return (void*) &elts; }
  void* elt_body(int64_t cellnum, int64_t cellsz) { return offset(elts_addr(), cellnum * cellsz); };
  int64_t num_elts() { return arsz; }
  void set_num_elts(int64_t n) { arsz = n; }
  void* get_meta() { return (void*) meta; }

  void set_meta(void* m) { meta = (HEAP_CELL_HEADER_TYPE) m; }
  bool is_forwarded() {
    return (((uint64_t) get_meta()) & FORWARDED_BIT) != 0;
  }
  void set_forwarded_body(void* newbody) {
    set_meta((void*) (((uint64_t) newbody) | FORWARDED_BIT));
  }
  void* get_forwarded_body() {
    return (void*) (((uint64_t) get_meta()) & ~FORWARDED_BIT);
  }

  static heap_array* from_heap_cell(heap_cell* ptr) {
    return (heap_array*) ptr;
  }
};


// This structure describes the layout of a particular type,
// giving offsets and type descriptors for the pointer slots.
// Note that the GC plugin emits unpadded elements!
struct typemap {
  int64_t     cell_size;
  const char* name;
  int32_t     numOffsets;
  int8_t      ctorId;
  int8_t      isCoro;
  int8_t      isArray;
  int8_t      unused_padding;
  int32_t     offsets[0];
};

struct stackmap {
  struct OffsetWithMetadata {
    void* metadata;
    int32_t offset;
  };
  // GC maps emit structures without alignment, so we can't simply
  // use sizeof(stackmap::OffsetWithMetadata), because that value
  // includes padding.

  // A safe point is a location in the code stream where it is
  // safe for garbage collection to happen (that is, where the
  // code generator guarantees that any registers which might
  // hold references to live objects have been stored on the stack).
  //
  // A point cluster is a collection of safe points which share
  // the same layout of live pointers. Because LLVM does not (as of
  // this writing) calculate liveness information, all safe points
  // in the same function wind up with the same "live" variables.
  int32_t pointClusterCount;
  struct PointCluster {
    // register_stackmaps() assumes it knows the layout of this struct!
    int32_t frameSize;
    int32_t addressCount;
    int32_t liveCountWithMetadata;
    int32_t liveCountWithoutMetadata;
    OffsetWithMetadata
            liveOffsetsWithMetadata[0];
    int32_t liveOffsetsWithoutMetadata[0];
    void*   safePointAddresses[0];

    // Use manual pointer arithmetic to avoid C's padding rules.
    const OffsetWithMetadata* offsetWithMetadata(int i) const {
      #define OFFSET_WITH_METADATA_SIZE (sizeof(void*) + sizeof(int32_t))
      return (const OffsetWithMetadata*)
                  offset((void*) liveOffsetsWithMetadata,
                         i * OFFSET_WITH_METADATA_SIZE);
    }

    // TODO provide similar methods to find actual
    // addresses of the other flexible arrays.
  };
  PointCluster pointClusters[0];
};

struct stackmap_table {
  int32_t numStackMaps;
  stackmap stackmaps[0];
};


} } } // namespace foster::runtime::gc
