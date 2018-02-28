// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster.h"
#include "libfoster_util.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "foster_globals.h"
#include "stat_tracker.h"

#include "base/time/time.h" // for TimeTicks, TimeDelta
#include "base/metrics/histogram.h"
#include "base/metrics/statistics_recorder.h"

#include "execinfo.h" // for backtrace

#include <functional>
#include <stddef.h> // offsetof

#ifdef OS_LINUX
#include <sys/mman.h>
#endif

#include <immintrin.h>

extern "C" int64_t __foster_getticks();
extern "C" double  __foster_getticks_elapsed(int64_t t1, int64_t t2);

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)

// These are defined as compile-time constants so that the compiler
// can do effective dead-code elimination. If we were JIT compiling
// the GC we could (re-)specialize these config vars at runtime...
#define ENABLE_GCLOG 0
#define ENABLE_LINE_GCLOG 0
#define ENABLE_GCLOG_PREP 0
#define ENABLE_GCLOG_ENDGC 1
#define FOSTER_GC_TRACK_BITMAPS       0
#define FOSTER_GC_ALLOC_HISTOGRAMS    0
#define FOSTER_GC_TIME_HISTOGRAMS     0
#define FOSTER_GC_EFFIC_HISTOGRAMS    0
#define ENABLE_GC_TIMING              1
#define ENABLE_GC_TIMING_TICKS        0
#define GC_ASSERTIONS 0
#define MARK_EXACT                 1
#define MARK_FRAME21S                 1
#define COALESCE_FRAME15S             1
#define UNSAFE_ASSUME_F21_UNMARKED    false
#define TRACK_NUM_ALLOCATIONS         0
#define TRACK_NUM_ALLOC_BYTES         0
#define TRACK_NUM_REMSET_ROOTS        0
#define TRACK_NUM_OBJECTS_MARKED      0
#define TRACK_WRITE_BARRIER_COUNTS    0
#define TRACK_BYTES_KEPT_ENTRIES      0
#define TRACK_BYTES_ALLOCATED_ENTRIES 0
#define TRACK_BYTES_ALLOCATED_PINHOOK 0
#define GC_BEFORE_EVERY_MEMALLOC_CELL 0
#define DEBUG_INITIALIZE_ALLOCATIONS  0
#define FORCE_INITIALIZE_ALLOCATIONS  0 // Initialize even when the middle end doesn't think it's necessary
#define ELIDE_INITIALIZE_ALLOCATIONS  0 // Unsafe: ignore requests to initialize allocated memory.
#define MEMSET_FREED_MEMORY           0
// This included file may un/re-define these parameters, providing
// a way of easily overriding-without-overwriting the defaults.
#include "gc/foster_gc_reconfig-inl.h"

const int kFosterGCMaxDepth = 1024;
const ssize_t inline gSEMISPACE_SIZE() { return __foster_globals.semispace_size; }

/////////////////////////////////////////////////////////////////

#include "foster_gc_utils.h"

#include <sstream>
#include <list>
#include <vector>
#include <map>
#include <set>

#define IMMIX_LINE_SIZE     256
#define IMMIX_LINE_SIZE_LOG 8
#define IMMIX_CARDS_PER_FRAME15_LOG 7 /*15 - 8*/
#define IMMIX_CARDS_PER_FRAME15   128

extern "C" {
  void foster_pin_hook_memalloc_cell(uint64_t nbytes);
  void foster_pin_hook_memalloc_array(uint64_t nbytes);
}

namespace foster {
namespace runtime {
namespace gc {

FILE* gclog = NULL;

// {{{ Type definitions for GC globals
struct memory_range {
  void* base;
  void* bound;
  bool contains(void* addr) const { return base <= addr && addr < bound; }
  const char* rel(void* addr) const {
    if (addr <  base) return "before";
    if (addr >= bound) return "after";
    return "within";
  }
  size_t size() const { return distance(base, bound); }
};

void* realigned_to_line(void* bump) {
 return offset(roundUpToNearestMultipleWeak(bump, IMMIX_LINE_SIZE)
              ,HEAP_CELL_HEADER_SIZE);
}

void* realigned_for_allocation(void* bump) {
 return offset(roundUpToNearestMultipleWeak(bump, FOSTER_GC_DEFAULT_ALIGNMENT)
              ,HEAP_CELL_HEADER_SIZE);
}

class bump_allocator : public memory_range {
public:
  bump_allocator() {
    this->base = nullptr;
    this->bound = nullptr;
  }

  void* prechecked_alloc_noinit(size_t bytes) {
    void* rv = base;
    incr_by(base, bytes);
    return rv;
  }

  void* prechecked_alloc(size_t bytes) {
    void* rv = prechecked_alloc_noinit(bytes);
    if (DEBUG_INITIALIZE_ALLOCATIONS) { memset(rv, 0xAA, bytes); }
    return rv;
  }
};

struct byte_limit {
  ssize_t frame15s_left;

  byte_limit(ssize_t maxbytes) {
    // Round up; a request for 10K should be one frame15, not zero.
    this->frame15s_left = (maxbytes + ((1 << 15) - 1)) >> 15;
    auto mb = foster::humanize_s(double(maxbytes), "B");
    auto fb = foster::humanize_s(double(frame15s_left * (1 << 15)), "B");
    fprintf(gclog, "byte_limit: maxbytes = %s, maxframe15s = %ld, framebytes=%s\n",
          mb.c_str(), frame15s_left, fb.c_str());
  }
};

base::TimeTicks now() {
  if (ENABLE_GC_TIMING) { return base::TimeTicks::Now(); }
  else return base::TimeTicks();
}

base::TimeDelta timed(std::function<void()> f) {
  auto start = now();
  f();
  auto fin = now();
  return fin - start;
}

typedef void* ret_addr;
typedef void* frameptr;
// I've looked at using std::unordered_map or google::sparsehash instead,
// but both options lead to unacceptable binary bloat vs std::map,
// because chromium_base (etc) already uses std::map...
typedef std::map<frameptr, const stackmap::PointCluster*> ClusterMap;
// }}}

class heap {
public:
  virtual ~heap() {}

  virtual tidy* tidy_for(tori* t) = 0;

  virtual void dump_stats(FILE* json) = 0;
  virtual byte_limit* get_byte_limit() = 0;

  virtual void force_gc_for_debugging_purposes() = 0;
  virtual void gc_and_shrink() = 0;

  //virtual void condemn() = 0;

  virtual void scan_cell(heap_cell* cell, int maxdepth) = 0;
  virtual void visit_root(unchecked_ptr* root, const char* slotname) = 0;


  virtual void remember_outof(void** slot, void* val) = 0;
  virtual void remember_into(void** slot) = 0;

  virtual void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) = 0;
  virtual void* allocate_cell(typemap* typeinfo) = 0;

  virtual void* allocate_cell_16(typemap* typeinfo) = 0;
  virtual void* allocate_cell_32(typemap* typeinfo) = 0;
  virtual void* allocate_cell_48(typemap* typeinfo) = 0;
};

#define immix_heap heap

struct immix_space;
struct immix_worklist {
    void       initialize()      { ptrs.clear(); idx = 0; }
    void       process(immix_heap* target);
    bool       empty()           { return idx >= ptrs.size(); }
    void       advance()         { ++idx; }
    heap_cell* peek_front()      { return ptrs[idx]; }
    void       add(heap_cell* c) { ptrs.push_back(c); }
    size_t     size()            { return ptrs.size(); }
  private:
    size_t                  idx;
    std::vector<heap_cell*> ptrs;
};


// {{{ Global data used by the GC

class frame15;
class frame21;

enum class frame15kind : uint8_t {
  unknown = 0,
  immix_smallmedium, // associated is immix_space*
  immix_linebased,
  immix_malloc_start, // associated is immix_malloc_frame15info*
  immix_malloc_continue, // associated is heap_array* base.
  staticdata // parent is nullptr
};

enum class condemned_status : uint8_t {
  not_condemned = 0,
  yes_condemned
};

struct frame15info {
  void*            associated;
  frame15kind      frame_classification;
  uint8_t          num_marked_lines_at_last_collection;
  uint8_t          num_available_lines_at_last_collection;
  condemned_status frame_status;
};

// {{{
#define MAX_ARR_OBJ_PER_FRAME15 4
struct immix_malloc_frame15info {
  // Since allocs are min 8K, this will be guaranteed to have size at most 4.
  heap_array*      contained[MAX_ARR_OBJ_PER_FRAME15];
  immix_heap*      parents[MAX_ARR_OBJ_PER_FRAME15];
  condemned_status condemned[MAX_ARR_OBJ_PER_FRAME15];

  void remove(heap_array* arr) {
    for (int i = 0; i < arraysize(condemned); ++i) {
      if (contained[i] == arr) {
        contained[i] = nullptr;
        parents[i] = nullptr;
        condemned[i] = condemned_status::not_condemned;
        break;
      }
    }
  }

  void add(heap_array* arr, immix_heap* parent) {
    for (int i = 0; i < arraysize(condemned); ++i) {
      if (contained[i] == nullptr) {
        contained[i] = arr;
        parents[i] = parent;
        condemned[i] = condemned_status::not_condemned;
        break;
      }
    }
  }

};

template<int N, typename T, typename V>
V sizedset__lookup(T** arr, T* key, V* values) {
  for (int i = 0; i < N; ++i) {
    if (arr[i] == key) {
      return values[i];
    }
  }
  return V();
}

template<int N, typename T>
int sizedset__count(T** arr) {
  int rv = 0;
  for (int i = 0; i < N; ++i) {
    if (arr[i] != nullptr) { ++rv; }
  }
  return rv;
}
// }}}

template<typename Allocator>
struct GCGlobals {
  Allocator* allocator = NULL;
  Allocator* default_allocator = NULL;

  ClusterMap clusterForAddress;

  bool had_problems;

  std::map<std::pair<const char*, typemap*>, int64_t> alloc_site_counters;

  base::TimeTicks gc_time;
  base::TimeTicks runtime_start;
  base::TimeTicks    init_start;

  int num_gcs_triggered;
  int num_gcs_triggered_involuntarily;
  int num_big_stackwalks;
  double subheap_ticks;

  uint64_t num_allocations;
  uint64_t num_alloc_bytes;

  uint64_t write_barrier_phase0_hits;
  uint64_t write_barrier_phase1_hits;

  uint64_t num_objects_marked_total;

  frame15info* lazy_mapped_frame15info;
};

GCGlobals<immix_heap> gcglobals;

// The worklist would be per-GC-thread in a multithreaded implementation.
immix_worklist immix_worklist;

#define IMMIX_F15_PER_F21 64
#define IMMIX_LINES_PER_BLOCK 128
#define IMMIX_BYTES_PER_LINE 256
#define IMMIX_ACTIVE_F15_PER_F21 (IMMIX_F15_PER_F21 - 1)

// On a 64-bit machine, physical address space will only be 48 bits usually.
// If we use 47 of those bits, we can drop the low-order 15 bits and be left
// with 32 bits!
typedef uint32_t frame15_id;
typedef uint32_t frame21_id;

frame15_id frame15_id_of(void* p) { return frame15_id(uintptr_t(p) >> 15); }
frame21_id frame21_id_of(void* p) { return frame21_id(uintptr_t(p) >> 21); }

frame21* frame21_of_id(frame21_id x) { return (frame21*) (uintptr_t(x) << 21); }

uintptr_t low_n_bits(uintptr_t val, uintptr_t n) { return val & ((1 << n) - 1); }

uintptr_t line_offset_within_f21(void* slot) {
  return low_n_bits(uintptr_t(slot) >> 8, 21 - 8);
}

uintptr_t line_offset_within_f15(void* slot) {
  return low_n_bits(uintptr_t(slot) >> 8, 15 - 8);
}

inline
frame15info* frame15_info_for_frame15_id(frame15_id fid) {
  return &gcglobals.lazy_mapped_frame15info[fid];
}


inline
frame15kind classification_for_frame15_id(frame15_id fid) {
  return gcglobals.lazy_mapped_frame15info[fid].frame_classification;
}

inline
void set_classification_for_frame15_id(frame15_id fid, frame15kind v) {
  gcglobals.lazy_mapped_frame15info[fid].frame_classification = v;
}

inline
void* associated_for_frame15_id(frame15_id fid) {
  return gcglobals.lazy_mapped_frame15info[fid].associated;
}

inline
void set_associated_for_frame15_id(frame15_id fid, void* v) {
  gcglobals.lazy_mapped_frame15info[fid].associated = v;
}

//static_assert(sizeof(frame15info) == 16, "expect frame15info to be two words");

frame15info* frame15_info_for(void* addr) {
  // The one liner definition is:
  return frame15_info_for_frame15_id(frame15_id_of(addr));
  // But Clang generates weird code.
  // Instead of shifting right 15 and then left 4 (to convert idx-to-byte-offset),
  // Clang shifts right 11 and then masks the low bits with an AND of a large immediate.
  //return (frame15info*)offset((void*)gcglobals.lazy_mapped_frame15info, (uintptr_t(addr) >> 15) << 4);
}

struct large_array_allocator {
  std::list<void*> allocated;

  static heap_array* align_as_array(void* base) {
    // We want the body address of the array to be aligned mod 16.
    return static_cast<heap_array*>(((uintptr_t(base) & 0xF) == 8) ? base : offset(base, 8));
  }

  tidy* allocate_array(const typemap* arr_elt_map,
                       int64_t  num_elts,
                       int64_t  total_bytes,
                       bool     init,
                       uint8_t  mark_bits_current_value,
                       immix_heap* parent) {
    void* base = malloc(total_bytes + 8);
    heap_array* allot = align_as_array(base);

    if (FORCE_INITIALIZE_ALLOCATIONS ||
      (init && !ELIDE_INITIALIZE_ALLOCATIONS)) { memset((void*) base, 0x00, total_bytes + 8); }
    allot->set_header(arr_elt_map, mark_bits_current_value);
    allot->set_num_elts(num_elts);
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_array(total_bytes); }

    // TODO modify associated frame15infos, lazily allocate card bytes.
    toggle_framekinds_for(allot, offset(base, total_bytes + 7), parent);
    // TODO review when/where line mark bit setting happens,
    //      ensure it doesn't happen for pointers to arrays.
    allocated.push_front(base);
    return allot->body_addr();
  }

  void toggle_framekinds_for(heap_array* allot, void* last, immix_heap* parent) {
    frame15_id b = frame15_id_of(allot);
    frame15_id e = frame15_id_of(last);

    set_framekind_malloc(b, allot, parent);
    // If b == e, we've already set the framekind.
    // If the line offset isn't the last one in the block, we must assume that
    // another allocation can happen, so we'll leave the framekind unset.
    if ((b != e) && (line_offset_within_f15(last) == IMMIX_LINES_PER_BLOCK - 1)) {
      set_framekind_malloc_continue(e, allot);
    }
    // Any blocks in between the start and end should be marked as continuations.
    while (++b < e) {
      set_framekind_malloc_continue(b, allot);
    }
  }

  void set_framekind_malloc(frame15_id b, heap_array* allot, immix_heap* parent) {
    if (classification_for_frame15_id(b) != frame15kind::immix_malloc_start) {
      set_classification_for_frame15_id(b, frame15kind::immix_malloc_start);
      // Potential race condition in multithreaded code

      immix_malloc_frame15info* maf = (immix_malloc_frame15info*) malloc(sizeof(immix_malloc_frame15info));
      memset(maf->contained, 0, sizeof(maf->contained));
      set_associated_for_frame15_id(b, maf);
    }

    immix_malloc_frame15info* maf = (immix_malloc_frame15info*) associated_for_frame15_id(b);
    maf->add(allot, parent);
  }

  void set_framekind_malloc_continue(frame15_id mc, heap_array* allot) {
    auto mc_f = frame15_info_for_frame15_id(mc);
    set_classification_for_frame15_id(mc, frame15kind::immix_malloc_continue);
    set_associated_for_frame15_id(mc, allot);
  }

  void framekind_malloc_cleanup(heap_array* allot) {
    auto b = frame15_id_of(allot);
    immix_malloc_frame15info* maf = (immix_malloc_frame15info*) associated_for_frame15_id(b);
    maf->remove(allot);

    if (0 == sizedset__count<4>(&maf->contained[0])) {
      auto b_f = frame15_info_for_frame15_id(b);
      set_classification_for_frame15_id(b, frame15kind::unknown);
      free(associated_for_frame15_id(b));
      set_associated_for_frame15_id(b, nullptr);
    }
  }

  // Iterates over each allocated array, and calls free() on the unmarked ones.
  void sweep_arrays(uint8_t mark_bits_current_value) {
    for (auto it = allocated.begin(); it != allocated.end();       ) {
      void* base = *it;
      heap_array* arr = align_as_array(base);
      if (arr->get_mark_bits() != mark_bits_current_value) {
        if (ENABLE_GCLOG) { fprintf(gclog, "freeing unmarked array %p\n", arr); }
        // unmarked, can free associated array.
        it = allocated.erase(it); // erase() returns incremented iterator.
        framekind_malloc_cleanup(arr);
        free(base);

        // TODO inspect outgoing card table?
      } else {
        ++it;
      }
    }
  }
};
// }}}

// {{{ Internal utility functions
extern "C" foster_bare_coro** __foster_get_current_coro_slot();

void gc_assert(bool cond, const char* msg);

intr* from_tidy(tidy* t) { return (intr*) t; }

struct immix_line_frame15;
void mark_lineframe(immix_line_frame15* f) {
  auto fid = frame15_id_of(f);
  gcglobals.lazy_mapped_frame15info[fid].associated = f;
  gcglobals.lazy_mapped_frame15info[fid].frame_classification = frame15kind::immix_linebased;
}

void set_parent_for_frame(immix_space* p, frame15* f) {
  auto fid = frame15_id_of(f);
  gcglobals.lazy_mapped_frame15info[fid].associated = p;
  gcglobals.lazy_mapped_frame15info[fid].frame_classification = frame15kind::immix_smallmedium;
}

frame15kind frame15_classification(void* addr) {
  return gcglobals.lazy_mapped_frame15info[frame15_id_of(addr)].frame_classification;
}

void set_frame15_classification(void* addr, frame15kind v) {
  gcglobals.lazy_mapped_frame15info[frame15_id_of(addr)].frame_classification = v;
}

// Returns either null (for static data) or a valid immix_space*.
immix_heap* heap_for(void* addr);

bool non_kosher_addr(void* addr) {
  intptr_t signed_val = intptr_t(addr);
  return signed_val < 0x100000;
  // Including negative values, which correspond to high-bit-set addrs;
  // this implies that we can't use the 3rd GB of the 32-bit addr pace.
}

// TODO make sure the addresses we use for allocation are kosher...
bool owned_by(tori* body, immix_heap* space) {
  if (non_kosher_addr(body)) {
    return false;
  }

  return heap_for((void*) body) == space;
}

/*
bool is_condemned_(void* slot, frame15info* finfo) {
  return condemned_status_for_frame15info(finfo, slot) == condemned_status::yes_condemned;
}
*/

bool is_condemned(void* slot, immix_heap* space) {
  return owned_by((tori*)slot, space);
}


template <typename T>
inline T num_granules(T size_in_bytes) { return size_in_bytes / T(16); }

// }}}

// {{{

namespace helpers {

  void print_heap_starvation_info(FILE* f) {
    //fprintf(f, "working set exceeded heap size of %lld bytes! aborting...\n", curr->get_size()); fflush(f);
    fprintf(f, "    try running with a larger heap size using a flag like\n");
    fprintf(f, "      --foster-runtime '{\"gc_semispace_size_kb\":64000}'\n");
  }

  void oops_we_died_from_heap_starvation() {
    print_heap_starvation_info(gclog);
    print_heap_starvation_info(stderr);
    exit(255); // TODO be more careful if we're allocating from a coro...
  }

  tidy* allocate_array_prechecked(bump_allocator* bumper,
                                  const typemap* arr_elt_map,
                                  int64_t  num_elts,
                                  int64_t  total_bytes,
                                  uint8_t  mark_value,
                                  bool     init) {
    heap_array* allot = static_cast<heap_array*>(bumper->prechecked_alloc_noinit(total_bytes));
    if (FORCE_INITIALIZE_ALLOCATIONS ||
      (init && !ELIDE_INITIALIZE_ALLOCATIONS)) { memset((void*) allot, 0x00, total_bytes); }
    //fprintf(gclog, "alloc'a %d, bump = %p, low bits: %x\n", int(total_bytes), bump, intptr_t(bump) & 0xF);
    allot->set_header(arr_elt_map, mark_value);
    allot->set_num_elts(num_elts);
    //if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(total_bytes); }
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_array(total_bytes); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += total_bytes; }

    if (FOSTER_GC_TRACK_BITMAPS) {
      //size_t granule = granule_for(tori_of_tidy(allot->body_addr()));
      //obj_start.set_bit(granule);
      //obj_limit.set_bit(granule + num_granules(total_bytes));
    }
    return allot->body_addr();
  }

  void allocate_cell_prechecked_histogram(int N) {
    if (N > 128) {
      LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-alloc-large", N, 129, 33000000, 50);
    } else {
      LOCAL_HISTOGRAM_ENUMERATION("gc-alloc-small", N, 128);
    }
  }

  tidy* allocate_cell_prechecked(bump_allocator* bumper,
                                 const typemap* map,
                                 int64_t  cell_size,
                                 uint8_t  mark_value) {
    heap_cell* allot = static_cast<heap_cell*>(bumper->prechecked_alloc(cell_size));
    //if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(map->cell_size); }
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_cell(cell_size); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += cell_size; }
    if (FOSTER_GC_ALLOC_HISTOGRAMS) { allocate_cell_prechecked_histogram((int) cell_size); }
    allot->set_header(map, mark_value);

    if (FOSTER_GC_TRACK_BITMAPS) {
      //size_t granule = granule_for(tori_of_tidy(allot->body_addr()));
      //obj_start.set_bit(granule);
    }
    return allot->body_addr();
  }

} // namespace helpers
// }}}

// {{{ Bitmap/bytemap utility class
// Bitmap overhead for 16-byte granules is 8 KB per MB (roughly 1%).
class bitmap {
private:
  size_t num_bytes;
  uint8_t* bytes;

public:
  bitmap(int num_bits) {
    // Invariant: can treat bytes as an array of uint64_t.
    num_bytes = roundUpToNearestMultipleWeak(num_bits / 8, 8);
    bytes = (uint8_t*) malloc(num_bytes);
  }

  ~bitmap() { free(bytes); bytes = 0; }

  void clear() { memset(bytes, 0, num_bytes); }

  static uint8_t get_bit(int n, uint8_t* bytes) {
    int byte_offset = n / 8;
    int bit_offset  = n % 8;
    uint8_t val = bytes[byte_offset];
    uint8_t bit = (val >> bit_offset) & 1;
    return bit;
  }

  static void set_bit(int n, uint8_t* bytes) {
    int byte_offset = n / 8;
    int bit_offset  = n % 8;
    uint8_t val = bytes[byte_offset];
    bytes[byte_offset] = val | (1 << bit_offset);
  }

  uint8_t get_bit(int n) { return bitmap::get_bit(n, bytes); }
  void    set_bit(int n) {        bitmap::set_bit(n, bytes); }

  // For object start/finish bitmaps, we expect the bitmap to be dense
  // and thus this loop will execute a very small number of times, and
  // searching by byte is likely to be noise/overhead.
  int prev_bit_onebyone(int n) {
    while (n --> 0) {
      if (get_bit(n)) return n;
    }
    return -1;
  }

};
// }}}

////////////////////////////////////////////////////////////////////

// {{{ Function prototype decls
void inspect_typemap(const typemap* ti);
void visitGCRoots(void* start_frame, immix_heap* visitor);
void coro_visitGCRoots(foster_bare_coro* coro, immix_heap* visitor);
const typemap* tryGetTypemap(heap_cell* cell);
// }}}

// TODO use stat_tracker again?

frame21* allocate_frame21() {
  frame21* rv = (frame21*) base::AlignedAlloc(1 << 21, 1 << 21);
  gc_assert(rv != NULL, "unable to allocate a 2MB chunk from the OS");
  return rv;
}

struct frame15_allocator {
  frame15_allocator() : next_frame15(nullptr) {}

  bool empty() { return !next_frame15 && spare_frame15s.empty(); }

  void clear() {
    if (!spare_frame15s.empty()) {
      fprintf(gclog, "WARNING: frame15_allocator.clear() with spare frame15s...\n");
      spare_frame15s.clear();
    }

    if (!self_owned_allocated_frame21s.empty()) {
      fprintf(gclog, "calling AlignedFree on %zu frame21s\n", self_owned_allocated_frame21s.size());
      for (auto f21 : self_owned_allocated_frame21s) {
        base::AlignedFree(f21);
      }
      self_owned_allocated_frame21s.clear();
    }

    next_frame15 = nullptr;
  }

  void give_frame15(frame15* f) { spare_frame15s.push_back(f); }

  // Precondition: empty()
  // Note: we allocate frame15s from the frame21 but the space may retain ownership.
  void give_frame21(frame21* f) {
    next_frame15 = (frame15*) f;
    // Skip first frame15, which will be used for metadata.
    incr_by(next_frame15, 1 << 15);
  }

  frame15* get_frame15() {
    if (!spare_frame15s.empty()) {
      frame15* f = spare_frame15s.back(); spare_frame15s.pop_back();
      return f;
    }

    if (empty()) {
      frame21* f = allocate_frame21();
      self_owned_allocated_frame21s.push_back(f);
      give_frame21(f);
    }

    frame15* curr_frame15 = next_frame15;

    incr_by(next_frame15, 1 << 15);
    if (frame21_id_of(curr_frame15) != frame21_id_of(next_frame15)) {
      next_frame15 = nullptr;
    }

    //fprintf(gclog, "handing out frame15: %p, now empty? %d\n", curr_frame15, empty());
    return curr_frame15;
  }

  void give_line_frame15(immix_line_frame15* f) { spare_line_frame15s.push_back(f); }

  immix_line_frame15* get_line_frame15() {
    if (!spare_line_frame15s.empty()) {
      auto f = spare_line_frame15s.back(); spare_line_frame15s.pop_back();
      return f;
    }

    return (immix_line_frame15*) get_frame15();
  }

  // Note: the associated f21 may or may not be owned by this class...
  frame15* next_frame15;
  immix_line_frame15* next_line_frame15;
  std::vector<frame15*> spare_frame15s;
  std::vector<immix_line_frame15*> spare_line_frame15s;

  std::vector<frame21*> self_owned_allocated_frame21s;
};

class immix_line_space;
immix_line_space* get_owner_for_immix_line_frame15(immix_line_frame15* f, int line);
condemned_status get_condemned_status_for_immix_line_frame15(immix_line_frame15* f, int line);
condemned_status condemned_status_for(void* addr);


__attribute((noinline))
condemned_status condemned_status_for_slowpath(frame15kind fc, void* addr) {
  auto associated = associated_for_frame15_id(frame15_id_of(addr));

  if (fc == frame15kind::immix_linebased) {
    auto lineframe = static_cast<immix_line_frame15*>(associated);
    auto line = line_offset_within_f15(addr);
    return get_condemned_status_for_immix_line_frame15(lineframe, line);
  } else if (fc == frame15kind::immix_malloc_continue) {
    return condemned_status_for(associated);
  } else if (fc == frame15kind::immix_malloc_start) {
    immix_malloc_frame15info* maf = (immix_malloc_frame15info*) associated;
    heap_array* arr = heap_array::from_heap_cell(heap_cell::for_tidy((tidy*)addr));
    return sizedset__lookup<4>(&maf->contained[0], arr, &maf->condemned[0]);
  }

  foster_assert(false, "condemned_status missing a case! maybe 'frame15kind::unknown'");
  return condemned_status::not_condemned;
}

condemned_status condemned_status_for(void* addr) {
  auto f15id = frame15_id_of(addr);
  auto fc = classification_for_frame15_id(f15id);
  if (fc == frame15kind::immix_smallmedium) {
    return gcglobals.lazy_mapped_frame15info[f15id].frame_status;
  }
  return condemned_status_for_slowpath(fc, addr);
}

__attribute((noinline))
immix_heap* heap_for_slowpath(frame15kind fc, void* associated, void* addr) {
  if (fc == frame15kind::immix_linebased) {
    auto lineframe = static_cast<immix_line_frame15*>(associated);
    auto line = line_offset_within_f15(addr);
    return (immix_heap*) get_owner_for_immix_line_frame15(lineframe, line);
  } else if (fc == frame15kind::immix_malloc_continue) {
    return heap_for(associated);
    //finfo = frame15_info_for(associated);
    // fallthrough!
  } else if (fc == frame15kind::immix_malloc_start) {
    immix_malloc_frame15info* maf = (immix_malloc_frame15info*) associated;
    heap_array* arr = heap_array::from_heap_cell(heap_cell::for_tidy((tidy*)addr));
    return sizedset__lookup<4>(&maf->contained[0], arr, &maf->parents[0]);
  }

  return static_cast<immix_heap*>(associated);
}

immix_heap* heap_for(void* addr) {
  auto f15id = frame15_id_of(addr);
  auto fc = classification_for_frame15_id(f15id);
  auto ss = associated_for_frame15_id(f15id);
  if (fc == frame15kind::immix_smallmedium) {
    return static_cast<immix_heap*>(ss);
  }
  return heap_for_slowpath(fc, ss, addr);
}

//immix_heap* heap_for_frame15info_normalonly(frame15info* finfo, void* addr) {
//  return static_cast<immix_heap*>(finfo->associated);
//}

frame15_allocator global_frame15_allocator;


// Since these pointers are guaranteed to fit within a single line,
// we can embed the information in the start of each free span.
class free_line_span {
  void* bump;
  void* limit;
  free_line_span* next;
};

// 64 * 32 KB = 2 MB  ~~~ 2^6 * 2^15 = 2^21
struct frame21_15_metadata_block {
  union {
    // The first block entry (IMMIX_LINES_PER_BLOCK bytes) of the linemap will be
    // unused, since it self-referentially refers to the metadata block's lines.
    // Likewise for the other metadata elements listed here.
    struct { uint8_t framemap[IMMIX_F15_PER_F21];
             // TODO intrusive linked list of frames?
    };
    // 8 KB for 256-byte lines
    uint8_t linemap[IMMIX_F15_PER_F21][IMMIX_LINES_PER_BLOCK]; // # bytes needed for 256-byte lines
  };

  // 16 KB: 64 * (32 KB / 16 B) = 64 * 2 K bits = 64 * 256 B = 16 KB
  // Changing line size from 128 <-> 256 doesn't change the number of bits
  // needed for the object map, but it does change whether all the
  // object-start bits for a single line fall onto the same byte in memory.
  uint8_t objstart_bits[16384]; // uint8_t objstart_block[IMMIX_F15_PER_F21][256]; // 256 = 2 K bits

  // TODO when & how to clear objstart bits?

  uint8_t cardmap[IMMIX_F15_PER_F21][IMMIX_LINES_PER_BLOCK];
};

// Returns a number between zero and 63.
uint8_t frame15_id_within_f21(frame15_id global_fid) {
  return uint8_t(low_n_bits(global_fid, 21 - 15));
}

frame15* frame15_for_frame15_id(frame15_id f15) {
  return (frame15*)(uintptr_t(f15) << 15);
}

frame21_15_metadata_block* metadata_block_for_slot(void* slot) {
 return (frame21_15_metadata_block*)((uintptr_t(slot) >> 21) << 21);
}

frame21_15_metadata_block* metadata_block_for_frame15_id(frame15_id f15) {
  return metadata_block_for_slot((void*) frame15_for_frame15_id(f15));
}

frame21_15_metadata_block* metadata_block_for_frame21(frame21* f21) {
 return (frame21_15_metadata_block*)f21;
}


uint8_t* cards_for_frame15_id(frame15_id fid) {
  auto mdb = metadata_block_for_frame15_id(fid);
  return &mdb->cardmap[frame15_id_within_f21(fid)][0];
}

uint8_t* linemap_for_frame15_id(frame15_id fid) {
  auto mdb = metadata_block_for_frame15_id(fid);
  return &mdb->linemap[frame15_id_within_f21(fid)][0];
}

void clear_linemap(uint8_t* linemap) {
  memset(linemap, 0, IMMIX_LINES_PER_BLOCK);
}

void clear_frame15(frame15* f15) {
  memset(f15, 0xDD, 1 << 15);
}


uint8_t* get_frame_map(frame21_15_metadata_block* mdb) {
  return &mdb->linemap[0][0];
}

void mark_frame15_for_slot_with(void* slot, uint8_t value) {
  uint8_t* framemap = get_frame_map(metadata_block_for_slot(slot));
  framemap[frame15_id_within_f21(frame15_id_of(slot))] = value;
}

void   mark_frame15_for_slot(void* slot) { mark_frame15_for_slot_with(slot, 1); }
void   mark_frame21_for_slot(void* slot) {
  uint8_t* framemap = get_frame_map(metadata_block_for_slot(slot));
  framemap[0] = 1;
}

void unmark_frame15(frame15* f15) { mark_frame15_for_slot_with(f15, 0); }
void unmark_frame21(frame21* f21) { clear_linemap(get_frame_map(metadata_block_for_frame21(f21))); }

bool frame15_is_marked(frame15* f15) {
  uint8_t* framemap = get_frame_map(metadata_block_for_slot(f15));
  return framemap[frame15_id_within_f21(frame15_id_of(f15))] == 1;
}

bool frame21_is_marked(frame21* f21) {
  if (MARK_FRAME21S) {
    uint8_t* framemap = get_frame_map(metadata_block_for_frame21(f21));
    return framemap[0] == 1;
  } else if (false) { // marking frame15s
    uint8_t* framemap = get_frame_map(metadata_block_for_frame21(f21));
    uint64_t* fm64 = (uint64_t*) framemap;
    uint64_t frame_bits = (fm64[0] | fm64[1])
                        | (fm64[2] | fm64[3])
                        | (fm64[4] | fm64[5])
                        | (fm64[6] | fm64[7]);
    return frame_bits != 0;
  } else return !UNSAFE_ASSUME_F21_UNMARKED;
}

// {{{ metadata helpers

static inline int64_t array_size_for(int64_t n, int64_t slot_size) {
  return roundUpToNearestMultipleWeak(sizeof(heap_array) + n * slot_size,
                                      FOSTER_GC_DEFAULT_ALIGNMENT);
}

inline void get_cell_metadata(heap_cell* cell,
                              heap_array*    & arr ,
                              const typemap* & map,
                              int64_t        & cell_size) {
  cell_size = cell->cell_size();
  gc_assert(cell_size > 0, "cannot copy cell lacking metadata or length");

  if ((map = tryGetTypemap(cell))) {
    if (ENABLE_GCLOG) { inspect_typemap(map); }
    if (map->isArray) {
      arr = heap_array::from_heap_cell(cell);
    }
  }

  // {{{
  if (!map) {
    // already have cell size
  } else if (!arr) {
    cell_size = map->cell_size; // probably an actual pointer
  } else {
    cell_size = array_size_for(arr->num_elts(), map->cell_size);
    if (ENABLE_GCLOG) {
      fprintf(gclog, "Collecting array of total size %" PRId64
                    " (rounded up from %" PRId64 " + %" PRId64 " = %" PRId64
                    "), cell size %" PRId64 ", len %" PRId64 "...\n",
                          cell_size,
                          int64_t(sizeof(heap_array)),
                                               arr->num_elts() * map->cell_size,
                          sizeof(heap_array) + arr->num_elts() * map->cell_size,
                          map->cell_size,
                          arr->num_elts());
    }
  }
  // }}}
}

// }}}

// {{{

void mark_line_for_slot(void* slot) {
  auto mdb = metadata_block_for_frame15_id(frame15_id_of(slot));
  uint8_t* linemap = &mdb->linemap[0][0];
  linemap[ line_offset_within_f21(slot) ] = 1;
}

// Precondition: slot in small/medium/linemap frame,
// therefore slot and lastslot guaranteed to be in the same frame.
void mark_lines_for_slots(void* slot, uint64_t cell_size) {
  auto mdb = metadata_block_for_frame15_id(frame15_id_of(slot));
  uint8_t* linemap = &mdb->linemap[0][0];

  void* lastslot = offset(slot, cell_size);

  auto firstoff = line_offset_within_f21(slot);
  auto lastoff  = line_offset_within_f21(lastslot);

  if (MARK_FRAME21S) { mark_frame21_for_slot(slot); }

  linemap[firstoff] = 1;
  // Exact marking for small objects
  linemap[lastoff] = 1;

  // Interestingly, this gets *slower* if we remove the line above!
  // Why? Without it, Clang is smart enough to recognize a memset-like loop,
  // but because our expected number of iterations is zero or one,
  // the overhead of calling memset is a net loss.

  // Mark intermediate lines if necessary.
  while (++firstoff < lastoff) {
    linemap[firstoff] = 1;
  }
}

void mark_lines_for_slots_conserv(void* slot, uint64_t cell_size) {
  mark_line_for_slot(slot);

  while (cell_size > IMMIX_LINE_SIZE) {
    cell_size -= IMMIX_LINE_SIZE;
    incr_by(slot, IMMIX_LINE_SIZE);
    mark_line_for_slot(slot);
  }
}

struct immix_common {

  uint8_t mark_bits_current_value;

  immix_common() : mark_bits_current_value(0) {}

  uint8_t get_mark_value() { return mark_bits_current_value; }

  inline bool is_marked(heap_cell* obj) {
    return obj->get_mark_bits() == this->mark_bits_current_value;
  }

  void flip_current_mark_bits_value() {
    // This value starts intialized to zero by the immix_space constructor.
    this->mark_bits_current_value =
      this->mark_bits_current_value ^ HEADER_MARK_BITS;
  }

  void scan_with_map_and_arr(immix_heap* space,
                             heap_cell* cell, const typemap& map,
                             heap_array* arr, int depth) {
    //fprintf(gclog, "copying %lld cell %p, map np %d, name %s\n", cell_size, cell, map.numEntries, map.name); fflush(gclog);
    if (!arr) {
      scan_with_map(space, from_tidy(cell->body_addr()), map, depth);
    } else if (map.numOffsets > 0) { // Skip this loop for int arrays and such.
      int64_t numcells = arr->num_elts();
      for (int64_t cellnum = 0; cellnum < numcells; ++cellnum) {
        scan_with_map(space, arr->elt_body(cellnum, map.cell_size), map, depth);
      }
    }

    if (map.isCoro == 1) {
      foster_bare_coro* coro = reinterpret_cast<foster_bare_coro*>(cell->body_addr());
      coro_visitGCRoots(coro, space);
    }
  }

  void scan_with_map(immix_heap* space, intr* body, const typemap& map, int depth) {
    for (int i = 0; i < map.numOffsets; ++i) {
      immix_trace(space, (unchecked_ptr*) offset(body, map.offsets[i]),
                           depth);
    }
  }

  void scan_cell(immix_heap* space, heap_cell* cell, int depth) {
    if (is_marked(cell)) {
      //fprintf(gclog, "cell %p was already marked\n", cell);
      return;
    }

    if (depth == 0) {
      immix_worklist.add(cell);
      return;
    }

    heap_array* arr = NULL;
    const typemap* map = NULL;
    int64_t cell_size;
    get_cell_metadata(cell, arr, map, cell_size);

    cell->flip_mark_bits();
    if (TRACK_NUM_OBJECTS_MARKED) { gcglobals.num_objects_marked_total++; }

    auto frameclass = frame15_classification(cell);

    if (frameclass == frame15kind::immix_smallmedium
     || frameclass == frame15kind::immix_linebased) {
      void* slot = (void*) cell;
      if (MARK_EXACT) {
        mark_lines_for_slots(slot, cell_size);
      } else {
        mark_lines_for_slots_conserv(slot, cell_size);
      }
    }

    // Without metadata for the cell, there's not much we can do...
    if (map) scan_with_map_and_arr(space, cell, *map, arr, depth - 1);
  }

  // Jones/Hosking/Moss refer to this function as "process(fld)".
  void immix_trace(immix_heap* space, unchecked_ptr* root, int depth) {
    //       |------------|       obj: |------------|
    // root: |    body    |---\        |  size/meta |
    //       |------------|   |        |------------|
    //                        \- tidy->|            |
    //                        |       ...          ...
    //                        \-*root->|            |
    //                                 |------------|
    tidy* tidyn;
    tori* body = untag(*root);
    if (!body) return;

    auto f15id = frame15_id_of((void*) body);
    auto f15info = frame15_info_for((void*) body);

    // Look up status of corresponding frame15
    // Possibilities:
    //   * Immix block in this space
    //      - Mark or evacuate based on prev collection's stats
    //   * Immix block in some other space
    //      - Ignore, since we can rely on remembered sets
    //   * Stable (known global or stack data)
    //      - Trace but don't evacuate
    //   * Unknown (??)
    if (classification_for_frame15_id(f15id) == frame15kind::staticdata) {
      // Do nothing: no need to mark, since static data never points to
      // dynamically allocated data.
      return;
    }

    // TODO is_full_heap || ....
    //if (!is_condemned_(body, f15info)) {
    if (!is_condemned(body, space)) {
      // When collecting a subset of the heap, we only look at condemned objects,
      // and ignore objects stored in non-condemned regions (regardless of
      // whether they are part of this particular subheap or not).
      // The remembered set is guaranteed to contain all incoming pointers
      // from non-condemned regions.
      return;
    }

    //fprintf(gclog, "space %p saw pointer %p to owner space %p\n", this, body, owner);

    // TODO drop the assumption that body is a tidy pointer.
    heap_cell* obj = heap_cell::for_tidy(reinterpret_cast<tidy*>(body));
    bool should_evacuate = false;
    if (should_evacuate) {
      //tidyn = next->ss_copy(obj, depth);
      // Calculate the original root's updated (possibly interior) pointer.
      //*root = make_unchecked_ptr((tori*) offset(tidyn, distance(tidy, body) ));
      //gc_assert(NULL != untag(*root), "copying gc should not null out slots");
      //gc_assert(body != untag(*root), "copying gc should return new pointers");
    } else {
      scan_cell(space, obj, depth);
    }
  }

  void visit_root(immix_heap* space, unchecked_ptr* root, const char* slotname) {
    gc_assert(root != NULL, "someone passed a NULL root addr!");
    if (ENABLE_GCLOG) {
      fprintf(gclog, "\t\tSTACK SLOT %p contains ptr %p, slot name = %s\n", root,
                        unchecked_ptr_val(*root),
                        (slotname ? slotname : "<unknown slot>"));
    }
    immix_trace(space, root, kFosterGCMaxDepth);
  }

  template <bool use_space>
  uint64_t process_remset(immix_heap* space, std::set<tori**>& incoming_ptr_addrs) {
    uint64_t numRemSetRoots = 0;
    for (tori** loc: incoming_ptr_addrs) {
      // We can ignore the remembered set root if the source is also getting collected.
      if (is_condemned(loc, space)) {
        continue;
      }

      tori* ptr = *loc;
      // Otherwise, we must check whether the source slot was modified;
      // if so, it might not point into our space.
      if (owned_by(ptr, space)) {
        if (TRACK_NUM_REMSET_ROOTS) { numRemSetRoots++; }
        visit_root(space, (unchecked_ptr*) ptr, "remembered_set_root");
      }
    }
    return numRemSetRoots;
  }
    /*
    uint64_t numRemSetLines = 0;
    // Trace from remembered set roots
    for (auto& fid : frames_pointing_here) {
      auto frame_cards = cards_for_frame15_id(fid);
      for (int i = 0; i < IMMIX_CARDS_PER_FRAME15; ++i) {
        if (frame_cards[i] != 0) {
          ++numRemSetLines;
          // Scan card for pointers that point into this space.
          unchecked_ptr** finger = (unchecked_ptr**) frame15_for_frame15_id(fid);
          unchecked_ptr** limit  = (unchecked_ptr**) frame15_for_frame15_id(fid + 1);
          for ( ; finger != limit; ++finger) {
            unchecked_ptr* ptr = *finger;
            if (owned_by((tori*)ptr, this)) {
              // TODO pin values since they're being treated conservatively?
              if (TRACK_NUM_REMSET_ROOTS) { numRemSetRoots++; }
              common.visit_root(this, ptr, "remembered_set_root");
            }
          }
        }
      }
    }
    */
};


class immix_line_frame15;

class immix_frame_tracking {
  // We store the frame15 count separately so that we don't need to
  // consult the map entries in fromglobal_frame15s.
  size_t num_frame15s_total; // including both indvidual and coalesced.

  // Stores values returned from global_frame15_allocator.get_frame15();
  // Note we store a vector rather than a set because we maintain
  // the invariant that a given frame15 is only added once between clear()s.
#if COALESCE_FRAME15S
  std::map<frame21_id, std::vector<frame15*> > fromglobal_frame15s;
#else
  std::vector<frame15*> uncoalesced_frame15s;
#endif

  std::vector<frame21*> coalesced_frame21s;
public:

  template<typename Thunk>
  void iter_frame15(Thunk thunk) {
#if COALESCE_FRAME15S
    for (auto mapentry : fromglobal_frame15s) {
      for (auto f15 : mapentry.second) {
        thunk(f15);
      }
    }
#else
      for (auto f15 : uncoalesced_frame15s) {
        thunk(f15);
      }
#endif
  }

  template<typename Thunk>
  void iter_coalesced_frame21(Thunk thunk) {
    for (auto f21 : coalesced_frame21s) {
      thunk(f21);
    }
  }

  void clear() {
    num_frame15s_total = 0;
#if COALESCE_FRAME15S
    fromglobal_frame15s.clear();
#else
    uncoalesced_frame15s.clear();
#endif
    coalesced_frame21s.clear();
  }

  void add_frame21(frame21* f) {
    num_frame15s_total += IMMIX_ACTIVE_F15_PER_F21;
    coalesced_frame21s.push_back(f);
  }

  void add_frame15(frame15* f) {
    ++num_frame15s_total;

#if COALESCE_FRAME15S
    auto x = frame21_id_of(f);
    std::vector<frame15*>& v = fromglobal_frame15s[x];
    v.push_back(f);
    //fprintf(gclog, "v.size() is %d for frame21 %d of f15 %p\n", v.size(), x, f);
    if (v.size() == IMMIX_ACTIVE_F15_PER_F21) {
      coalesced_frame21s.push_back(frame21_of_id(x));
      fromglobal_frame15s.erase(fromglobal_frame15s.find(x));
    }
#else
    uncoalesced_frame15s.push_back(f);
#endif
  }

  size_t logical_frame15s() { return num_frame15s_total; }

  size_t physical_frame15s() {
    size_t rv = 0;
#if COALESCE_FRAME15S
    for (auto mapentry : fromglobal_frame15s) {
      rv += mapentry.second.size();
    }
#else
    rv = uncoalesced_frame15s.size();
#endif
    return rv;
  }

  size_t count_frame21s() { return coalesced_frame21s.size(); }
};

#define IMMIX_LINE_FRAME15_START_LINE 4

struct immix_line_frame15 {
  // We set aside 5 of the 128 lines in the frame, which is 3.9% overhead
  // (1 KB + 128b out of 32 KB).
  //condemned_status condemned[128]; // one line for per-line condemned bytemap
  // We can store per-line space pointers for the remaining 123 lines:
  immix_line_space* owners[124]; // 8 b * (123 + 5) = 1 KB
  // And have five words left over for bookkeeping:
  union {
    struct {
      bump_allocator bumper;
      immix_line_space* last_user;
    };
    struct {
      uint64_t pad1;
      uint64_t pad2;
      uint64_t pad3;
      uint64_t pad4;
      uint64_t pad5;
    };
  };

  char begin_lines[0];


  void mark_owner(immix_line_space* owner, int64_t nbytes);

  // The offset mediates between the logical and physical view of line numbering.
  // If we stored metadata at the end of the frame we could avoid it.
  immix_line_space* get_owner_for_line(int n) { return owners[n - IMMIX_LINE_FRAME15_START_LINE]; }
  void set_owner_for_line(int n, immix_line_space* o) { owners[n - IMMIX_LINE_FRAME15_START_LINE] = o; }

  //condemned_status  get_condemned_status_for_line(int n) { return condemned[n]; }
};

static_assert( IMMIX_BYTES_PER_LINE > IMMIX_LINES_PER_BLOCK,
            "too few entries in immix_line_frame15->condemned!");
static_assert(  offsetof(immix_line_frame15, begin_lines)
            == (IMMIX_LINE_FRAME15_START_LINE * IMMIX_BYTES_PER_LINE),
            "our expectation for the positioning of begin_lines is broken!");

void* first_line_of_line_frame15(immix_line_frame15* f) {
  return offset(f, IMMIX_LINE_FRAME15_START_LINE * IMMIX_LINE_SIZE);
}


class immix_line_allocator {
  immix_line_frame15* current_frame;

public:
  immix_line_allocator() : current_frame(nullptr) {}

  void ensure_current_frame(immix_line_space* owner, int64_t cell_size, bool force_new_line = false);

  // For use as the last step in condemn().
  void ensure_no_line_reuse(immix_line_space* owner) {
    if (!current_frame) return;
    ensure_current_frame(owner, 0, true);
  }

  void* allocate_array(immix_line_space* owner, typemap* elt_typeinfo, int64_t n, int64_t req_bytes, uint8_t mark_value, bool init) {
    ensure_current_frame(owner, req_bytes);
    return helpers::allocate_array_prechecked(&current_frame->bumper, elt_typeinfo, n, req_bytes, mark_value, init);
  }

  void* allocate_cell(immix_line_space* owner, int64_t cell_size, uint8_t mark_value, typemap* typeinfo) {
    ensure_current_frame(owner, cell_size);
    return helpers::allocate_cell_prechecked(&(current_frame->bumper), typeinfo, cell_size, mark_value);
  }

  bool owns(immix_line_frame15* f) { return f == current_frame; }
};

immix_line_allocator global_immix_line_allocator;

// Each immix_line_space implicitly references the global immix line allocator,
// which keeps a single line_frame15* (which can have multiple "owners").
// The line allocator requests new frames from spaces, which get frames from
// the global_frame15_allocator.
// This  back-and-forth lets frames obey space limits.
//
// TODO problematic thing i think:
// line space S allocates a line or two from frame F which is stored in global_immix_line_allocator (GILA);
// S marks F as used;
// line space GCs -> F empty -> F returned to global_frame15_allocator (GFA)

class immix_line_space : public heap {
public:
  immix_common common;

private:
  // How many are we allowed to allocate before being forced to GC & reuse?
  byte_limit* lim;
  
  large_array_allocator laa;

  std::vector<immix_line_frame15*> used_frames;
  immix_line_frame15* prev_used_frame;


  // The points-into remembered set; each frame in this set needs to have its
  // card table inspected for pointers that actually point here.
  //std::set<frame15_id> frames_pointing_here;
  std::set<tori**> incoming_ptr_addrs;

public:
  immix_line_space(byte_limit* lim) : lim(lim) {
    fprintf(gclog, "new immix_line_space %p, byte limit: %p, current value: %zd f15s\n", this, lim, lim->frame15s_left);
  }

  virtual void dump_stats(FILE* json) {
    return;
  }

  virtual void scan_cell(heap_cell* cell, int depth) {
    common.scan_cell(this, cell, depth);
  }

  void used_frame(immix_line_frame15* f) {
    // We want to keep a set of used frames.
    // Calls to this function will often have locality,
    // which we capture with prev_used_frame.
    // We ought to use a hash table instead of a vector
    // so that we don't grow when reusing/recycling multiple frames.
    if (f != prev_used_frame) { used_frames.push_back(f); prev_used_frame = f; }
  }

  immix_line_frame15* get_new_frame(bool secondtry = false) {
    if (lim->frame15s_left == 0) {
      gcglobals.num_gcs_triggered_involuntarily++;

      this->immix_line_gc();

      fprintf(gclog, "forced smallgc reclaimed %d frames\n", lim->frame15s_left);
      if (secondtry) {
        helpers::oops_we_died_from_heap_starvation();
      } else return get_new_frame(true);
    }

    // The frame returned may be fragmented, which we don't yet account for.
    --lim->frame15s_left;
    auto lineframe = global_frame15_allocator.get_line_frame15();
    mark_lineframe(lineframe);
    lineframe->last_user = this;
    lineframe->bumper.base = realigned_for_allocation(first_line_of_line_frame15(lineframe));
    lineframe->bumper.bound = offset(first_line_of_line_frame15(lineframe),
                                          ((1 << 15) - (1 << 10)));
    return lineframe;
  }

  virtual tidy* tidy_for(tori* t) { return (tidy*) t; }

  virtual void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) {
    int64_t slot_size = elt_typeinfo->cell_size; // note the name change!
    int64_t req_bytes = array_size_for(n, slot_size);

    //fprintf(gclog, "allocating array, %d elts * %d b = %d bytes\n", n, slot_size, req_bytes);

    if (false && FOSTER_GC_ALLOC_HISTOGRAMS) {
      LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-alloc-array", (int) req_bytes, 1, 33000000, 128);
    }

    if (req_bytes > (1 << 13)) {
      return laa.allocate_array(elt_typeinfo, n, req_bytes, init, common.get_mark_value(), this);
    } else {
      return global_immix_line_allocator.allocate_array(this, elt_typeinfo, n, req_bytes, common.get_mark_value(), init);
    }
  }


  // Invariant: cell size is less than one line.
  virtual void* allocate_cell(typemap* typeinfo) {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.
    return global_immix_line_allocator.allocate_cell(this, cell_size, common.get_mark_value(), typeinfo);
  }

  // Invariant: N is less than one line.
  template <int N>
  void* allocate_cell_N(typemap* typeinfo) {
    return global_immix_line_allocator.allocate_cell(this, N, common.get_mark_value(), typeinfo);
  }

  virtual void* allocate_cell_16(typemap* typeinfo) { return allocate_cell_N<16>(typeinfo); }
  virtual void* allocate_cell_32(typemap* typeinfo) { return allocate_cell_N<32>(typeinfo); }
  virtual void* allocate_cell_48(typemap* typeinfo) { return allocate_cell_N<48>(typeinfo); }


  virtual byte_limit* get_byte_limit() { return lim; }
  virtual void force_gc_for_debugging_purposes() { this->immix_line_gc(); }
  virtual void gc_and_shrink() {
    this->immix_line_gc();
    // No shrinking for line spaces, currently.
  }

  /*
  virtual void condemn() {
    for (auto lineframe : used_frames) {
      for (int i = IMMIX_LINE_FRAME15_START_LINE; i < IMMIX_LINES_PER_BLOCK; ++i) {
        if (lineframe->get_owner_for_line(i) == this) {
          lineframe->condemned[i] = condemned_status::yes_condemned;
        }
      }
    }

    global_immix_line_allocator.ensure_no_line_reuse(this);
  }

  void uncondemn() {
    for (auto lineframe : used_frames) {
      for (int i = IMMIX_LINE_FRAME15_START_LINE; i < IMMIX_LINES_PER_BLOCK; ++i) {
        if (lineframe->get_owner_for_line(i) == this) {
          lineframe->condemned[i] = condemned_status::not_condemned;
        }
      }
    }
  }
  */

  void visit_root(unchecked_ptr* root, const char* slotname) {
    common.visit_root(this, root, slotname);
  }

  // Clear the line map for our frames -- but only for the lines we own!
  void clear_mark_bits_for_space() {
    for (auto lineframe : used_frames) {
      uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(lineframe));
      for (int i = IMMIX_LINE_FRAME15_START_LINE; i < IMMIX_LINES_PER_BLOCK; ++i) {
        if (lineframe->get_owner_for_line(i) == this) {
          linemap[i] = 0;
        }
      }
    }
  }

  void immix_line_gc() {
    auto num_marked_at_start = gcglobals.num_objects_marked_total;

    base::TimeTicks lineGCStartTime = now();

    common.flip_current_mark_bits_value();

    auto deltaClearMarkBits = timed([&] () {
      // Before we begin tracing, we need to establish the invariant that
      // any line which might be free should be unmarked.
      // Since the assumption is that the space is small, we do so directly.
      clear_mark_bits_for_space();
    });

    // TODO check condemned set instead of assuming true
    uint64_t numRemSetRoots = common.process_remset<true>(this, incoming_ptr_addrs);

    visitGCRoots(__builtin_frame_address(0), this);

    foster_bare_coro** coro_slot = __foster_get_current_coro_slot();
    foster_bare_coro*  coro = *coro_slot;
    if (coro) {
      if (ENABLE_GCLOG) {
        fprintf(gclog, "==========visiting current coro: %p\n", coro); fflush(gclog);
      }
      common.visit_root(this, (unchecked_ptr*)coro_slot, NULL);
      if (ENABLE_GCLOG) {
        fprintf(gclog, "==========visited current coro: %p\n", coro); fflush(gclog);
      }
    }

    immix_worklist.process(this);

    // The regular immix space would call clear_current_blocks() here
    // because it marks frames as recycled.
    {
    
    laa.sweep_arrays(common.get_mark_value());

    // Get a copy of the used frames
    auto all_used_frames = get_all_used_frames();
    used_frames.clear();
    prev_used_frame = nullptr;

    for (auto lineframe : all_used_frames) {
      this->inspect_line_frame15_postgc(lineframe);
    }

#if ENABLE_GC_TIMING && ENABLE_GCLOG_ENDGC
    auto delta = now() - lineGCStartTime;
    fprintf(gclog, "used frames: %zu -> %zu, took %ld us which was %f%% premark; frames left: %zd\n",
        all_used_frames.size(), used_frames.size(),
        delta.InMicroseconds(),
        double(deltaClearMarkBits.InMicroseconds() * 100.0)/double(delta.InMicroseconds()),
        lim->frame15s_left
        );
#endif
#   if TRACK_NUM_OBJECTS_MARKED
        fprintf(gclog, "\t%d objects marked in this GC cycle, %d marked overall\n",
                gcglobals.num_objects_marked_total - num_marked_at_start,
                gcglobals.num_objects_marked_total);
#   endif
#if (ENABLE_GCLOG || ENABLE_GCLOG_ENDGC)
#   if TRACK_NUM_REMSET_ROOTS
        fprintf(gclog, "\t%ld objects identified in remset\n", numRemSetRoots);
#   endif
      fprintf(gclog, "\t/endgc-small\n\n");
      fflush(gclog);
#endif
    }

    // TODO gcglobals.gc_time and gcglobals.subheap_ticks
    gcglobals.num_gcs_triggered += 1;
  }

  // Note this returns a copy!
  std::vector<immix_line_frame15*> get_all_used_frames() {
    return used_frames;
  }

  void inspect_line_frame15_postgc(immix_line_frame15* lineframe) {

    //frame15* f15 = frame15_for_frame15_id(fid);
    //if (heap_for(f15) != this) { return; }

    uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(lineframe));

    uint8_t num_marked_lines = 0;
    for (int i = IMMIX_LINE_FRAME15_START_LINE; i < IMMIX_LINES_PER_BLOCK; ++i) {
      if (lineframe->get_owner_for_line(i) == this) {
        if (linemap[i]) {
          ++num_marked_lines;
        } else {
          lineframe->set_owner_for_line(i, nullptr);
        }
      }
    }

    // We currently only recycle blocks when every line we own(ed) is left unmarked.
    // Another possibility would be to explicitly manage lines instead of blocks,
    // but that gets into segregated freelist designs, splitting/merging, etc.

    if (num_marked_lines > 0) {
      if (ENABLE_GCLOG || ENABLE_LINE_GCLOG) { fprintf(gclog, "immix_line_space reusing frame %p\n", lineframe); }
      used_frame(lineframe);
    } else if (!global_immix_line_allocator.owns(lineframe)) {
      if (ENABLE_GCLOG || ENABLE_LINE_GCLOG) { fprintf(gclog, "immix_line_space returning frame %p\n", lineframe); }
      lim->frame15s_left++;
      global_frame15_allocator.give_line_frame15(lineframe);
    } else {
      if (ENABLE_GCLOG || ENABLE_LINE_GCLOG) { fprintf(gclog, "immix_line_space ignoring active-allocation frame %p\n", lineframe); }
    }
    // TODO update frame15_info? does it make sense for shared frame15s?
  }

  virtual void remember_outof(void** slot, void* val) {
    auto mdb = metadata_block_for_slot((void*) slot);
    uint8_t* cards = (uint8_t*) mdb->cardmap;
    cards[ line_offset_within_f21((void*) slot) ] = 1;
  }

  virtual void remember_into(void** slot) {
    //frames_pointing_here.insert(frame15_id_of((void*) slot));
    incoming_ptr_addrs.insert((tori**) slot);
  }

};

immix_line_space* get_owner_for_immix_line_frame15(immix_line_frame15* f, int line) {
  return f->get_owner_for_line(line);
}

condemned_status get_condemned_status_for_immix_line_frame15(immix_line_frame15* f, int line) {
  //return f->get_condemned_status_for_line(line); // TODO
  gc_assert(false, "line condemned not yet implemented");
  return condemned_status::not_condemned;
}


void immix_line_frame15::mark_owner(immix_line_space* owner, int64_t nbytes) {
  int startline = line_offset_within_f15(bumper.base);
  int endline = line_offset_within_f15(offset(bumper.base, nbytes));
  if (endline == startline) {
    // mark just one, don't bother looping
    set_owner_for_line(startline, owner);
  } else {
    if (endline == 0) { // wrapped around
      endline = IMMIX_LINES_PER_BLOCK - IMMIX_LINE_FRAME15_START_LINE;
    }
    for (int i = startline; i < endline; ++i) {
      set_owner_for_line(i, owner);
    }
  }

  owner->used_frame(this);
}

void immix_line_allocator::ensure_current_frame(immix_line_space* owner, int64_t cell_size, bool force_new_line) {
  if (!current_frame) {
    current_frame = owner->get_new_frame();
    if (ENABLE_GCLOG || ENABLE_LINE_GCLOG) { fprintf(gclog, "immix_line_allocator acquired first frame %p\n", current_frame); }
  }

  // Are we continuing to allocate to our own lines,
  // or taking ownership from another space?
  if (current_frame->last_user != owner || force_new_line) {
    if (current_frame->bumper.size() < IMMIX_LINE_SIZE) {
      // If we're on the last line, we cannot realign to the next line.
      current_frame->bumper.base = current_frame->bumper.bound;
    } else {
      // If we have room, we can move to a new frame
      // and check below whether we have room to allocate.
      current_frame->bumper.base = realigned_for_allocation(
          realigned_to_line(current_frame->bumper.base));
      current_frame->last_user = owner;
    }
  }

  // Make sure we have enough space even after realignment.
  if (current_frame->bumper.size() < cell_size) {
    current_frame = owner->get_new_frame();
    if (ENABLE_GCLOG || ENABLE_LINE_GCLOG) { fprintf(gclog, "immix_line_allocator acquired new frame %p with bumper size %d\n",
        current_frame, current_frame->bumper.size()); }
  }

  current_frame->mark_owner(owner, cell_size);
}

// }}}

// Invariant: IMMIX_LINES_PER_BLOCK <= 256
// Invariant: marked lines have value 1, unmarked are 0.
uint8_t count_marked_lines_for_frame15(uint8_t* linemap_for_frame) {
  uint8_t count = 0; // Note: Clang compiles this to straight-line code using vector ops.
  for (int i = 0; i < IMMIX_LINES_PER_BLOCK; ++i) { count += linemap_for_frame[i]; }
  return count;
}

bool no_marked_lines_for_frame15(uint8_t* linemap_for_frame) {
  uint64_t* linemap64 = (uint64_t*) linemap_for_frame;
  uint64_t bits = 0; // Note: Clang compiles this to straight-line code using "or"s.
  for (int i = 0; i < (IMMIX_LINES_PER_BLOCK / sizeof(*linemap64)); ++i) { bits |= linemap64[i]; }
  return bits == 0;
}

uint8_t count_holes_in_linemap_for_frame15(uint8_t* linemap_for_frame) {
  uint8_t numTransitions = 0;
  uint8_t currentState = linemap_for_frame[0];
  for (int i = 0; i < IMMIX_LINES_PER_BLOCK; ++i) {
    if (linemap_for_frame[i] != currentState) {
      ++numTransitions;
      currentState = linemap_for_frame[i];
    }
  }

  // ddddddddddd : 0 holes, 0 transitions
  // ___________ : 1 hole,  0 transitions
  if (numTransitions == 0) return 1 - currentState; // _ = 0 = unmarked = hole

  // ddd________ : 1 hole,  1 transition
  // ddd_____ddd : 1 hole,  2 transitions
  // ____ddd____ : 2 holes, 2 transitions
  // ____ddd__dd : 2 holes, 3 transitions
  return numTransitions - (currentState == 1);
}



// TODO mark_lines_from_slot() function?

bool is_linemap15_clear(frame15* f15) {
  uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(f15));
  return no_marked_lines_for_frame15(linemap);
}

bool is_linemap_clear(frame21* f21) {
    if (!frame21_is_marked(f21)) return true;

    auto mdb = metadata_block_for_frame21(f21);
#if 1
    uint64_t linehash = 0;
    for (int i = 1; i < IMMIX_F15_PER_F21; ++i) {
      uint64_t* lines = (uint64_t*) &mdb->linemap[i][0];
      #pragma clang loop vectorize(enable)
      for (int j = 0; j < IMMIX_LINES_PER_BLOCK / 8; ++j) {
        linehash |= lines[j];
      }
      if (linehash != 0) break;
    }
    return linehash == 0;
#else
    __m256i linehash = _mm256_setzero_si256();
    for (int i = 1; i < IMMIX_F15_PER_F21; ++i) {
      __m256i* lines = (__m256i*) &mdb->linemap[i][0];
      for (int j = 0; j < IMMIX_LINES_PER_BLOCK / sizeof(*lines); ++j) {
        //linehash |= lines[j];
        linehash = _mm256_or_si256(linehash, lines[j]);
      }
      //if (linehash != 0) break; (skipped for cleaner vectorization)
    }
    //return linehash == 0;
    return _mm256_testz_si256(linehash, linehash);



    /*
    auto pstart = &mdb->linemap[1][0];
    auto pend   = &mdb->linemap[IMMIX_F15_PER_F21 - 1][IMMIX_LINES_PER_BLOCK - 1];
    return memchr(pstart, 1, pend - pstart) == nullptr;
    */
#endif
}



class immix_space : public heap {
public:
  immix_space(byte_limit* lim) : lim(lim) {
    fprintf(gclog, "new immix_space %p, byte limit ptr: %p, current value: %zd f15s\n", this, lim, lim->frame15s_left);
  }
  // TODO take a space limit. Use a combination of local & global
  // frame21_allocators to service requests for frame15s.

  virtual void dump_stats(FILE* json) {
    return;
  }

  virtual byte_limit* get_byte_limit() { return lim; }

  void clear_current_blocks() {
    // TODO clear mem to avoid conservative pointer leaks
    small_bumper.base = small_bumper.bound;
    medium_bumper.base = medium_bumper.bound;
  }

  virtual void visit_root(unchecked_ptr* root, const char* slotname) {
    common.visit_root(this, root, slotname);
  }

  virtual void force_gc_for_debugging_purposes() { this->immix_gc(); }

  // {{{ Prechecked allocation functions
  template <int N>
  tidy* allocate_cell_prechecked_N(const typemap* map) {
    return helpers::allocate_cell_prechecked(&small_bumper, map, N, common.get_mark_value());
  }

  tidy* allocate_cell_prechecked(const typemap* map) {
    return helpers::allocate_cell_prechecked(&small_bumper, map, map->cell_size, common.get_mark_value());
  }
  // }}}


  // {{{ Allocation, in various flavors & specializations.

  // If this function returns false, we'll trigger a GC and try again.
  // If the function still returns false after GCing, game over!
  inline bool try_establish_alloc_precondition(bump_allocator* bumper, int64_t cell_size) {
     if (bumper->size() >= cell_size) return true;
     return try_prep_allocatable_block(bumper, cell_size);
  }

  bool try_prep_allocatable_block(bump_allocator* bumper, int64_t cell_size) __attribute__((noinline)) {
    //fprintf(gclog, "prepping allocatable block in subheap %p; #recycl = %d\n", this, recycled_frame15s.size());

    // Note the implicit policy embodied below in the preference between
    // using recycled frames, clean used frames, or fresh/new frames.
    //
    // The immix paper uses a policy of expansion -> recycled -> clean used.
    // The order below is different.

    // Recycled frames are only used for small allocations, for which we only
    // need one free line. Using recycled frames for medium allocations raises
    // the risk for fragmentation to require searching many recycled frames.

    if (!recycled_frame15s.empty() && cell_size <= IMMIX_LINE_SIZE) {
      frame15* f = recycled_frame15s.back(); recycled_frame15s.pop_back();
      uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(f));
      int startline = MARK_EXACT
                    ? unmarked_line_from(linemap, 0)
                    : conservatively_unmarked_line_from(linemap, 0);
      int endline   = first_marked_line_after(linemap, startline);
      if (ENABLE_GCLOG || ENABLE_GCLOG_PREP) {
        fprintf(gclog, "using recycled frame15 %p: startline = %d, endline = %d, # left: %zu\n", f, startline, endline, recycled_frame15s.size());
        for (int i = 0; i < IMMIX_LINES_PER_BLOCK; ++i) { fprintf(gclog, "%c", linemap[i] ? 'd' : '_'); }
        fprintf(gclog, "\n");
      }
      if (startline != -1) {
        bumper->bound = offset(f, endline   * IMMIX_LINE_SIZE);
        bumper->base  = offset(f, startline * IMMIX_LINE_SIZE);
        bumper->base  = realigned_for_allocation(bumper->base);
        return true;
      }
    }

    if (!clean_frame15s.empty()) {
      frame15* f = clean_frame15s.back(); clean_frame15s.pop_back();
      if (ENABLE_GCLOG_PREP) { fprintf(gclog, "grabbed clean frame15: %p\n", f); }
      if (MEMSET_FREED_MEMORY) { clear_frame15(f); }
      bumper->base  = realigned_for_allocation(f);
      bumper->bound = offset(f, 1 << 15);
      return true;
    }

    if (lim->frame15s_left > 0) {
      --lim->frame15s_left;
      // Note: cannot call clear() on global allocator until
      // all frame15s it has distributed are relinquished.
      frame15* f = global_frame15_allocator.get_frame15();
      tracking.add_frame15(f);
      set_parent_for_frame(this, f);
      bumper->base  = realigned_for_allocation(f);
      bumper->bound = offset(f, 1 << 15);
      if (ENABLE_GCLOG_PREP) { fprintf(gclog, "grabbed global frame15: %p into space %p\n", f, this); }
      return true;
    }

    // Note: frame15_allocator would call allocate_frame21() itself if empty
    // but we don't want it to, because the space should own any allocated
    // frames for bookkeeping purposes.
    if (local_frame15_allocator.empty()) {
      if (clean_frame21s.empty()) {
        return false; // no used frames, no new frames available. sad!
      }

      frame21* f = clean_frame21s.back(); clean_frame21s.pop_back();
      if (ENABLE_GCLOG_PREP) { fprintf(gclog, "giving clean frame21 to local f15 allocator: %p\n", f); }
      local_frame15_allocator.give_frame21(f);
    }

    frame15* f = local_frame15_allocator.get_frame15();
    if (MEMSET_FREED_MEMORY) { clear_frame15(f); }
    set_parent_for_frame(this, f);
    bumper->base  = realigned_for_allocation(f);
    bumper->bound = offset(f, 1 << 15);
    if (ENABLE_GCLOG_PREP) { fprintf(gclog, "using local frame15: %p\n", f); }
    return true;
  }

  int conservatively_unmarked_line_from(uint8_t* linemap, int start) {
      for (int i = start; i < (IMMIX_LINES_PER_BLOCK - 1); ++i) {
        if (linemap[i] == 0 && linemap[i + 1] == 0) {
          if (i == 0) return 0;
          return i + 1;
        }
      }
      return -1;
  }

  int unmarked_line_from(uint8_t* linemap, int start) {
      for (int i = start; i < (IMMIX_LINES_PER_BLOCK - 1); ++i) {
        if (linemap[i] == 0) return i;
      }
      return -1;
  }

  int first_marked_line_after(uint8_t* linemap, int start) {
      for (int i = start + 1; i < IMMIX_LINES_PER_BLOCK; ++i) {
        if (linemap[i] != 0) return i;
      }
      return IMMIX_LINES_PER_BLOCK;
  }

  // Quick benchmark suggests we can use the line-mark map
  // to skip full blocks at a rate of 3 microseconds per 2 MB.
  // Use of SIMD could probably reduce that to ~100 ns per MB.
  //                                         ~~ 100 us per GB

  // Invariant: cell size is less than one line.
  virtual void* allocate_cell(typemap* typeinfo) {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.

    if (try_establish_alloc_precondition(&small_bumper, cell_size)) {
      return allocate_cell_prechecked(typeinfo);
    } else {
      return allocate_cell_slowpath(typeinfo);
    }
  }

  // Invariant: N is less than one line.
  template <int N>
  void* allocate_cell_N(typemap* typeinfo) {
    if (try_establish_alloc_precondition(&small_bumper, N)) {
      return allocate_cell_prechecked_N<N>(typeinfo);
    } else {
      return allocate_cell_slowpath(typeinfo);
    }
  }

  virtual void* allocate_cell_16(typemap* typeinfo) { return allocate_cell_N<16>(typeinfo); }
  virtual void* allocate_cell_32(typemap* typeinfo) { return allocate_cell_N<32>(typeinfo); }
  virtual void* allocate_cell_48(typemap* typeinfo) { return allocate_cell_N<48>(typeinfo); }

  void* allocate_cell_slowpath(typemap* typeinfo) __attribute__((noinline))
  {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.

    //fprintf(gclog, "allocate_cell_slowpath triggering immix gc\n");
    gcglobals.num_gcs_triggered_involuntarily++;
    this->immix_gc();
    //fprintf(gclog, "allocate_cell_slowpath triggered immix gc\n");
    //printf("allocate_cell_slowpath trying to establish cell precond\n"); fflush(stdout);

    if (!try_establish_alloc_precondition(&small_bumper, cell_size)) {
      helpers::oops_we_died_from_heap_starvation(); return NULL;
    }

    //fprintf(gclog, "gc collection freed space for cell, now have %lld\n", curr->free_size());
    //fflush(gclog);

    /*
    if (FOSTER_GC_EFFIC_HISTOGRAMS) {
       double reclaimed = double(curr->free_size()) / double(curr->get_size());
       int percent = int(reclaimed * 100.0);
       LOCAL_HISTOGRAM_PERCENTAGE("gc-reclaimed-pct", percent);
    }
    */

    return allocate_cell_prechecked(typeinfo);
  }

  virtual void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) {
    int64_t slot_size = elt_typeinfo->cell_size; // note the name change!
    int64_t req_bytes = array_size_for(n, slot_size);

    //fprintf(gclog, "allocating array, %d elts * %d b = %d bytes\n", n, slot_size, req_bytes);

    if (false && FOSTER_GC_ALLOC_HISTOGRAMS) {
      LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-alloc-array", (int) req_bytes, 1, 33000000, 128);
    }

    if (req_bytes <= IMMIX_LINE_SIZE) {
      return allocate_array_into_bumper(&small_bumper, elt_typeinfo, n, req_bytes, init);
    } else if (req_bytes > (1 << 13)) {
      // The Immix paper, since it built on top of Jikes RVM, uses an 8 KB
      // threshold to distinguish medium-sized allocations from large ones.
      return laa.allocate_array(elt_typeinfo, n, req_bytes, init, common.get_mark_value(), this);
    } else {
      // If it's not small and it's not large, it must be medium.
      return allocate_array_into_bumper(&medium_bumper, elt_typeinfo, n, req_bytes, init);
    }
  }

  void* allocate_array_into_bumper(bump_allocator* bumper, typemap* elt_typeinfo, int64_t n, int64_t req_bytes, bool init) {
    if (try_establish_alloc_precondition(bumper, req_bytes)) {
      return helpers::allocate_array_prechecked(bumper, elt_typeinfo, n, req_bytes, common.get_mark_value(), init);
    } else {
      gcglobals.num_gcs_triggered_involuntarily++;
      this->immix_gc();
      if (try_establish_alloc_precondition(bumper, req_bytes)) {
        //fprintf(gclog, "gc collection freed space for array, now have %lld\n", curr->free_size());
        //fflush(gclog);
        return helpers::allocate_array_prechecked(bumper, elt_typeinfo, n, req_bytes, common.get_mark_value(), init);
      } else { helpers::oops_we_died_from_heap_starvation(); return NULL; }
    }
  }

  // }}}

  virtual tidy* tidy_for(tori* t) { return (tidy*) t; }

/*
      inline tidy* tidy_for_granule(size_t g) { return (tidy*) offset(range.base, g * 16); }

      inline size_t granule_for(tori* t) {
        return distance(range.base, (void*) t) / 16;
      }

      inline tidy* tidy_for(tori* t) {
        if (!FOSTER_GC_TRACK_BITMAPS) return (tidy*) t; // assume no interior pointers...

        size_t granule = granule_for(t);
        if (obj_start.get_bit(granule)) {
          return (tidy*) t;
        }
        //fprintf(gclog, "granule for %p is %d, prev is %d mapping to %p\n", t, granule,
        //  obj_start.prev_bit_onebyone(granule), tidy_for_granule(obj_start.prev_bit_onebyone(granule)));
        //fflush(gclog);
        return tidy_for_granule(obj_start.prev_bit_onebyone(granule));
      }
      */

  void clear_mark_bits_for_space() {
    // Could filter out clean blocks, which by definition are clean because
    // their mark bits are all clear, but preliminary testing suggested it
    // wasn't faster than unconditional bulk clearing.
    // Maybe the branch mispredict hurts more than the memory traffic?
#define FOSTER_TOBECLEARED
#ifndef FOSTER_TOBECLEARED
    for (auto f15 : frame15s) {
      clear_linemap(linemap_for_frame15_id(frame15_id_of(f15)));
      unmark_frame15(f15);
    }

    for (auto f21 : frame21s) {
      frame15_id fid = frame15_id_of(f21);
      // Note: the first frame is the metadata frame, so we skip it.
      for (int i = 1; i < IMMIX_F15_PER_F21; ++i) {
        clear_linemap(linemap_for_frame15_id(fid + i));
      }

      unmark_frame21(f21);
    }
#else
    for (auto f15 : to_be_cleared) {
      clear_linemap(linemap_for_frame15_id(frame15_id_of(f15)));
    }
    to_be_cleared.clear();
#endif
  }

  void immix_gc() {

    //printf("GC\n");
    //fprintf(gclog, "GC\n");

    base::TimeTicks gcstart = now();
#if ENABLE_GC_TIMING_TICKS
    int64_t t0 = __foster_getticks();
#endif

    auto num_marked_at_start = gcglobals.num_objects_marked_total;
    if (ENABLE_GCLOG) {
      fprintf(gclog, ">>>>>>> visiting gc roots on current stack\n"); fflush(gclog);
    }

    //worklist.initialize();
    common.flip_current_mark_bits_value();

    auto deltaClearMarkBits = timed([this] {
      // Before we begin tracing, we need to establish the invariant that
      // any line which might be free should be unmarked.
      // The simple way of doing so would be to clear all the mark bits
      // for this space. However, doing so can be wasteful if the space is
      // mostly unused and therefore remains always clean. So we do something
      // a little more subtle. First, clean frames by definition are unmarked.
      // So we only need to clear the mark bits for recycled frames and
      // formerly-clean frames that were allocated into since the last GC.
      clear_mark_bits_for_space();
    });

    auto phaseStartTime = now();
#if FOSTER_GC_TIME_HISTOGRAMS && ENABLE_GC_TIMING_TICKS
    int64_t phaseStartTicks = __foster_getticks();
#endif


    // TODO check condemned set instead of assuming true
    uint64_t numRemSetRoots = common.process_remset<true>(this, incoming_ptr_addrs);

    visitGCRoots(__builtin_frame_address(0), this);

#if FOSTER_GC_TIME_HISTOGRAMS && ENABLE_GC_TIMING_TICKS
    LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-rootscan-ticks", __foster_getticks_elapsed(phaseStartTicks, __foster_getticks()),  0, 60000000, 256);
#endif

    foster_bare_coro** coro_slot = __foster_get_current_coro_slot();
    foster_bare_coro*  coro = *coro_slot;
    if (coro) {
      if (ENABLE_GCLOG) {
        fprintf(gclog, "==========visiting current coro: %p\n", coro); fflush(gclog);
      }
      this->visit_root((unchecked_ptr*)coro_slot, NULL);
      if (ENABLE_GCLOG) {
        fprintf(gclog, "==========visited current coro: %p\n", coro); fflush(gclog);
      }
    }

    immix_worklist.process(this);

    auto deltaRecursiveMarking = now() - phaseStartTime;
    phaseStartTime = now();
#if FOSTER_GC_TIME_HISTOGRAMS && ENABLE_GC_TIMING_TICKS
    phaseStartTicks = __foster_getticks();
#endif
    // Coarse grained sweep, post-collection
    {
    // The current block will probably get marked recycled;
    // rather than trying to stop it, we just accept it and reset the base ptr
    // so that the next allocation will trigger a fetch of a new block to use.
    clear_current_blocks();

    // These vectors will get filled by the calls to inspect_*_postgc().
    recycled_frame15s.clear();
    clean_frame15s.clear();
    clean_frame21s.clear();
    local_frame15_allocator.clear();
    laa.sweep_arrays(common.get_mark_value());

    auto inspectFrame15Start = now();
    tracking.iter_frame15( [this](frame15* f15) {
      this->inspect_frame15_postgc(frame15_id_of(f15), f15);
    });
    auto inspectFrame15Time = now() - inspectFrame15Start;

    auto inspectFrame21Start = now();

    tracking.iter_coalesced_frame21([this](frame21* f21) {
      inspect_frame21_postgc(f21);
    });
    auto inspectFrame21Time = now() - inspectFrame21Start;

    auto deltaPostMarkingCleanup = now() - phaseStartTime;
#if FOSTER_GC_TIME_HISTOGRAMS && ENABLE_GC_TIMING_TICKS
    LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-postgc-ticks", __foster_getticks_elapsed(phaseStartTicks, __foster_getticks()),  0, 60000000, 256);
#endif
    //if (TRACK_BYTES_KEPT_ENTRIES) { hpstats.bytes_kept_per_gc.record_sample(next->used_size()); }


#if (ENABLE_GCLOG || ENABLE_GCLOG_ENDGC)
      size_t frame15s_total = tracking.logical_frame15s();
      auto total_heap_size = foster::humanize_s(double(frame15s_total * (1 << 15)), "B");
      size_t frame15s_kept = frame15s_total - (recycled_frame15s.size() + frame15s_in_reserve_clean());
      auto total_live_size = foster::humanize_s(double(frame15s_kept) * (1 << 15), "B");

      fprintf(gclog, "logically %zu frame15s, comprised of %zu frame21s and %zu actual frame15s\n", frame15s_total,
          tracking.count_frame21s(), tracking.physical_frame15s());
      describe_frame15s_count("tracking  ", frame15s_total);
      describe_frame15s_count("  recycled", frame15s_in_reserve_recycled());
      describe_frame15s_count("  clean   ", frame15s_in_reserve_clean());
      fprintf(gclog, "tracking %d f21s, ended with %d clean f21s\n", tracking.count_frame21s(), clean_frame21s.size());

      fprintf(gclog, "%lu recycled, %lu clean f15 + %lu clean f21; %d total (%d f21) => (%zu f15 @ %s kept / %s)",
          recycled_frame15s.size(), clean_frame15s.size(), clean_frame21s.size(),
          frame15s_total, tracking.count_frame21s(),
          frame15s_kept, total_live_size.c_str(), total_heap_size.c_str());
      if (ENABLE_GC_TIMING) {
        auto delta = now() - gcstart;
        fprintf(gclog, ", took %ld us which was %f%% premark, %f%% marking, %f%% post-mark",
          delta.InMicroseconds(),
          double(deltaClearMarkBits.InMicroseconds() * 100.0)/double(delta.InMicroseconds()),
          double(deltaRecursiveMarking.InMicroseconds() * 100.0)/double(delta.InMicroseconds()),
          double(deltaPostMarkingCleanup.InMicroseconds() * 100.0)/double(delta.InMicroseconds()));
      }
      fprintf(gclog, "\n");

      if (ENABLE_GC_TIMING) {
        fprintf(gclog, "\ttook %ld us inspecting frame15s, %ld us inspecting frame21s\n",
            inspectFrame15Time.InMicroseconds(), inspectFrame21Time.InMicroseconds());
      }

#   if TRACK_NUM_OBJECTS_MARKED
        fprintf(gclog, "\t%d objects marked in this GC cycle, %d marked overall\n",
                gcglobals.num_objects_marked_total - num_marked_at_start,
                gcglobals.num_objects_marked_total);
#   endif
#   if TRACK_NUM_REMSET_ROOTS
        fprintf(gclog, "\t%lu objects identified in remset\n", numRemSetRoots);
#   endif
      fprintf(gclog, "\t/endgc\n\n");
      fflush(gclog);
#endif
    }

    if (ENABLE_GC_TIMING) {
      auto delta = now() - gcstart;
      if (FOSTER_GC_TIME_HISTOGRAMS) {
        LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-pause-micros", delta.InMicroseconds(),  0, 60000000, 256);
      }
      gcglobals.gc_time += delta;
    }

#if ENABLE_GC_TIMING_TICKS
    int64_t t1 = __foster_getticks();
    if (FOSTER_GC_TIME_HISTOGRAMS) {
      LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-pause-ticks", __foster_getticks_elapsed(t0, t1),  0, 60000000, 256);
    }
    gcglobals.subheap_ticks += __foster_getticks_elapsed(t0, t1);
#endif

    gcglobals.num_gcs_triggered += 1;
  }

  void describe_frame15s_count(const char* start, size_t f15s) {
    auto h = foster::humanize_s(double(f15s) * (1 << 15), "B");
    fprintf(gclog, "%s: %6zd f15s == %s\n", start, f15s, h.c_str());
  }
  size_t frame15s_in_reserve_recycled() { return recycled_frame15s.size(); }
  size_t frame15s_in_reserve_clean() { return clean_frame15s.size() + (clean_frame21s.size() * IMMIX_ACTIVE_F15_PER_F21); }

  void inspect_frame21_postgc(frame21* f21) {
    bool is_frame21_entirely_clear = is_linemap_clear(f21);
    if (is_frame21_entirely_clear) {
      clean_frame21s.push_back(f21);
      // TODO set frameinfo?
    } else {
      // Handle the component frame15s individually.
      frame15_id fid = frame15_id_of(f21);
      for (int i = 1; i < IMMIX_F15_PER_F21; ++i) {
        // Because we can trigger GCs before reaching the space limit for a heap,
        // some of the frame15s for a f21 might not yet be used. If so, we should
        // skip 'em.
        frame15* f15 = frame15_for_frame15_id(fid + i);
        if (heap_for(f15) != this) { continue; }

        inspect_frame15_postgc(fid + i, f15);
      }
    }
  }

  void inspect_frame15_postgc(frame15_id fid, frame15* f15) {
    uint8_t* linemap = linemap_for_frame15_id(fid);
    auto num_marked_lines = count_marked_lines_for_frame15(linemap);

    if (ENABLE_GCLOG) {
      fprintf(gclog, "frame %u: ", fid);
      for(int i = 0;i < IMMIX_LINES_PER_BLOCK; ++i) { fprintf(gclog, "%c", (linemap[i] == 0) ? '_' : 'd'); }
      fprintf(gclog, "\n");
    }

    // Due to conservative line marking, the first line after every
    // sequence of marked lines must be treated as unavailable.
    // ddddddddddd : 0 holes, 0 conservatively marked lines
    // ___________ : 1 hole,  0 conservatively marked lines
    // ddddd______ : 1 hole,  1 conservatively marked line
    // ______ddddd : 1 hole,  0 conservatively marked line
    // __dd__dd__d : 3 holes, 2 conservatively marked lines
    // d_dd__dd__d : 3 holes, 3 conservatively marked lines
    // As the above indicates, the first hole is not counted if it starts the
    // block; otherwise, each hole contributes one line lost to cons marking.
    auto finfo = frame15_info_for(f15);
    finfo->num_marked_lines_at_last_collection = num_marked_lines;

    if (num_marked_lines == 0) {
      clean_frame15s.push_back(f15);
      finfo->num_available_lines_at_last_collection = IMMIX_LINES_PER_BLOCK;
    } else {
#if MARK_EXACT
      auto conservative_adjustment = 0;
#else
      auto num_holes = count_holes_in_linemap_for_frame15(linemap);
      auto conservative_adjustment = num_holes - (linemap[0] == 0);
#endif
      auto num_available_lines = (IMMIX_LINES_PER_BLOCK - num_marked_lines) - conservative_adjustment;

      finfo->num_available_lines_at_last_collection = num_available_lines;

#ifdef FOSTER_TOBECLEARED
      to_be_cleared.push_back(f15);
#endif

      if (num_available_lines == 0) {
        // no free lines; just skip
      } else {
        if (ENABLE_GCLOG) {
          fprintf(gclog, "Adding frame %p to recycled list; n marked = %d, n avail = %d\n", f15, num_marked_lines, num_available_lines);
        }
        recycled_frame15s.push_back(f15);
      }

      // TODO increment mark histogram
    }

    // TODO clear card map bytes when sweeping blocks or deallocating arrays.
  }

  void add_subheap_handle(heap_handle<immix_heap>* subheap) {
    subheaps.push_back(subheap);
  }

  void scan_cell(heap_cell* cell, int depth) {
    return common.scan_cell(this, cell, depth);
  }

  virtual void remember_outof(void** slot, void* val) {
    auto mdb = metadata_block_for_slot((void*) slot);
    uint8_t* cards = (uint8_t*) mdb->cardmap;
    cards[ line_offset_within_f21((void*) slot) ] = 1;
  }

  virtual void remember_into(void** slot) {
    //frames_pointing_here.insert(frame15_id_of((void*) slot));
    incoming_ptr_addrs.insert((tori**) slot);
  }

  void gc_and_shrink() {
    // Establish the invariant that live frames/arrays are suitably marked.
    this->immix_gc();

    std::vector<frame15*> keep_frame15s;
    std::vector<frame21*> keep_frame21s;

    // Frames that are unmarked will be freed as appropriate;
    // marked frames will be kept.
    tracking.iter_frame15( [&](frame15* f15) {
      if (is_linemap15_clear(f15)) {
        global_frame15_allocator.give_frame15(f15);
      } else {
        keep_frame15s.push_back(f15);
      }
    });

    tracking.iter_coalesced_frame21( [&](frame21* f21) {
      if (is_linemap_clear(f21)) {
        // We return memory directly to the OS, not to the global allocator.
        base::AlignedFree(f21);
      } else {
        keep_frame21s.push_back(f21);
      }
    });

    // Adjust frame limit counts, accounting for frames we're going to keep.
    lim->frame15s_left += tracking.logical_frame15s();
    lim->frame15s_left -= (keep_frame15s.size() + keep_frame21s.size() * IMMIX_ACTIVE_F15_PER_F21);

    // Get rid of everything except the frames we wanted to keep.
    tracking.clear();
    for (auto f : keep_frame15s) { tracking.add_frame15(f); }
    for (auto f : keep_frame21s) { tracking.add_frame21(f); }
    clear_current_blocks();

    recycled_frame15s.clear();
    clean_frame15s.clear();
    clean_frame21s.clear();
    to_be_cleared.clear();
    local_frame15_allocator.clear();
    laa.sweep_arrays(common.get_mark_value());
    // TODO remembered sets?
  }

public:
  // How many are we allowed to allocate before being forced to GC & reuse?
  byte_limit* lim;

  immix_common common;

private:
  // These bumpers point into particular frame15s.
  bump_allocator small_bumper;
  bump_allocator medium_bumper;

  large_array_allocator laa;

  // Tracks the frames that belong to this space: used, unused, clean, & recycled.
  immix_frame_tracking tracking;

  // The next few vectors store the frames that the previous collection
  // identified as being viable candidates for allocation into.

  // For now, we'll represent these as explicit lists, and reset them
  // after each stop-the-world collection.
  // In a concurrent setting, we'd probably have an explicit status word for
  // each frame15info, and use transitions of the concurrently-computed status
  // to drive transfers between such cached lists.
  // These two lists can contain local and global frame15s.
  std::vector<frame15*> recycled_frame15s;
  std::vector<frame15*> clean_frame15s;

  std::vector<frame21*> clean_frame21s;

  // This stores frames that were deemed recyclable or full at the
  // last collection. These need their linemaps cleared before the
  // next GC cycle occurs. Clearing the marks cannot be done eagerly
  // because recycling allocation needs marks to work properly.
  std::vector<frame15*> to_be_cleared;

  // This allocator wraps one frame21 at a time and doles it out as frame15s.
  // For now, this means in practice that subheaps will usually reserve 2 MB
  // of address space at a time, even though they only use 32 KB at a time.
  // The main benefit of doing so is (slightly) lower metadata costs and
  // higher locality.
  frame15_allocator local_frame15_allocator;

  // The points-into remembered set; each frame in this set needs to have its
  // card table inspected for pointers that actually point here.
  //std::set<frame15_id> frames_pointing_here;
  std::set<tori**> incoming_ptr_addrs;

  std::vector<heap_handle<immix_heap>*> subheaps;

  // immix_space_end
};

void immix_worklist::process(immix_heap* target) {
  while (!empty()) {
    heap_cell* cell = peek_front();
    advance();
    target->scan_cell(cell, kFosterGCMaxDepth);
  }
  initialize();
}

#include "foster_gc_backtrace_x86-inl.h"

// {{{ Walks the call stack, calling visitor->visit_root() along the way.
void visitGCRoots(void* start_frame, immix_heap* visitor) {
  enum { MAX_NUM_RET_ADDRS = 1024 };
  // Garbage collection requires 16+ KB of stack space due to these arrays.
  ret_addr  retaddrs[MAX_NUM_RET_ADDRS];
  frameinfo frames[MAX_NUM_RET_ADDRS];

  // Collect frame pointers and return addresses
  // for the current call stack.
  int nFrames = foster_backtrace((frameinfo*) start_frame, frames, MAX_NUM_RET_ADDRS);
  if (nFrames == MAX_NUM_RET_ADDRS) {
    gcglobals.num_big_stackwalks += 1;
  }
  if (FOSTER_GC_TIME_HISTOGRAMS) {
    LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-stackscan-frames", nFrames,  0, 60000000, 256);
  }

  const bool SANITY_CHECK_CUSTOM_BACKTRACE = false;
  if (SANITY_CHECK_CUSTOM_BACKTRACE) {
    // backtrace() fails when called from a coroutine's stack...
    int numRetAddrs = backtrace((void**)&retaddrs, MAX_NUM_RET_ADDRS);
    if (ENABLE_GCLOG) {
      for (int i = 0; i < numRetAddrs; ++i) {
        fprintf(gclog, "backtrace: %p\n", retaddrs[i]);
      }
      for (int i = 0; i < nFrames; ++i) {
        fprintf(gclog, "           %p\n", frames[i].retaddr);
      }
    }
    int diff = numRetAddrs - nFrames;
    for (int i = 0; i < numRetAddrs; ++i) {
      if (frames[i].retaddr != retaddrs[diff + i]) {
        fprintf(gclog, "custom + system backtraces disagree: %p vs %p, diff %d\n", frames[diff + i].retaddr, retaddrs[i], diff);
        exit(1);
      }
    }
  }

  // Use the collected return addresses to look up a safe point
  // cluster map, which gives offsets from the corresponding
  // frame pointer at which we will find pointers to be scanned.

  // For now, we must disable frame pointer elimination
  // to ensure that we can calculate the stack pointer
  // (which requires that we have a frame pointer).
  // It would be nice to eventually allow FPE and use debug
  // info (unwind tables) to reconstruct frame sizes.
  // But, judging by
  // http://mituzas.lt/2009/07/26/on-binaries-and-fomit-frame-pointer/
  // the performance gain from FPE is only on the order of
  // 1 to 3%, so it's not a critical optimization.
  //
  // Note that while LLVM's GC plugin architecture tells us
  // frame sizes for Foster functions, and thus lets us
  // theoretically reconstruct frame boundaries once we
  // reach the land of Foster, we still need "a few"
  // frame pointers to get from Here to There.
  //
  // If we were willing to accept a dependency on libgcc,
  // we could reuse the _Unwind_Backtrace function to unwind
  // past libfoster frames and then use LLVM's computed
  // stack frame sizes to crawl the rest of the stack.

  for (int i = 0; i < nFrames; ++i) {
    ret_addr safePointAddr = frames[i].retaddr;
    frameptr fp = (frameptr) frames[i].frameptr;

    const stackmap::PointCluster* pc = gcglobals.clusterForAddress[safePointAddr];
    if (!pc) {
      if (ENABLE_GCLOG) {
        fprintf(gclog, "no point cluster for address %p with frame ptr%p\n", safePointAddr, fp);
      }
      continue;
    }

    if (ENABLE_GCLOG) {
      fprintf(gclog, "\nframe %d: retaddr %p, frame ptr %p: live count w/meta %d, w/o %d\n",
        i, safePointAddr, fp,
        pc->liveCountWithMetadata, pc->liveCountWithoutMetadata);
    }

    const void* const* ms = pc->getMetadataStart();
    const int32_t    * lo = pc->getLiveOffsetWithMetaStart();
    int32_t frameSize = pc->frameSize;
    for (int a = 0; a < pc->liveCountWithMetadata; ++a) {
      int32_t     off = lo[a];
      const void*   m = ms[a];
      void*  rootaddr = offset(fp, off);

      visitor->visit_root(static_cast<unchecked_ptr*>(rootaddr),
                          static_cast<const char*>(m));
    }

    gc_assert(pc->liveCountWithoutMetadata == 0,
                  "TODO: scan pointer w/o metadata");
  }
}
// }}}

/////////////////////////////////////////////////////////////////
////////////////////// coro functions ///////////////////////////
//////////////////////////////////////////////////////////////{{{

// coro_transfer (using CORO_ASM) pushes a fixed number
// of registers on the stack before switching stacks and jumping.
// Because coro_transfer is marked noinline, the first register
// implicitly pushed is the old %eip, and the first register
// explicitly pushed is %ebp /  %rbp, thus forming an x86 stack frame.
void* coro_topmost_frame_pointer(foster_bare_coro* coro) {
  // If the coro status is "running", we should scan the coro
  // but not its stack (since the stack will be examined from ::gc()).
  // TODO when multithreading, running coros should be stamed with
  // the id of the thread running them, so that other threads will
  // know not to scan underneath another running thread.
  gc_assert(coro_status(coro) == FOSTER_CORO_SUSPENDED
         || coro_status(coro) == FOSTER_CORO_DORMANT,
           "can only get topmost frame pointer from "
           "suspended or dormant coro!");
  void** sp = coro_ctx(coro).sp;
  #if __amd64
  const int NUM_SAVED = 6;
  #else // CORO_WIN_TIB : += 3
  const int NUM_SAVED = 4;
  #endif

  return &sp[NUM_SAVED - 1];
}

const char* coro_status_name(foster_bare_coro* c) {
  switch (coro_status(c)) {
  case FOSTER_CORO_INVALID: return "invalid";
  case FOSTER_CORO_SUSPENDED: return "suspended";
  case FOSTER_CORO_DORMANT: return "dormant";
  case FOSTER_CORO_RUNNING: return "running";
  case FOSTER_CORO_DEAD: return "dead";
  default: return "unknown";
  }
}

void coro_print(foster_bare_coro* coro) {
  if (!coro) return;
  fprintf(gclog, "coro %p: ", coro); fflush(stdout);
  fprintf(gclog, "parent %p, status %s, fn %p\n",
      foster::runtime::coro_parent(coro),
      coro_status_name(coro),
      foster::runtime::coro_fn(coro));
}

void coro_dump(foster_bare_coro* coro) {
  if (!coro) {
    fprintf(gclog, "cannot dump NULL coro ptr!\n");
  } else if (ENABLE_GCLOG) {
    coro_print(coro);
  }
}

// Declared in libfoster_coro.cpp
extern "C"
void foster_coro_ensure_self_reference(foster_bare_coro* coro);

// A thin wrapper around visitGCRoots.
void coro_visitGCRoots(foster_bare_coro* coro, immix_heap* visitor) {
  coro_dump(coro);
  if (!coro
   || foster::runtime::coro_status(coro) == FOSTER_CORO_INVALID
   || foster::runtime::coro_status(coro) == FOSTER_CORO_DEAD
   || foster::runtime::coro_status(coro) == FOSTER_CORO_RUNNING) {
    // No need to scan the coro's stack...
    return;
  }

  foster_coro_ensure_self_reference(coro);

  // If we've made it this far, then the coroutine is owned by us,
  // and is either dormant or suspended. We don't scan
  // the stack of a running coro, since we should already have done so.
  // But we will trace back the coro invocation chain and scan other stacks.

  // extract frame pointer from ctx, and visit its stack.
  void* frameptr = coro_topmost_frame_pointer(coro);
  gc_assert(frameptr != NULL, "coro frame ptr shouldn't be NULL!");

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanning coro (%p, fn=%p, %s) stack from %p\n",
        coro, foster::runtime::coro_fn(coro), coro_status_name(coro), frameptr);
  }

  visitGCRoots(frameptr, visitor);

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanned coro stack from %p\n", frameptr);
    fflush(gclog);
  }
}

//////////////////////////////////////////////////////////////}}}

// {{{ get_static_data_range
#if OS_LINUX
// http://stackoverflow.com/questions/4308996/finding-the-address-range-of-the-data-segment
// Sadly, the etext symbol sometimes comes after certain rodata segments;
// we take a conservative approach and include all the binary's text and data.
extern "C" char __executable_start, end;
void get_static_data_range(memory_range& r) {
  r.base  = &__executable_start;
  r.bound = &end;
}
#elif OS_MACOSX
// http://stackoverflow.com/questions/1765969/unable-to-locate-definition-of-etext-edata-end
//
// However, these return static (aka file) addresses; to find the actual
// runtime addresses, we need to query the dynamic loader to find the offset
// it applied when loading this process.
uintptr_t get_base();
uintptr_t get_offset();

#include <mach-o/getsect.h>
#include <mach-o/dyld.h>
#include <sys/param.h>
// See also http://opensource.apple.com//source/cctools/cctools-822/libmacho/get_end.c
void get_static_data_range(memory_range& r) {
  uintptr_t offset = get_offset();
  r.base  = (void*) (get_base() + offset);
  r.bound = (void*) (get_end()  + offset);

  if (!r.contains((void*) &get_static_data_range)) {
    fprintf(gclog, "WARNING: computation of static data ranges seems to have gone awry.\n");
    fprintf(gclog, "         The most likely consequence is that the program "
                   "will exit with status code 99.\n");
  }
}

// http://stackoverflow.com/questions/10301542/getting-process-base-address-in-mac-osx
uintptr_t get_base() {
  return getsegbyname("__TEXT")->vmaddr;
}

uintptr_t get_offset() {
  char path[MAXPATHLEN];
  uint32_t size = sizeof(path);
  if (_NSGetExecutablePath(path, &size) != 0) {
    // Due to nested links, MAXPATHLEN wasn't enough! See also `man 3 dyld`.
    return 0;
  }
  for (uint32_t i = 0; i < _dyld_image_count(); i++) {
    if (strcmp(_dyld_get_image_name(i), path) == 0) {
      return _dyld_get_image_vmaddr_slide(i);
    }
  }
  return 0;
}

#else
#error TODO: Use Win32 to find boundaries of data segment range.
#endif
// }}}

// {{{ GC startup & shutdown
void register_stackmaps(ClusterMap&); // see foster_gc_stackmaps.cpp

int address_space_prefix_size_log() {
  if (sizeof(void*) == 4) { return 32; }
  if (sizeof(void*) == 8) { return 47; }
  exit(3); return 0;
}

template<typename T>
T* allocate_lazily_zero_mapped(size_t num_elts) {
#if OS_MACOSX
  // On macOS, multi-page malloc() will lazily zero-initialize:
  // https://developer.apple.com/library/content/documentation/Performance/Conceptual/ManagingMemory/Articles/MemoryAlloc.html
  return (T*) malloc(sizeof(T) * num_elts);
#elif OS_LINUX
  T* rv = (T*) mmap(NULL, sizeof(T) * num_elts,
    PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);

  if (rv == MAP_FAILED) {
    perror("mmap failed...");
  }
  return rv;
#else
#error Need to determine how to lazy allocate pages
#endif
}

void initialize(void* stack_highest_addr) {
  gcglobals.init_start = base::TimeTicks::Now();
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");
  if (!base::TimeTicks::IsHighResolution()) {
    fprintf(gclog, "(warning: using low-resolution timer)\n");
  }

  base::StatisticsRecorder::Initialize();

  gcglobals.allocator = new immix_space(new byte_limit(gSEMISPACE_SIZE()));
  gcglobals.default_allocator = gcglobals.allocator;

  gcglobals.had_problems = false;

  register_stackmaps(gcglobals.clusterForAddress);

  gcglobals.lazy_mapped_frame15info             = allocate_lazily_zero_mapped<frame15info>(size_t(1) << (address_space_prefix_size_log() - 15));
  //gcglobals.lazy_mapped_frame15info_associated  = allocate_lazily_zero_mapped<void*>(      size_t(1) << (address_space_prefix_size_log() - 15));

  gcglobals.gc_time = base::TimeTicks();
  gcglobals.runtime_start = base::TimeTicks::Now();
  gcglobals.num_gcs_triggered = 0;
  gcglobals.num_gcs_triggered_involuntarily = 0;
  gcglobals.num_big_stackwalks = 0;
  gcglobals.subheap_ticks = 0.0;
  gcglobals.num_allocations = 0;
  gcglobals.num_alloc_bytes = 0;
  gcglobals.write_barrier_phase0_hits = 0;
  gcglobals.write_barrier_phase1_hits = 0;
  gcglobals.num_objects_marked_total = 0;
}



void gclog_time(const char* msg, base::TimeDelta d, FILE* json) {
  fprintf(gclog, "%s: %2ld.%03ld s\n", msg,
          long(d.InSeconds()),
          long(d.InMilliseconds() - (d.InSeconds() * 1000)));
  if (json) {
  fprintf(json, "'%s_s' : %2ld.%03ld,\n", msg,
          long(d.InSeconds()),
          long(d.InMilliseconds() - (d.InSeconds() * 1000)));
  fprintf(json, "'%s_ms': %2ld.%03ld,\n", msg,
          long(d.InMilliseconds()),
          long(d.InMicroseconds() - (d.InMilliseconds() * 1000)));
  }
}

void dump_alloc_site_stats(FILE* stats) {
  if (!gcglobals.alloc_site_counters.empty()) {
    fprintf(stats, "'allocation_sites' : [\n");
    for (auto it : gcglobals.alloc_site_counters) {
      typemap* map = it.first.second;
      int64_t bytes_allocated = map->cell_size * it.second;
      fprintf(stats, "{ 'typemap' : %p , 'allocations' : %12" PRId64 ", 'alloc_size':%" PRId64
                      ", 'bytes_allocated': %10" PRId64
                      // ", 'alloc_percent':%f,"
                      ,
                      map, it.second, map->cell_size, bytes_allocated
                      //, (double(bytes_allocated) * 100.0) / approx_bytes
                      );
      fprintf(stats, "  'from' : \"%s\" },\n", it.first.first);
    }
    fprintf(stats, "],\n");
  }
}

FILE* print_timing_stats() {
  base::TimeTicks fin = base::TimeTicks::Now();
  base::TimeDelta total_elapsed = fin - gcglobals.init_start;
  base::TimeDelta  init_elapsed = gcglobals.runtime_start - gcglobals.init_start;
  base::TimeDelta    gc_elapsed = gcglobals.gc_time - base::TimeTicks();
  base::TimeDelta   mut_elapsed = total_elapsed - gc_elapsed - init_elapsed;

  fprintf(gclog, "'Exact_Marking': %d\n", MARK_EXACT);
  fprintf(gclog, "'F15_Coalescing': %d\n", COALESCE_FRAME15S);
  fprintf(gclog, "'F21_Marking': %d\n", MARK_FRAME21S);
  fprintf(gclog, "'F21_UnsafeAssumedClean': %s\n", UNSAFE_ASSUME_F21_UNMARKED ? "true" : "false");

  FILE* json = __foster_globals.dump_json_stats_path.empty()
                ? NULL
                : fopen(__foster_globals.dump_json_stats_path.c_str(), "w");
  if (json) fprintf(json, "{\n");
  if (!json &&
      (FOSTER_GC_ALLOC_HISTOGRAMS || FOSTER_GC_TIME_HISTOGRAMS || FOSTER_GC_EFFIC_HISTOGRAMS)) {
    fprintf(gclog, "stats recorder active? %d\n", base::StatisticsRecorder::IsActive());
    auto gah = base::StatisticsRecorder::ToJSON("");
    fprintf(gclog, "GC_Alloc_Histograms : %s\n", gah.c_str());
    std::string output;
    base::StatisticsRecorder::WriteGraph("", &output);
    fprintf(gclog, "%s\n", output.c_str());
  }

  dump_alloc_site_stats(gclog);

  fprintf(gclog, "'Num_Big_Stackwalks': %d\n", gcglobals.num_big_stackwalks);
  fprintf(gclog, "'Num_GCs_Triggered': %d\n", gcglobals.num_gcs_triggered);
  fprintf(gclog, "'Num_GCs_Involuntary': %d\n", gcglobals.num_gcs_triggered_involuntarily);
  if (TRACK_NUM_ALLOCATIONS) {
    auto s = foster::humanize_s(double(gcglobals.num_allocations), "");
    fprintf(gclog, "'Num_Allocations': %s\n", s.c_str());
  }
  if (TRACK_NUM_ALLOC_BYTES) {
    auto s = foster::humanize_s(double(gcglobals.num_alloc_bytes), "B");
    fprintf(gclog, "'Num_Alloc_Bytes': %s\n", s.c_str());
  }
  if (TRACK_NUM_OBJECTS_MARKED && TRACK_NUM_ALLOCATIONS) {
    fprintf(gclog, "'MarkCons_Obj_div_Obj': %e\n",
        double(gcglobals.num_objects_marked_total) / double(gcglobals.num_allocations));
  }
  if (TRACK_NUM_OBJECTS_MARKED && TRACK_NUM_ALLOCATIONS) {
    fprintf(gclog, "'MarkCons_Obj_div_Bytes': %e\n",
        double(gcglobals.num_objects_marked_total) / double(gcglobals.num_alloc_bytes));
  }
  if (TRACK_WRITE_BARRIER_COUNTS) {
    fprintf(gclog, "'Num_Write_Barriers_Fast': %lu\n", (gcglobals.write_barrier_phase0_hits - gcglobals.write_barrier_phase1_hits));
    fprintf(gclog, "'Num_Write_Barriers_Slow': %lu\n",  gcglobals.write_barrier_phase1_hits);
  }
  if (ENABLE_GC_TIMING_TICKS) {
    auto s = foster::humanize_s(gcglobals.subheap_ticks, "");
    fprintf(gclog, "'Subheap_Ticks': %s\n", s.c_str());
    if (gcglobals.num_gcs_triggered > 0) {
      auto v = foster::humanize_s(gcglobals.subheap_ticks / double(gcglobals.num_gcs_triggered), "");
      fprintf(gclog, "'Avg_GC_Ticks': %s\n", v.c_str());
    }
  }

  //fprintf(gclog, "sizeof immix_space: %lu\n", sizeof(immix_space));
  //fprintf(gclog, "sizeof immix_line_space: %lu\n", sizeof(immix_line_space));
  {
    auto x = foster::humanize_s(16, "");
    fprintf(gclog, "16 -> %s\n", x.c_str());
  }

  gclog_time("Elapsed_runtime", total_elapsed, json);
  gclog_time("Initlzn_runtime",  init_elapsed, json);
  if (ENABLE_GC_TIMING) {
    gclog_time("     GC_runtime",  gc_elapsed, json);
  }
  gclog_time("Mutator_runtime",   mut_elapsed, json);
  return json;
}

// TODO: track bytes allocated, bytes collected, max heap size,
//       max slop (alloc - reserved), peak mem use; compute % GC time.

int cleanup() {
  FILE* json = print_timing_stats();
  bool had_problems = gcglobals.had_problems;
  if (json) gcglobals.allocator->dump_stats(json);
  delete gcglobals.allocator;
  fclose(gclog); gclog = NULL;
  if (json) fprintf(json, "}\n");
  if (json) fclose(json);
  return had_problems ? 99 : 0;
}
// }}}

/////////////////////////////////////////////////////////////////

//  {{{ Debugging utilities
void gc_assert(bool cond, const char* msg) {
  if (GC_ASSERTIONS) {
    if (!cond) {
      gcglobals.allocator->dump_stats(NULL);
    }
    foster_assert(cond, msg);
  }
}

void inspect_typemap(const typemap* ti) {
  fprintf(gclog, "typemap: %p\n", ti); fflush(gclog);
  if (!ti) return;
  fprintf(gclog, "\tsize:       %" PRId64 "\n", ti->cell_size);   fflush(gclog);
  gc_assert(ti->cell_size > 0, "invalid typemap in inspect_typemap");
  fprintf(gclog, "\tname:       %s\n",   ti->name);        fflush(gclog);
  fprintf(gclog, "\tisCoro:     %d\n",   ti->isCoro);      fflush(gclog);
  fprintf(gclog, "\tisArray:    %d\n",   ti->isArray);     fflush(gclog);
  fprintf(gclog, "\tnumOffsets: %d\n",   ti->numOffsets);  fflush(gclog);
  int iters = ti->numOffsets > 128 ? 0 : ti->numOffsets;   fflush(gclog);
  for (int i = 0; i < iters; ++i) {
    fprintf(gclog, "\t@%d, ", ti->offsets[i]);
    fflush(gclog);
  }
  fprintf(gclog, "\n");
}

extern "C" void inspect_ptr_for_debugging_purposes(void* bodyvoid) {
  /*
  unsigned align = (!(intptr_t(bodyvoid) & 0x0f)) ? 16
                 : (!(intptr_t(bodyvoid) & 0x07)) ? 8
                 : (!(intptr_t(bodyvoid) & 0x03)) ? 4 : 0
                 ;
                 */
  fprintf(gclog, "<%p>\n", bodyvoid);
  fprintf(stdout, "<%p>\n", bodyvoid);
  /*
  unchecked_ptr bodyu = make_unchecked_ptr(static_cast<tori*>(bodyvoid));
  tori* body = untag(bodyu);
  if (! body) {
    fprintf(gclog, "body is (maybe tagged) null\n");
  } else {
    if (gc::gcglobals.allocator->owns(body)) {
      fprintf(gclog, "\t...this pointer is owned by the main allocator");
    } else {
      fprintf(gclog, "\t...this pointer is not owned by the main allocator, nor marked as stable!");
      goto done;
    }

    gc::heap_cell* cell = gc::heap_cell::for_tidy(gc::gcglobals.allocator->tidy_for(body));
    if (cell->is_forwarded()) {
      fprintf(gclog, "cell is forwarded to %p\n", cell->get_forwarded_body());
    } else {
      if (const gc::typemap* ti = tryGetTypemap(cell)) {
        //gc::inspect_typemap(stdout, ti);
        int iters = ti->numOffsets > 128 ? 0 : ti->numOffsets;
        for (int i = 0; i < iters; ++i) {
          fprintf(gclog, "\t@%d : %p\n", ti->offsets[i], gc::offset(bodyvoid, ti->offsets[i]));
          fflush(gclog);
        }
      } else {
        fprintf(gclog, "\tcell has no typemap, size is %lld\n", cell->cell_size());
      }
    }
  }

done:
  fprintf(gclog, "done inspecting ptr: %p\n", body);
  fflush(gclog);
  */
}
// }}}

// {{{ Pointer classification utilities
const typemap* tryGetTypemap(heap_cell* cell) {
  if (uint64_t(cell->cell_size()) < uint64_t(1<<16)) return nullptr;
  const typemap* map = cell->get_meta();
  if (GC_ASSERTIONS) {
    bool is_corrupted = (
          ((map->isCoro  != 0) && (map->isCoro  != 1))
       || ((map->isArray != 0) && (map->isArray != 1))
       || (map->numOffsets < 0)
       || (map->cell_size  < 0));
    if (is_corrupted) {
      fprintf(gclog, "Found corrupted type map:\n"); fflush(gclog);
      inspect_typemap(map);
      gc_assert(!is_corrupted, "tryGetTypemap() found corrupted typemap");
    }
  }
  return map;
}
// }}}

/////////////////////////////////////////////////////////////////

extern "C" {

// {{{ Allocation interface used by generated code
void* memalloc_cell(typemap* typeinfo) {
  if (GC_BEFORE_EVERY_MEMALLOC_CELL) {
    gcglobals.allocator->force_gc_for_debugging_purposes();
  }
  return gcglobals.allocator->allocate_cell(typeinfo);
}

void* memalloc_cell_16(typemap* typeinfo) {
  if (GC_BEFORE_EVERY_MEMALLOC_CELL) {
    gcglobals.allocator->force_gc_for_debugging_purposes();
  }
  return gcglobals.allocator->allocate_cell_16(typeinfo);
}

void* memalloc_cell_32(typemap* typeinfo) {
  if (GC_BEFORE_EVERY_MEMALLOC_CELL) {
    gcglobals.allocator->force_gc_for_debugging_purposes();
  }
  return gcglobals.allocator->allocate_cell_32(typeinfo);
}

void* memalloc_cell_48(typemap* typeinfo) {
  if (GC_BEFORE_EVERY_MEMALLOC_CELL) {
    gcglobals.allocator->force_gc_for_debugging_purposes();
  }
  return gcglobals.allocator->allocate_cell_48(typeinfo);
}

void* memalloc_array(typemap* typeinfo, int64_t n, int8_t init) {
  return gcglobals.allocator->allocate_array(typeinfo, n, (bool) init);
}

void record_memalloc_cell(typemap* typeinfo, const char* srclines) {
  gcglobals.alloc_site_counters[std::make_pair(srclines, typeinfo)]++;
}
// }}}

// Extern symbol for gdb, not direct use by generated code.
void fflush_gclog() { fflush(gclog); }

//__attribute((noinline))
immix_heap* heap_for_wb(void* val) {
  //frame15* f15 = frame15_for_frame15_id(frame15_id_of(val));
  //return *((immix_heap**)f15);

  //return heap_for_frame15info_normalonly(frame15_info_for(val), val);

  return heap_for(val);
}

immix_heap* heap_for_tidy(tidy* val) {
  return ((immix_heap**)val)[-2];
}

__attribute((noinline))
void foster_write_barrier_slowpath(immix_heap* hv, immix_heap* hs, void* val, void** slot) {
    if (TRACK_WRITE_BARRIER_COUNTS) { ++gcglobals.write_barrier_phase1_hits; }
    hv->remember_into(slot);
    //hs->remember_outof(slot, val);
}

__attribute__((always_inline))
void foster_write_barrier_generic(void* val, void** slot) /*__attribute((always_inline))*/ {
//void __attribute((always_inline)) foster_write_barrier_generic(void* val, void** slot) {
  //immix_heap* hv = heap_for_tidy((tidy*)val);
  //immix_heap* hs = heap_for_tidy((tidy*)slot);
  immix_heap* hv = heap_for_wb(val);
  immix_heap* hs = heap_for_wb((void*)slot);
  if (TRACK_WRITE_BARRIER_COUNTS) { ++gcglobals.write_barrier_phase0_hits; }
  //fprintf(gclog, "write barrier writing ptr %p from heap %p into slot %p in heap %p\n", val, hv, slot, hs); fflush(gclog);
  if (hv == hs) {
    *slot = val;
    return;
  }

  // Preconditions:
  //   val SHOULD NOT point into the same frame as slot
  //   val SHOULD NOT point into the oldest generation
  // Violations of these preconditions will not produce errors, but will result
  // in remembered sets that are larger than necessary.
  //
  // Static data (for which the immix_space* will be null)
  // must be immutable, so hs will never be null, but hv might be.
  // If hv is null (meaning static data), we don't need to remember anything,
  // since statically allocated data will never be deallocated, and can never
  // point into the program heap (by virtue of its immutability).
  if (hv) {
    foster_write_barrier_slowpath(hv, hs, val, slot);
  }
  *slot = val;
}

// We need a degree of separation between the possibly-moving
// traced immix heap, which does not currently support finalizers/destructors,
// and the fact that immix_space is a C++ object with a non-trivial "dtor".
// There's also an issue of alignment: pointers in the immix heap ought to be
// aligned (though I guess it's not strictly necessary for types without any
// constructors).
void* foster_subheap_create_raw() {
  immix_space* subheap = new immix_space(gcglobals.allocator->get_byte_limit());
  fprintf(gclog, "created subheap %p\n", subheap);
  void* alloc = malloc(sizeof(heap_handle<immix_space>));
  heap_handle<immix_space>* h = (heap_handle<immix_space>*)
    realigned_for_allocation(alloc);
  h->header           = subheap->common.get_mark_value();
  h->unaligned_malloc = alloc;
  h->body             = subheap;
  //gcglobals.allocator->add_subheap_handle(h); // TODO XXXX
  return h;
}

void* foster_subheap_create_small_raw() {
  immix_line_space* subheap = new immix_line_space(gcglobals.allocator->get_byte_limit());
  fprintf(gclog, "created small subheap %p\n", subheap);
  void* alloc = malloc(sizeof(heap_handle<heap>));
  heap_handle<heap>* h = (heap_handle<heap>*)
    realigned_for_allocation(alloc);
  h->header           = subheap->common.get_mark_value();
  h->unaligned_malloc = alloc;
  h->body             = subheap;
  //gcglobals.allocator->add_subheap_handle(h); // TODO XXXX
  return h;
}

void foster_subheap_activate_raw(void* generic_subheap) {
  // TODO make sure we properly retain (or properly remove!)
  //      a subheap that is created, installed, and then silently dropped
  //      without explicitly being destroyed.
  immix_heap* subheap = ((heap_handle<immix_heap>*) generic_subheap)->body;
  gcglobals.allocator = subheap;
  //fprintf(gclog, "activated subheap %p\n", subheap);
}

void foster_subheap_shrink_raw(void* generic_subheap) {
  auto subheap = ((heap_handle<immix_heap>*) generic_subheap)->body;
  subheap->gc_and_shrink();
  //fprintf(gclog, "shrink()-ed subheap %p\n", subheap);
}

void foster_subheap_collect_raw(void* generic_subheap) {
  auto subheap = ((heap_handle<immix_heap>*) generic_subheap)->body;
  //fprintf(gclog, "collecting subheap %p\n", subheap);
  subheap->force_gc_for_debugging_purposes();
  //fprintf(gclog, "subheap-collect done\n");
}

/*
void foster_subheap_condemn_raw(void* generic_subheap) {
  auto subheap = ((heap_handle<immix_heap>*) generic_subheap)->body;
  //fprintf(gclog, "collecting subheap %p\n", subheap);
  subheap->condemn();
  //fprintf(gclog, "subheap-collect done\n");
}
*/


} // extern "C"

void force_gc_for_debugging_purposes() {
  gcglobals.allocator->force_gc_for_debugging_purposes();
}

} // namespace foster::runtime::gc

uint8_t ctor_id_of(void* constructed) {
  gc::heap_cell* cell = gc::heap_cell::for_tidy((gc::tidy*) constructed);
  const gc::typemap* map = tryGetTypemap(cell);
  gc_assert(map, "foster_ctor_id_of() was unable to get a usable typemap");
  int8_t ctorId = map->ctorId;
  if (ctorId < 0) {
    fprintf(gc::gclog, "foster_ctor_id_of inspected bogus ctor id %d\n", ctorId);
    gc::inspect_typemap(map);
  }
  return ctorId;
}

} // namespace foster::runtime
} // namespace foster

