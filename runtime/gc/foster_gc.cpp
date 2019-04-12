// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster.h"
#include "libfoster_util.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "foster_globals.h"
#include "bitmap.h"
#include "ptr_fifo.h"

#include "build/build_config.h" // from chromium_base
#include "hdr_histogram.h"

#include "execinfo.h" // for backtrace

#include <functional>
#include <stddef.h> // offsetof

#include <sparsehash/dense_hash_set>
#include <sparsehash/dense_hash_map>

// jemalloc_pages
bool  pages_boot(void);
void* pages_map(void* addr, size_t size, size_t alignment, bool* commit);
void  pages_unmap(void* addr, size_t size);

#include <immintrin.h>

extern "C" int64_t __foster_getticks_start();
extern "C" int64_t __foster_getticks_end();
extern "C" double  __foster_getticks_elapsed(int64_t t1, int64_t t2);

extern "C" char* __foster_fosterlower_config;

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)
#define PREFETCH_FOR_WRITES(addr) __builtin_prefetch(addr, 1, 3)
#define PREFETCH_FOR_MARKING(addr) __builtin_prefetch(addr, 0, 0)

// These are defined as compile-time constants so that the compiler
// can do effective dead-code elimination. If we were JIT compiling
// the GC we could (re-)specialize these config vars at runtime...
#define ENABLE_OPPORTUNISTIC_EVACUATION 0
#define GCLOG_DETAIL 0
#define GCLOG_PRINT_LINE_MARKS 0
#define GCLOG_PRINT_LINE_HISTO 0
#define GCLOG_PRINT_USED_GROUPS 0
#define GCLOG_MUTATOR_UTILIZATION 0
#define ENABLE_GCLOG_PREP 0
#define ENABLE_GCLOG_ENDGC 1
#define PRINT_STDOUT_ON_GC 0
#define FOSTER_GC_TRACK_BITMAPS       0
#define FOSTER_GC_ALLOC_HISTOGRAMS    0
#define FOSTER_GC_TIME_HISTOGRAMS     1 // Adds ~300 cycles per collection
#define FOSTER_GC_EFFIC_HISTOGRAMS    0
#define ENABLE_GC_TIMING              1
#define ENABLE_GC_TIMING_TICKS        1 // Adds ~430 cycles per collection
#define GC_ASSERTIONS 0
#define MARK_FRAME21S                 0
#define MARK_FRAME21S_OOL             0
#define UNSAFE_ASSUME_F21_UNMARKED    false
#define TRACK_NUM_ALLOCATIONS         1
#define TRACK_NUM_ALLOC_BYTES         1
#define TRACK_NUM_REMSET_ROOTS        1
#define TRACK_NUM_OBJECTS_MARKED      1
#define TRACK_WRITE_BARRIER_COUNTS    1
#define TRACK_BYTES_KEPT_ENTRIES      0
#define TRACK_BYTES_ALLOCATED_ENTRIES 0
#define TRACK_BYTES_ALLOCATED_PINHOOK 0
#define GC_BEFORE_EVERY_MEMALLOC_CELL 0
#define USE_FIFO_SIZE 0
#define DEBUG_VERIFY_MARK_BITS        0
#define DEBUG_PRINT_ALLOCATIONS  0
#define DEBUG_INITIALIZE_ALLOCATIONS  0 // Initialize even when the middle end doesn't think it's necessary
#define ELIDE_INITIALIZE_ALLOCATIONS  0 // Unsafe: ignore requests to initialize allocated memory.
#define MEMSET_FREED_MEMORY           0 || GC_ASSERTIONS
// This included file may un/re-define these parameters, providing
// a way of easily overriding-without-overwriting the defaults.
#include "gc/foster_gc_reconfig-inl.h"

const double kFosterDefragReserveFraction = 0.01;
const ssize_t inline gSEMISPACE_SIZE() { return __foster_globals.semispace_size; }

extern void* foster__typeMapList[];

/////////////////////////////////////////////////////////////////

#include "foster_gc_utils.h"
#define ENABLE_CLOCKTIMER ENABLE_GC_TIMING
#include "clocktimer.h"

#include <list>
#include <vector>
#include <map>
#include <set>

//std::map<uint32_t, int> refPatterns;

#define IMMIX_LINE_SIZE     256
#define IMMIX_LINE_SIZE_LOG 8
#define IMMIX_LINES_PER_FRAME15_LOG 7 /*15 - 8*/
#define IMMIX_LINES_PER_FRAME15   128

#define IMMIX_LINE_FRAME15_START_LINE 5
#define IMMIX_LINES_PER_LINE_FRAME15 (IMMIX_LINES_PER_FRAME15 - IMMIX_LINE_FRAME15_START_LINE)

#define COARSE_MARK_LOG 21

#define IMMIX_F15_PER_F21 64
#define IMMIX_BYTES_PER_LINE 256
#define IMMIX_LINES_PER_BLOCK 128
#define IMMIX_GRANULES_PER_LINE (IMMIX_BYTES_PER_LINE / 16)
#define IMMIX_GRANULES_PER_BLOCK (128 * IMMIX_GRANULES_PER_LINE)
#define IMMIX_ACTIVE_F15_PER_F21 (IMMIX_F15_PER_F21 - 1)

// A "sliver" is 1024 bytes (2^10) which happens to be 64 granules.
#define IMMIX_SLIVER_SIZE_LOG 10
// 8 bytes per sliver is less than 1% space overhead.

static_assert(IMMIX_GRANULES_PER_LINE == 16,    "documenting expected values");
static_assert(IMMIX_GRANULES_PER_BLOCK == 2048, "documenting expected values");

uint64_t g_approx_lines_allocated_since_last_collection = 0;
bool g_should_compact = false;

int num_free_lines = 0; // TODO move to gcglobals

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
  ssize_t size() const { return distance(base, bound); }

  void wipe_memory(uint8_t byte) { memset(base, byte, size()); }
};

// To be suitably aligned for allocation, a pointer should be positioned
// such that the body -- after the header -- will have the proper default alignment.
// Let P be a pointer, A be the alignment in bytes, and H the header size in bytes.
// If P is aligned at default alignment, then P = kA, and P + (A - H) is aligned for allocation,
// because (P + (A - H) + H) = P + A = kA + A = (k + 1) A.
void* offset_for_allocation(void* bump) {
  return offset(bump, FOSTER_GC_DEFAULT_ALIGNMENT - HEAP_CELL_HEADER_SIZE);
}

void* realigned_for_allocation(void* bump) {
 return offset_for_allocation(roundUpToNearestMultipleWeak(bump, FOSTER_GC_DEFAULT_ALIGNMENT));
}

void* realigned_for_heap_handle(void* bump) {
  return roundUpToNearestMultipleWeak(bump, FOSTER_GC_DEFAULT_ALIGNMENT);
}

void* realigned_to_line_flat(void* bump) {
 return roundUpToNearestMultipleWeak(bump, IMMIX_LINE_SIZE);
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

struct freelist { freelist* next; };


// On a 64-bit machine, physical address space will only be 48 bits usually.
// If we use 47 of those bits, we can drop the low-order 15 bits and be left
// with 32 bits!
typedef uint32_t frame15_id;
typedef uint32_t frame21_id;

frame15_id frame15_id_of(void* p) { return frame15_id(uintptr_t(p) >> 15); }
frame21_id frame21_id_of(void* p) { return frame21_id(uintptr_t(p) >> 21); }

uintptr_t low_n_bits(uintptr_t val, uintptr_t n) { return val & ((1 << n) - 1); }

uintptr_t line_offset_within_heap(void* slot) {
  return uintptr_t(slot) >> 8;
}
uintptr_t line_offset_within_f21(void* slot) {
  return low_n_bits(uintptr_t(slot) >> 8, 21 - 8);
}

int line_offset_within_f15(void* slot) {
  return int(low_n_bits(uintptr_t(slot) >> 8, 15 - 8));
}

struct immix_line_frame15;
class frame15;
class frame21;

frame15* frame15_for_frame15_id(frame15_id f15) {
  return (frame15*)(uintptr_t(f15) << 15);
}

uint64_t sliver_id_of(void* addr) { return uint64_t(uintptr_t(addr) >> IMMIX_SLIVER_SIZE_LOG); }
void*    sliver_addr(uint64_t s) { return (void*) (s << IMMIX_SLIVER_SIZE_LOG); }
uint64_t frame15_id_to_sliver(frame15_id x) { return sliver_id_of(frame15_for_frame15_id(x)); }

// The pointer itself is the base pointer of the equivalent memory_range.
struct free_linegroup {
  void*           bound;
  free_linegroup* next;
};

int linegroup_size_in_lines(free_linegroup* g) { return distance((void*) g, g->bound) / IMMIX_BYTES_PER_LINE; }

struct used_linegroup {
  void*           base;
  int             count;

  int startline() const { return line_offset_within_f15(base); }
  int endline()   const { return line_offset_within_f15(base) + count; }

  size_t size_in_bytes() const { return count * IMMIX_BYTES_PER_LINE; }
  size_t size_in_lines() const { return count; }

  frame15_id associated_frame15_id() const { return frame15_id_of(base); }
  immix_line_frame15* associated_lineframe() const {
    return (immix_line_frame15*) frame15_for_frame15_id(associated_frame15_id());
  }

  used_linegroup singleton(int i) const {
    return used_linegroup { .base  = offset(base,  i      * IMMIX_BYTES_PER_LINE),
                            .count = 1 };
  }

  bool contains(void* slot) const { return slot > base && distance(base, slot) < size_in_bytes(); }

  void clear_line_and_object_mark_bits();
};

used_linegroup used_group_of_free_group(free_linegroup* g) {
  return {
    .base = (void*) g,
    .count = linegroup_size_in_lines(g)
  };
}

void install_free_group(bump_allocator& bumper, free_linegroup* g) {
  bumper.base  = realigned_for_allocation(g);
  bumper.bound = g->bound;
}

typedef void* ret_addr;
typedef void* frameptr;
// I've looked at using std::unordered_map or google::sparsehash instead,
// but both options lead to unacceptable binary bloat vs std::map,
// because chromium_base (etc) already uses std::map...
typedef std::map<frameptr, const stackmap::PointCluster*> ClusterMap;
// }}}

struct remset_t {
  remset_t() { dhs.set_empty_key(nullptr); }

  void insert(tori** slot) {
    buffer.push_back(slot);
    if (buffer.size() == 100) {
      consolidate(); 
    }
  }

  void consolidate() {
    for (auto slot : buffer) {
      dhs.insert(slot);
    }
    buffer.clear();
  }

  std::vector<tori**> move_to_vector() {
    consolidate();
    std::vector<tori**> slots(dhs.begin(), dhs.end());
    dhs.clear();
    return slots;
  }

  std::vector<tori**> copy_to_vector() {
    consolidate();
    std::vector<tori**> slots(dhs.begin(), dhs.end());
    dhs.clear();
    return slots;
  }

  void clear() { dhs.clear(); buffer.clear(); }
private:
  std::vector<tori**> buffer;
  google::dense_hash_set<tori**> dhs;
};

typedef uint16_t line_stamp_t;
line_stamp_t get_current_line_stamp(void* slot);

struct remset_with_obj_t {
  remset_with_obj_t() {
    dhm.set_empty_key(nullptr);
    dhm.set_deleted_key((tori**) 1);
  }

  void insert(tori** slot, tidy* obj) {
    buffer.push_back(std::make_pair(slot, std::make_pair(obj, get_current_line_stamp(obj))));
    if (buffer.size() == 100) {
      consolidate();
    }
  }

  void update(tori** old_slot, tori** new_slot, tidy* new_obj) {
    dhm.erase(old_slot);
    dhm[new_slot] = std::make_pair(new_obj, get_current_line_stamp(new_obj));
  }

  void consolidate() {
    for (auto p : buffer) {
      dhm[p.first] = p.second;
    }
    buffer.clear();
  }

  ssize_t size() { consolidate(); return dhm.size(); }

  std::vector<std::pair<tori**, std::pair<tidy*, line_stamp_t> > >
            copy_to_vector() {
    consolidate();
    std::vector<std::pair<tori**, std::pair<tidy*, line_stamp_t> > > slots;
    for (auto p : dhm) { slots.push_back(p); }
    return slots;
  }

  void clear() { dhm.clear(); buffer.clear(); }
private:
  std::vector<std::pair<tori**,  std::pair<tidy*, line_stamp_t> > > buffer;
  google::dense_hash_map<tori**, std::pair<tidy*, line_stamp_t> > dhm;
};

uint32_t refPattern(const typemap* map) {
  uint32_t rv = 0;
  for (int i = 0; i < map->numOffsets; ++i) {
    int refoff = map->offsets[i] / 8;
    if (refoff < 28) {
      rv |=  (1 << refoff);
    } else {
      rv =  (1 << 30);
      break;
    }
  }
  return rv;
}

/*
class heap {
public:
  virtual ~heap() {}

  bool is_linked_to_default_subheap;

  virtual uint32_t hash_for_object_headers();

  virtual tidy* tidy_for(tori* t) = 0;

  virtual void dump_stats(FILE* json) = 0;

  virtual void force_gc_for_debugging_purposes() = 0;

  virtual uint64_t prepare_for_collection(bool) = 0;

  virtual void condemn() = 0;
  virtual void uncondemn() = 0;
  virtual bool is_condemned() = 0;

  virtual int64_t immix_sweep(clocktimer<false>& phase, int64_t* num_lines_tracked, int64_t* num_groups_tracked) = 0;

  virtual void trim_remset() = 0;
  virtual remset_with_obj_t& get_incoming_ptr_addrs() = 0;

  virtual bool is_empty() = 0;
  virtual uint64_t approx_size_in_bytes() = 0;

  virtual void remember_into(void** slot, void* obj) = 0;

  virtual void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) = 0;
  virtual void* allocate_cell(typemap* typeinfo) = 0;

  virtual void* allocate_cell_16(typemap* typeinfo) = 0;
  virtual void* allocate_cell_32(typemap* typeinfo) = 0;
  virtual void* allocate_cell_48(typemap* typeinfo) = 0;
};

#define immix_space heap
*/

struct immix_space;

/* We can collect the heap at three granularities:
 *   1) Collect the whole heap, ignoring subheap boundaries.
 *      This is used to find space triggered by heap exhaustion.
 *   2) Collect a single subheap.
 *   3) Collect whatever subheaps have been condemned.
 */
enum class condemned_set_status : uint8_t {
  default_and_linked = 0,
  whole_heap_condemned,
  per_frame_condemned
};

struct immix_worklist_t {
    void       initialize()      { roots.clear(); }
    template <condemned_set_status condemned_status>
    void       process();
    void       process_for_compaction();
    bool       empty()           { return roots.empty(); }
    unchecked_ptr* pop_root()  { auto root = roots.back(); roots.pop_back(); return root; }
    void       add_root(unchecked_ptr* root) { PREFETCH_FOR_MARKING(*(void**)root); roots.push_back(root); }
    size_t     size()            { return roots.size(); }
  private:
    size_t                  idx;
    std::vector<unchecked_ptr*> roots;
    ptr_fifo_2             fifo;
};

// {{{ Global data used by the GC

enum class frame15kind : uint8_t {
  unknown = 0,
  immix_smallmedium, // associated is immix_space*
  immix_malloc_start, // associated is immix_malloc_frame15info*
  immix_malloc_continue, // associated is heap_array* base.
};

struct frame15info {
  void*            associated;
  frame15kind      frame_classification;
  uint8_t          num_available_lines_at_last_collection; // TODO these two fields are mutually exclusively used...
  uint8_t          num_holes_at_last_full_collection;
  uint8_t          compactable;
  uint8_t          shared_lines;
};

// We track "available" rather than "marked" lines because it's more natural
// to track incrementally for line frames, where different spaces own different groups,
// and not all lines were necessarily part of the last condemned set. If a given line
// wasn't condemned, it's arguable whether its state is "unmarked" in the same sense
// that a condemned line might be, but it's straightforward to state that it's not available.

void gc_assert(bool cond, const char* msg);

// {{{
#define arraysize(x) (sizeof(x)/sizeof((x)[0]))
#define MAX_ARR_OBJ_PER_FRAME15 4
struct immix_malloc_frame15info {
  // Since allocs are min 8K, this will be guaranteed to have size at most 4.
  heap_array*      contained[MAX_ARR_OBJ_PER_FRAME15];
  immix_space*      parents[MAX_ARR_OBJ_PER_FRAME15];
  uint8_t          condemned[MAX_ARR_OBJ_PER_FRAME15];

  void remove(heap_array* arr) {
    for (int i = 0; i < arraysize(condemned); ++i) {
      if (contained[i] == arr) {
        contained[i] = nullptr;
        parents[i] = nullptr;
        condemned[i] = 0;
        break;
      }
    }
  }

  void add(heap_array* arr, immix_space* parent) {
    for (int i = 0; i < arraysize(condemned); ++i) {
      if (contained[i] == nullptr) {
        contained[i] = arr;
        parents[i] = parent;
        condemned[i] = 0;
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

template <typename Allocator>
struct condemned_set {
  condemned_set_status status;

  std::set<Allocator*> spaces;

  // Valid only during sweeping/compaction.
  // For non-emergency collections, this is the set of default-linked subheaps.
  // For emergency collections, this is both default-linked and non-default-linked subheaps.
  std::vector< heap_handle<Allocator>* > non_default_handles;

  // Some objects (in particular, subheap handles) are not allocated on regular frames
  // and thus would otherwise not get their granule mark bits reset at the end of each collection.
  // We track, above, the set of all created subheaps (in order to identify unmarked subheaps),
  // but to avoid O(full-heap) work on a subheap collection,
  // we only want to reset the marks we established during each collection.
  std::set<heap_cell*> unframed_and_marked;

  // Use line marks to reclaim space, then reset linemaps and object marks.
  int64_t sweep_condemned(clocktimer<false>& phase,
                          bool emergency, bool hadEmptyRootSet,
                          int64_t* num_lines_tracked, int64_t* num_groups_tracked);

  int64_t lines_live;

  void prepare_for_collection(bool voluntary, bool sticky, bool emergency,
                              uint64_t*, uint64_t*);
};

template<typename Allocator>
struct GCGlobals {
  Allocator* allocator = NULL;
  Allocator* default_allocator = NULL;

  // Invariant: null pointer when allocator == default_allocator,
  // otherwise a heap_handle to the current allocator.
  heap_handle<immix_space>* allocator_handle;

  uint32_t current_subheap_hash;

  condemned_set<Allocator> condemned_set;

  ClusterMap clusterForAddress;
  memory_range typemap_memory;

  bool had_problems;
  bool logall;

  std::map<std::pair<const char*, typemap*>, int64_t> alloc_site_counters;

  std::set<frame21*> all_frame21s;
  std::vector<heap_handle<Allocator>*> default_linked_subheaps;
  std::vector<heap_handle<Allocator>*> non_default_linked_subheaps;

  double gc_time_us;

  clocktimer<true> init_start;

  int num_gcs_triggered;
  int num_gcs_triggered_involuntarily;
  int num_gcs_triggered_nurseryonly;
  int num_big_stackwalks;
  double subheap_ticks;
  double involuntary_ticks;

  uint64_t num_allocations;
  uint64_t num_alloc_bytes;
  uint64_t num_subheaps_created;
  uint64_t num_subheap_activations;

  uint64_t num_closure_calls;

  uint64_t num_alloc_bytes_in_subheaps;

  uint64_t write_barrier_phase0_hits;
  uint64_t write_barrier_phase0b_hits;
  uint64_t write_barrier_phase1_hits;
  uint64_t write_barrier_phase1g_hits;

  uint64_t num_objects_marked_total;
  uint64_t alloc_bytes_marked_total;

  uint64_t max_bytes_live_at_whole_heap_gc;

  void**            lazy_mapped_markable_handles;

  frame15info*      lazy_mapped_frame15info;
  uint8_t*          lazy_mapped_coarse_marks;

  uint8_t*          lazy_mapped_granule_marks;
  uint16_t*         lazy_mapped_frame_liveness;
  uint64_t*         lazy_mapped_sliver_offsets;

  line_stamp_t*     lazy_mapped_line_stamps;
  uint8_t*          lazy_mapped_line_marks;
  // With sticky mark bits, subheaps, and lazy sweeping,
  // line marks are too overloaded. With lazy sweeping,
  // we must not re-use allocated lines that don't get
  // condemned before the next sweep; this suggests marking
  // at allocation time. But with sticky mark bits, sticky
  // collections do not reset line marks at the start of
  // collection. Thus a sticky collection could not reclaim
  // any "young" data... nor old data! Whoops.
  // So we do something slightly different:
  //   line_used   is reset at allocation (to "used" == 1);
  //   line_marks are reset at collection (to "unused" == 0)
  //     (or left as-is for sticky collections) and then
  //     copied to overwrite the condemned subset of line_used.
  // Thus line_used will be "unused" only for unmarked && condemned lines.
  uint8_t*          lazy_mapped_line_used;

  struct hdr_histogram* hist_gc_stackscan_frames;
  struct hdr_histogram* hist_gc_stackscan_roots;
  struct hdr_histogram* hist_gc_pause_micros;
  struct hdr_histogram* hist_gc_pause_ticks;
  struct hdr_histogram* hist_gc_rootscan_ticks;
  struct hdr_histogram* hist_gc_alloc_array;
  struct hdr_histogram* hist_gc_alloc_large;
  uint64_t enum_gc_alloc_small[129];

  int64_t evac_candidates_found;

  bool   next_collection_sticky;
  double yield_percentage_threshold;

  double last_full_gc_compaction_headroom_estimate;

  double last_full_gc_fragmentation_percentage;
  int evac_threshold;
  int64_t marked_histogram[128];
  int64_t marked_histogram_frames[128];
  int64_t residency_histogram[128];
};

GCGlobals<immix_space> gcglobals;

bool g_in_non_default_subheap = false;
int64_t g_bytes_marked = 0;

uint32_t fold_64_to_32(uint64_t x) {
  return uint32_t(x) ^ uint32_t(x >> uint64_t(32));
}

line_stamp_t get_current_line_stamp(void* slot) {
  return gcglobals.lazy_mapped_line_stamps[line_offset_within_heap(slot)];
}
void set_current_line_stamp(void* slot, line_stamp_t v) {
  gcglobals.lazy_mapped_line_stamps[line_offset_within_heap(slot)] = v;
}

void reset_marked_histogram() {
  if (GCLOG_PRINT_LINE_HISTO) {
    int64_t sum_x = 0;
    int64_t sum_f = 0;
    int64_t sum_u = 0;
    int64_t sum_v = 0;
    for (int i = 0; i < 128; ++i) {
      auto x = gcglobals.marked_histogram[i];
      auto f = gcglobals.marked_histogram_frames[i];
      auto u = (f * IMMIX_LINES_PER_BLOCK) - x;
      sum_x += x;
      sum_f += f;
      sum_u += u;
      sum_v += gcglobals.residency_histogram[i];
    }

    fprintf(gclog, "Mark histogram from prior collection:\n");
    fprintf(gclog, "   holes   marked      pct                               [cumulative]\n");
    int64_t cumx = 0;
    int64_t cumf = 0;
    int64_t cumu = 0;
    int64_t cumv = 0;
    int64_t all = sum_f * IMMIX_LINES_PER_BLOCK;
    for (int i = 127; i >= 0; --i) {
      auto x = gcglobals.marked_histogram[i];
      auto f = gcglobals.marked_histogram_frames[i];
      auto u = (f * IMMIX_LINES_PER_BLOCK) - x;
      auto v = gcglobals.residency_histogram[i];
      cumx += x;
      cumf += f;
      cumu += u;
      cumv += v;
      if (x > 0) {
        fprintf(gclog, "   %4d: %7zd   (%4.1f%%)     {%9.1f lines live}    [%9.1f lines live; %7zd lines used (%.2f%%);",
          i, x, double(x * 100)/double(sum_x), double(v)/double(IMMIX_BYTES_PER_LINE), // {lines live}
                                               double(cumv)/double(IMMIX_BYTES_PER_LINE),
                                               cumx, // lines used
                                              (100.0 * double(cumv)/double(IMMIX_BYTES_PER_LINE)) / double(cumx));
        fprintf(gclog, "%4.1f%% of used, %4.1f%% of all] [%4zd frames; %4.1f%%] [%6zd lines free; %4.1f%% of free; %4.1f%% of all] (%.3f u/m ratio (%.3f runway factor?))\n",
                                               double(cumx * 100)/double(sum_x), double(cumx * 100) / double(all), // of used; of all
                                               cumf, double(cumf * 100)/double(sum_f),
                                               cumu, double(cumu * 100)/double(sum_u), double(cumu * 100) / double(all),
                                               //(double(cumf)/double(sum_f)) / (double(cumx) / double(all))
                                               double(cumu)/double(cumx),
                                                 (1.0 - (double(cumu) / double(sum_u))) * (double(cumu)/double(cumx))
                                              ); }
    }
  }
  for (int i = 0; i < 128; ++i) { gcglobals.marked_histogram[i] = 0; }
  for (int i = 0; i < 128; ++i) { gcglobals.marked_histogram_frames[i] = 0; }
  for (int i = 0; i < 128; ++i) { gcglobals.residency_histogram[i] = 0; }
}

int num_avail_defrag_lines();
int num_assigned_defrag_lines();

int select_defrag_threshold(double defrag_pad_factor) {
  int64_t reserved = num_avail_defrag_lines();
  int64_t avail = int64_t(double(reserved) * defrag_pad_factor);
  int64_t required = 0;

  int thresh = 128;
  while (thresh-- > 0) {
    required += gcglobals.marked_histogram[thresh];
    if (required > avail) {
      if (GCLOG_DETAIL > 0) {
        fprintf(gclog, "defrag threshold: %d; backing off from %zd to %zd lines assumed needed vs %zd lines assumed avail (%d/%d lines)\n",
          thresh + 1,
          required, required - gcglobals.marked_histogram[thresh], avail,
          num_avail_defrag_lines(), num_assigned_defrag_lines());
      }
      
      return thresh + 1;
    }
  }
  return 0;
}

// The worklist would be per-GC-thread in a multithreaded implementation.
immix_worklist_t immix_worklist;

class condemned_set_status_manager {
  condemned_set_status prev;

public:
  condemned_set_status_manager(condemned_set_status new_status) {
    prev = gcglobals.condemned_set.status;
    gcglobals.condemned_set.status = new_status;
  }

  ~condemned_set_status_manager() {
    gcglobals.condemned_set.status = prev;
  }
};


template <typename T>
inline T num_granules(T size_in_bytes) { return size_in_bytes / T(16); }

uintptr_t global_granule_for(void* p) { return num_granules(uintptr_t(p)); }

// Precondition: x >= 15
uint32_t frameX_id_of(void* p, uintptr_t x) { return uint32_t(uintptr_t(p) >> x); }

frame21* frame21_of_id(frame21_id x) { return (frame21*) (uintptr_t(x) << 21); }

void clear_linemap(uint8_t* linemap) {
  memset(linemap, 0, IMMIX_LINES_PER_BLOCK);
}

void clear_frame15(frame15* f15) { memset(f15, 0xDD, 1 << 15); fprintf(gclog, "cleared frame15 %p (%u)\n", f15, frame15_id_of(f15)); }
void clear_frame21(frame21* f21) { memset(f21, 0xDD, 1 << 21); }
void do_clear_line_frame15(immix_line_frame15* f);

inline
frame15info* frame15_info_for_frame15_id(frame15_id fid) {
  return &gcglobals.lazy_mapped_frame15info[fid];
}

inline
frame15kind classification_for_frame15info(frame15info* finfo) {
  return finfo->frame_classification;
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

inline bool obj_is_marked(heap_cell* obj) {
  // Young objects aren't marked, but generally we only take shortcuts for
  // marked objects, not unmarked ones, so checking the young bit is pointless.
  uint8_t* markbyte = &gcglobals.lazy_mapped_granule_marks[global_granule_for(obj)];
  return *markbyte != 0;
}
inline bool arr_is_marked(heap_array* obj) { return obj_is_marked((heap_cell*)obj); }

// Roughly 3% degredation to incorporate size bits..
inline void do_mark_obj_of_size(heap_cell* obj, int64_t cell_size) {
  obj->mark_not_young();
  if (GCLOG_DETAIL > 3) { fprintf(gclog, "setting granule bit  for object %p in frame %u\n", obj, frame15_id_of(obj)); }
  uintptr_t g0 = global_granule_for(obj);
  int64_t size_in_granules = cell_size / 16;
  //fprintf(gclog, "setting granule bits (%zd) for size-%zd object %p in frame %u with header %zx\n", size_in_granules, cell_size, obj, frame15_id_of(obj), obj->raw_header());
  if (size_in_granules < 128) {
      gcglobals.lazy_mapped_granule_marks[g0] = uint8_t(size_in_granules) + 128;
  } else {
    auto g = g0;
    uint8_t flag = 0;
    while (size_in_granules >= 127) {
      gcglobals.lazy_mapped_granule_marks[g] = 127;
      ++g;
      size_in_granules -= 127;
    }
      gcglobals.lazy_mapped_granule_marks[g] = size_in_granules;
      // high bit set for initial byte
      gcglobals.lazy_mapped_granule_marks[g0] += 128;
  }
}

#if 0
inline void do_mark_obj(heap_cell* obj) {
  obj->mark_not_young();
  if (GCLOG_DETAIL > 3) { fprintf(gclog, "setting granule bit  for object %p in frame %u\n", obj, frame15_id_of(obj)); }
  gcglobals.lazy_mapped_granule_marks[global_granule_for(obj)] = 1;
}
#endif

inline void do_unmark_granule(void* obj) {
  gcglobals.lazy_mapped_granule_marks[global_granule_for(obj)] = 0;
}

void clear_object_mark_bits_for_group(free_linegroup* g) {
  auto num_freed_lines = linegroup_size_in_lines(g);
  //fprintf(gclog, "Clearing object mark bits for free group %p (size %d)\n", g, num_freed_lines); fflush(gclog);
  memset(&gcglobals.lazy_mapped_granule_marks[global_granule_for(g)], 0, num_freed_lines * IMMIX_GRANULES_PER_LINE);
}

void clear_object_mark_bits_for_used_group(used_linegroup& g) {
  //fprintf(gclog, "Clearing object mark bits for used group @ %p (size %d)\n", g.base, g.count); fflush(gclog);
  memset(&gcglobals.lazy_mapped_granule_marks[global_granule_for(g.base)], 0, g.count * IMMIX_GRANULES_PER_LINE);
}

#if 1
void clear_object_mark_bits_for_frame15(void* f15) {
  if (GCLOG_DETAIL > 2) { fprintf(gclog, "clearing granule bits for frame %p (%u)\n", f15, frame15_id_of(f15)); }
  memset(&gcglobals.lazy_mapped_granule_marks[global_granule_for(f15)], 0, IMMIX_GRANULES_PER_BLOCK);

  gcglobals.lazy_mapped_frame_liveness[frame15_id_of(f15)] = 0;
}
#endif

bool line_is_marked(  int line, uint8_t* linemap) { return linemap[line] != 0; }
bool line_is_unmarked(int line, uint8_t* linemap) { return linemap[line] == 0; }
void do_mark_line(  int line, uint8_t* linemap) { linemap[line] = 1; }
void do_unmark_line(int line, uint8_t* linemap) { linemap[line] = 0; }

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
                       immix_space* parent) {
    void* base = malloc(total_bytes + 8);
    heap_array* allot = align_as_array(base);

    if (GC_ASSERTIONS) { gc_assert(frame15_id_of(allot) == frame15_id_of(allot->body_addr()), "large array: metadata and body address on different frames!"); }
    if (DEBUG_INITIALIZE_ALLOCATIONS ||
      (init && !ELIDE_INITIALIZE_ALLOCATIONS)) { memset((void*) base, 0x00, total_bytes + 8); }
    allot->set_header(arr_elt_map, gcglobals.current_subheap_hash);
    allot->set_num_elts(num_elts);
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_array(total_bytes); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += total_bytes; }
    if (TRACK_NUM_ALLOC_BYTES && g_in_non_default_subheap) {
      gcglobals.num_alloc_bytes_in_subheaps += total_bytes; }

    // TODO modify associated frame15infos, lazily allocate card bytes.
    toggle_framekinds_for(allot, offset(base, total_bytes + 7), parent);
    // TODO review when/where line mark bit setting happens,
    //      ensure it doesn't happen for pointers to arrays.
    allocated.push_front(base);

    if (true || GCLOG_DETAIL > 0) {
      fprintf(gclog, "mallocating large array (%p, body %p) total bytes %zd, alloc #%zd\n",
          allot, allot->body_addr(), total_bytes, gcglobals.num_allocations);
    }

    return allot->body_addr();
  }

  void toggle_framekinds_for(heap_array* allot, void* last, immix_space* parent) {
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

  void set_framekind_malloc(frame15_id b, heap_array* allot, immix_space* parent) {
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

  void reset_large_array_marks() {
    auto it = allocated.begin();
    while (it != allocated.end()) {
      void* base = *it;
      do_unmark_granule(base);
      ++it;
    }
  }

  // Iterates over each allocated array; free() on the unmarked ones.
  void sweep_arrays() {
    auto it = allocated.begin();
    while (it != allocated.end()) {
      void* base = *it;
      heap_array* arr = align_as_array(base);
      if (!arr_is_marked(arr)) { // unmarked, can free associated array.
        if (GCLOG_DETAIL > 1) { fprintf(gclog, "freeing unmarked array %p\n", arr); }
        it = allocated.erase(it); // erase() returns incremented iterator.
        framekind_malloc_cleanup(arr);
        free(base);
      } else {
        ++it;
      }
    }
  }

  int64_t approx_size_in_bytes();

  bool empty() { return allocated.empty(); }
};
// }}}

// {{{ Internal utility functions
extern "C" foster_bare_coro** __foster_get_current_coro_slot();

intr* from_tidy(tidy* t) { return (intr*) t; }

void mark_as_smallmedium(frame15* f) {
  auto finfo = frame15_info_for_frame15_id(frame15_id_of(f));
  finfo->num_available_lines_at_last_collection = 0;
  finfo->frame_classification = frame15kind::immix_smallmedium;
}

// Markable objects live in the upper bits of address space;
// the low 4 GB is for constants, (immutable) globals, etc.
bool non_markable_addr(void* addr) {
  return uintptr_t(addr) < uintptr_t(0x100000000ULL);
}

bool non_kosher_addr(void* addr) {
  // The signed test catches negative values, which we assume are the
  // result of looking at data that was supposed to be a pointer but isn't.
  return intptr_t(addr) < 0x1000000;
}

bool is_in_default_subheap(tidy* val) {
  uint32_t space_id = space_id_of_header(heap_cell::for_tidy(val)->raw_header());
  return space_id == 0;
}

immix_space* heap_for_header(uint64_t header) {
  uint32_t space_id = space_id_of_header(header);
  if (space_id == 0) return gcglobals.default_allocator;
  return (immix_space*) uintptr_t(space_id);
}

immix_space* heap_for_tidy(tidy* val) {
  return heap_for_header(heap_cell::for_tidy(val)->raw_header());
}

bool tidy_owned_by(tidy* t, immix_space* space) {
  if (non_markable_addr(t)) {
    return false;
  }

  return heap_for_tidy(t) == space;
}

tidy* assume_tori_is_tidy(tori* p) { return (tidy*) p; }

bool space_is_condemned(immix_space* space);
remset_with_obj_t& space_incoming_ptr_addrs(immix_space* space);

bool per_frame_cell_is_condemned(heap_cell* obj) {
  //fprintf(gclog, "cell_is_condemned? obj: %p ", obj); fflush(gclog);
  //fprintf(gclog, "with header %zx", obj->raw_header());  fflush(gclog);
  auto rv = space_is_condemned(heap_for_header(obj->raw_header()));
  //fprintf(gclog, " ----> %d\n", rv); fflush(gclog);
  return rv;
}

bool is_condemned_for_default_and_linked(immix_space* space);

bool obj_is_condemned_d(tidy* obj, condemned_set_status condemned_portion) {
  if (condemned_portion == condemned_set_status::whole_heap_condemned) {
    return true;
  }

  immix_space* space = heap_for_tidy(obj);

  if (condemned_portion == condemned_set_status::default_and_linked) {
    //fprintf(gclog, "obj_is_condemned: active space is %p; obj space is %p; eqq %d\n",
    //    space, heap_for_tidy(obj), space == heap_for_tidy(obj));
    return is_condemned_for_default_and_linked((immix_space*) space);
  } else {
    return space_is_condemned(space);
  }
}

template<condemned_set_status condemned_portion>
bool obj_is_condemned(tidy* obj) {
  if (condemned_portion == condemned_set_status::whole_heap_condemned) {
    return true;
  }
  
  immix_space* space = heap_for_tidy(obj);
  if (condemned_portion == condemned_set_status::default_and_linked) {
    //fprintf(gclog, "obj_is_condemned: active space is %p; obj space is %p; eqq %d\n",
    //    space, heap_for_tidy(obj), space == heap_for_tidy(obj));

    return is_condemned_for_default_and_linked((immix_space*) space);
  } else {
    return space_is_condemned(space);
  }
}

// }}}

// {{{
// {{{ Function prototype decls
bool line_for_slot_is_marked(void* slot);
void inspect_typemap(const typemap* ti);
void collect_roots_from_stack(void* start_frame);
void collect_roots_from_stack_of_coro(foster_bare_coro* coro);
const typemap* tryGetTypemap(heap_cell* cell);
// }}}

uint8_t* linemap_for_frame15_id(frame15_id fid) {
  return &gcglobals.lazy_mapped_line_marks[size_t(fid) * IMMIX_LINES_PER_FRAME15];
}

uint8_t* line_used_for_frame15_id(frame15_id fid) {
  return &gcglobals.lazy_mapped_line_used[size_t(fid) * IMMIX_LINES_PER_FRAME15];
}

namespace helpers {

  void print_heap_starvation_info(FILE* f) {
    //fprintf(f, "working set exceeded heap size of %lld bytes! aborting...\n", curr->get_size()); fflush(f);
    fprintf(f, "    try running with a larger heap size using a flag like\n");
    fprintf(f, "      --foster-heap-MB 64\n");
  }

  void oops_we_died_from_heap_starvation(const char* message) {
    print_heap_starvation_info(gclog);
    print_heap_starvation_info(stderr);
    fprintf(gclog, "Triggered starvation via %s\n", message); fflush(gclog);
    exit(255); // TODO be more careful if we're allocating from a coro...
  }

  tidy* allocate_array_prechecked(bump_allocator* bumper,
                                  const typemap* arr_elt_map,
                                  int64_t  num_elts,
                                  int64_t  total_bytes,
                                  uint32_t space_id,
                                  bool     init) {
    //auto bumper_size_at_start = bumper->size();
    heap_array* allot = static_cast<heap_array*>(bumper->prechecked_alloc_noinit(total_bytes));

    if (GC_ASSERTIONS) { gc_assert(frame15_id_of(allot) == frame15_id_of(allot->body_addr()), "pre array: metadata and body address on different frames!"); }
    if (DEBUG_INITIALIZE_ALLOCATIONS ||
      (init && !ELIDE_INITIALIZE_ALLOCATIONS)) { memset((void*) allot, 0x00, total_bytes); }
    if (DEBUG_PRINT_ALLOCATIONS) {
      fprintf(gclog, "alloc'a %d @ %p; num elts = %d; size at start was %zd\n", int(total_bytes), allot, int(num_elts), bumper->size() + total_bytes);
    }
    allot->set_header(arr_elt_map, space_id);
    allot->set_num_elts(num_elts);
    //if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(total_bytes); }
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_array(total_bytes); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += total_bytes; }
    if (TRACK_NUM_ALLOC_BYTES && g_in_non_default_subheap) {
      gcglobals.num_alloc_bytes_in_subheaps += total_bytes; }

    if (FOSTER_GC_TRACK_BITMAPS) {
      //size_t granule = granule_for(tori_of_tidy(allot->body_addr()));
      //obj_start.set_bit(granule);
      //obj_limit.set_bit(granule + num_granules(total_bytes));
    }


    if (GC_ASSERTIONS && line_for_slot_is_marked(allot)) {
      fprintf(gclog, "INVARIANT VIOLATED: allocating array on a pre-marked line?!?\n");
      exit(4);
    }

    if (GCLOG_DETAIL > 3) {
      fprintf(gclog, "allocating array (%p, body %p) in line %d of frame %u, total bytes %zd, alloc #%zd\n",
          allot, allot->body_addr(), line_offset_within_f15(allot), frame15_id_of(allot), total_bytes, gcglobals.num_allocations);
    }

    return allot->body_addr();
  }

  void allocate_cell_prechecked_histogram(int N) {
    if (N > 128) {
      hdr_record_value(gcglobals.hist_gc_alloc_large, int64_t(N));
    } else {
      gcglobals.enum_gc_alloc_small[N]++;
    }
  }

  tidy* allocate_cell_prechecked(bump_allocator* bumper,
                                 const typemap* map,
                                 int64_t  cell_size,
                                 uint32_t space_id) {
    heap_cell* allot = static_cast<heap_cell*>(bumper->prechecked_alloc(cell_size));

    // TODO reduce duplication...

    // TODO we could pretty cheaply compute whether this object straddles lines or not via
    //        bool did_line_increment(u64 a, u64 b) { return (a >> 8) != (b >> 8); } (2 shifts, 1 cmp, 1 setne)
    //        or
    //        bool did_line_increment_alt(u64 a, u64 b) { return ((a ^ b) >> 8) != 0; } (1 xor, 1 shift, 1 setne)
    //      and embed the result in a header bit; this allows us to avoid looking up object
    //      size when marking, I guess?
    //          How much overhead on a benchmark that allocates and doesn't collect, like binarytrees?
    //          How much overhead on a benchmark that mostly collects, like minicache?
    //          How much overhead on a benchmark that's mixed, like sac-qsort?

    if (GC_ASSERTIONS) { gc_assert(frame15_id_of(allot) == frame15_id_of(allot->body_addr()), "cell prechecked: metadata and body address on different frames!"); }
    //if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(map->cell_size); }
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_cell(cell_size); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += cell_size; }
    if (TRACK_NUM_ALLOC_BYTES && g_in_non_default_subheap) {
      gcglobals.num_alloc_bytes_in_subheaps += cell_size; }
    if (FOSTER_GC_ALLOC_HISTOGRAMS) { allocate_cell_prechecked_histogram((int) cell_size); }
    allot->set_header(map, space_id);

    if (FOSTER_GC_TRACK_BITMAPS) {
      //size_t granule = granule_for(tori_of_tidy(allot->body_addr()));
      //obj_start.set_bit(granule);
    }

    if (GC_ASSERTIONS && line_for_slot_is_marked(allot)) {
      fprintf(gclog, "INVARIANT VIOLATED: allocating cell (%p) on a pre-marked line?!?\n", allot);
      exit(4);
    }
    if (GC_ASSERTIONS && obj_is_marked(allot)) {
      fprintf(gclog, "INVARIANT VIOLATED: allocating cell (%p)      pre-marked     ?!?\n", allot);
      exit(4);
    }

    if (DEBUG_PRINT_ALLOCATIONS) {
      fprintf(gclog, "Allocated prechecked cell of size %zd bytes at %p (line %d of %u) for space %x\n", cell_size, allot->body_addr(),
          line_offset_within_f15(allot->body_addr()), frame15_id_of(allot->body_addr()), space_id);
    }

    return allot->body_addr();
  }

#if 1
  bool remset_entry_is_externally_stale(tori** slot) {
    return !line_for_slot_is_marked(slot);
  }

  bool remset_entry_is_internally_stale(tori** slot) {
    tori* ptr = *slot;
    if (non_kosher_addr(ptr)) { return true; }
    frame15kind fk = classification_for_frame15_id(frame15_id_of(ptr));
    if (fk == frame15kind::unknown) { return true; }

    heap_cell* cell = heap_cell::for_tidy((tidy*) ptr);
    /*
    fprintf(gclog, "considering remset      ptr %p: body line marked %d, cell line marked %d, cell granule marked %d\n",
      ptr, line_for_slot_is_marked(ptr ),
           line_for_slot_is_marked(cell), obj_is_marked(cell)); fflush(gclog);
           */
    if (!obj_is_marked(cell)) { return true; }
    // TODO check to make sure that the space ownership hasn't changed?
    return false;
  }

  // Precondition: line marks have been established and not yet cleared.
  bool remset_entry_is_externally_or_internally_stale(tori** slot) {
    if (remset_entry_is_externally_stale(slot)) { return true; }
    return remset_entry_is_internally_stale(slot);
  }
#endif

  void do_trim_remset(remset_with_obj_t& incoming_ptr_addrs, immix_space* space) {
    auto slots = incoming_ptr_addrs.copy_to_vector();
    incoming_ptr_addrs.clear();

    if (GCLOG_DETAIL > 1) {
      fprintf(gclog, "gc %d: pre-trim remset contains %zu slots in space %p\n", 
            gcglobals.num_gcs_triggered, slots.size(), space);
    }
    int newsize = 0;
    for (auto p : slots) {
      auto slot = p.first;
      auto cell = heap_cell::for_tidy(p.second.first);
      if (0) {
        fprintf(gclog, "gc %d: maybe trim remset entry in space %p: slot %p in cell %p; src heap %p; cellstamp %d vs %d; slotstamp %d; srccell marked? %d; tgt marked? %d\n",
            gcglobals.num_gcs_triggered, space, slot, cell, heap_for_tidy(cell->body_addr()),
            int(p.second.second),
            int(get_current_line_stamp(cell)),
            int(get_current_line_stamp(slot)),
            obj_is_marked(cell),
            obj_is_marked(heap_cell::for_tidy((tidy*) *slot))
            ); fflush(gclog);
      }

      bool definitely_stale = get_current_line_stamp(cell) != p.second.second;

      //if (remset_entry_is_externally_or_internally_stale(p.first)) {
      // The source for this entry may or may not be condemned.
      // If we find a remset entry coming from an unmarked object in a condemned slot,
      // we can drop the entry: it's stale.
      if (definitely_stale
        //|| (!obj_is_marked(cell) && heap_for_tidy(cell->body_addr())->is_condemned())) {
          || (!obj_is_marked(cell) && obj_is_condemned_d(cell->body_addr(), gcglobals.condemned_set.status))) {
        //|| heap_for_header(cell->raw_header()) != space
        //|| classification_for_frame15_id(frame15_id_of(*slot)) != frame15kind::immix_smallmedium) {
        // do nothing
        
        if (0) {
        fprintf(gclog, "gc %d: dropping stale remset entry holding %p in space %p for slot %p in cell %p; mark=%d, tgtmark=%d, hdr=%zx; def-stale? %d\n",
            gcglobals.num_gcs_triggered, *slot, space, slot, cell,
            int(obj_is_marked(cell)),
            obj_is_marked(heap_cell::for_tidy((tidy*) *slot)),
            cell->raw_header(),
            definitely_stale
            );
        }
      } else {
        /*
        fprintf(gclog, "gc %d: re-adding remset entry holding %p in space %p for slot %p in cell %p\n",
            gcglobals.num_gcs_triggered, slot, space, slot, cell);
            */
        incoming_ptr_addrs.insert(slot, cell->body_addr());
        ++newsize;
      }
    }
    if (GCLOG_DETAIL > 1) {
      fprintf(gclog, "gc %d: post-trim remset contains %d slots\n", gcglobals.num_gcs_triggered, newsize);
    }
  }

  void visit_root(unchecked_ptr* root, const char* slotname) {
    gc_assert(root != NULL, "someone passed a NULL root addr!");
    if (/*gcglobals.num_gcs_triggered < 3 ||*/ GCLOG_DETAIL > 1) {
      fprintf(gclog, "\t\tgc %d: STACK SLOT slot %s (%p) holds %p\n",
                        gcglobals.num_gcs_triggered,
                        (slotname ? slotname : "<unknown slot>"),
                        root,
                        unchecked_ptr_val(*root)
                        );
      /*
      fprintf(gclog, "\t\tSTACK SLOT %p (in (%u)) contains ptr %p, slot name = %s\n", root, frame15_id_of(root),
                        unchecked_ptr_val(*root),
                        (slotname ? slotname : "<unknown slot>"));
                        */
    }

    if (!non_markable_addr(unchecked_ptr_val(*root))) {
      immix_worklist.add_root(root);
    }
  }

  void clear_line_and_object_mark_bits_for_used_group(used_linegroup g) {
    auto fid = frame15_id_of(g.base);
    //uint8_t* linemap = line_used_for_frame15_id(fid);
    uint8_t* linemap = linemap_for_frame15_id(fid);

    //fprintf(gclog, "clearing linemap of size %zd\n", g.size_in_lines());
    memset(&linemap[g.startline()], 0, g.size_in_lines());
    clear_object_mark_bits_for_used_group(g);
  }

} // namespace helpers
// }}}

// Bitmap overhead for 16-byte granules is 8 KB per MB (a bit under 1%).
// Bytemap overhead for 16-byte granules is 64 KB per MB (6.25%).

////////////////////////////////////////////////////////////////////

// TODO use stat_tracker again?

frame21* allocate_frame21() {
  bool commit = true;
  frame21* rv = (frame21*) pages_map(nullptr, 1 << 21, 1 << 21, &commit);
  if (ENABLE_GCLOG_PREP) { fprintf(gclog, "allocate_frame21() returning %p\n", rv); }
  gc_assert(commit && rv != NULL, "unable to allocate a 2MB chunk from the OS");
  gcglobals.all_frame21s.insert(rv);
  return rv;
}

// Returning un-needed memory to the OS is good, but churning virtual memory is not.
void deallocate_frame21(frame21* f) {
  gcglobals.all_frame21s.erase(f);
  pages_unmap(f, 1 << 21);
}

// We prefer to use empty frames for the defrag reserve, but in tight heaps we're often
// stuck with linegroups. Because we only defrag within the default subheap, it's okay
// to use lines as long as they only come from the default subheap.
struct defrag_reserve_t {
  int32_t reserved_lines_target;
  int32_t reserved_lines_current;

  //std::vector<frame15*> defrag_frame15s; // TODOX
  std::vector<free_linegroup*> defrag_lines; // TODOX

  defrag_reserve_t() : reserved_lines_target(0), reserved_lines_current(0) {}

  bool full() { return reserved_lines_current >= reserved_lines_target; }

  void freeze_target_line_count() { reserved_lines_target = reserved_lines_current; }

  void give_lines(free_linegroup* g) {
    auto size = linegroup_size_in_lines(g);
    //fprintf(gclog, "defrag reserve getting linegroup %p +> %d (%u)\n", g, size, frame15_id_of(g));
    reserved_lines_current += size;
    defrag_lines.push_back(g);
    frame15_info_for_frame15_id(frame15_id_of(g))->shared_lines += size;
  }

  free_linegroup* try_get_lines_for_defrag() {
    if (defrag_lines.empty()) return nullptr;
    free_linegroup* g = defrag_lines.back();
    defrag_lines.pop_back();
    auto size = linegroup_size_in_lines(g);
    reserved_lines_current -= size;
    frame15_info_for_frame15_id(frame15_id_of(g))->shared_lines -= size;
    //fprintf(gclog, "defrag reserve giving out linegroup %p +> %d\n", g, size);
    return g;
  }
};

defrag_reserve_t defrag_reserve;

// TODOX
int num_avail_defrag_lines() { return defrag_reserve.reserved_lines_current; }
int num_assigned_defrag_lines() { return defrag_reserve.reserved_lines_target; }

void display_linemap_for_frame15_id(frame15_id fid);
void display_usedmap_for_frame15_id(frame15_id fid);
void mark_slot_used(void* slot);
void mark_slots_used(void* slot, uint64_t cell_size);


struct space_allocator_t {
  space_allocator_t() : curr_frame15(0) {}

private:
  std::vector<frame21*>   frame21s;
  std::vector<frame15_id> frame15s;

  size_t curr_frame15;

  std::vector<free_linegroup*> singles;
  std::vector<free_linegroup*> biggers;

public:
  void reset_scan(int64_t lines_reclaimed) {
    curr_frame15 = 0;
    reset_marked_histogram();

    // Make sure no line groups persist between collections.
    singles.clear();
    biggers.clear();

    int64_t num_lines_left_to_give = lines_reclaimed / 4; // at most...
    //fprintf(gclog, "Reclaimed %zd lines, willing to give at most %zd for defrag reserve.\n", lines_reclaimed,  num_lines_left_to_give);
    while (num_lines_left_to_give > 0 && !defrag_reserve.full()) {
      auto fg = grab_free_linegroup<true>(1, IMMIX_LINES_PER_FRAME15);
      // Invariant: slots marked used.
      if (fg) {
        num_lines_left_to_give -= linegroup_size_in_lines(fg);
        defrag_reserve.give_lines(fg);
      } else break;
    }
  }

  void display_heap_linemaps() {
    for (auto fid : frame15s) { display_linemap_for_frame15_id(fid); }
  }

  void set_heap_size(ssize_t maxbytes) {
    // Round up; a request for 10K should be one frame15, not zero.
    auto frame15s_left = (maxbytes + ((1 << 15) - 1)) >> 15;

    auto mb = foster::humanize_s(double(maxbytes), "B");
    auto fb = foster::humanize_s(double(frame15s_left * (1 << 15)), "B");
    fprintf(gclog, "byte_limit: maxbytes = %s, maxframe15s = %ld, framebytes=%s, maxlines=%ld\n",
          mb.c_str(), frame15s_left, fb.c_str(), frame15s_left * IMMIX_LINES_PER_FRAME15);

    // At 10M, 1% + 4 == 4 + 4 = 2%; at 1000M, 1% + 4 = 400 + 4 = 1.01%
    auto num_defrag_reserved_frames =
          ENABLE_OPPORTUNISTIC_EVACUATION
            ? int(double(frame15s_left) * kFosterDefragReserveFraction) + 4 // + 6;
            : 0;

    frame15s_left -= num_defrag_reserved_frames;

    while (frame15s_left >= IMMIX_F15_PER_F21) {
      frame15s_left -= IMMIX_F15_PER_F21;
      frame21s.push_back(allocate_frame21());
      for (int i = 0; i < IMMIX_F15_PER_F21; ++i) {
        frame15s.push_back(frame15_id_of(offset(frame21s.back(), i << 15)));
        mark_as_smallmedium(frame15_for_frame15_id(frame15s.back()));
      }
    }

    if (frame15s_left > 0) {
      frame21s.push_back(allocate_frame21());
      for (int i = 0; i < frame15s_left; ++i) {
        frame15s.push_back(frame15_id_of(offset(frame21s.back(), i << 15)));
        mark_as_smallmedium(frame15_for_frame15_id(frame15s.back()));
      }
    }

    for (int i = 0; i < num_defrag_reserved_frames; ++i) {
      defrag_reserve.give_lines(grab_free_linegroup<false>(IMMIX_LINES_PER_FRAME15, IMMIX_LINES_PER_FRAME15));
    }
    defrag_reserve.freeze_target_line_count();
  }

  //           [                                 |     excess       ]
  // g: *----- ^                             rv: ^                  ^
  // g->bound:------------------------------------------------------+
  free_linegroup* trim_linegroup(free_linegroup* g, int size,
                                 int num_lines_needed, int max_lines_wanted) {
    // Return a tombstone if no excess to trim.
    if (num_lines_needed > max_lines_wanted) return nullptr;
    int excess_lines = size - max_lines_wanted;
    if (excess_lines <= 0) {
      return nullptr;
    }

    free_linegroup* rv = (free_linegroup*) offset(g->bound, -excess_lines * IMMIX_BYTES_PER_LINE);
    rv->bound = g->bound;
    g->bound = rv;
    return rv;
  }

  template<bool small>
  free_linegroup* grab_free_linegroup(size_t num_lines, size_t max_lines_wanted) {
    int big_limit = 0;

    while (true) {
      if (small) {
        if (!singles.empty()) {
          auto g = singles.back(); singles.pop_back();
          //fprintf(gclog, "marking single allocated line (size %zd) at %p\n", distance(g, g->bound), g);
          mark_slot_used(g); // mark until cleared during collection
          //clear_object_mark_bits_for_group(g);
          return g;
        }
      }

      // Remove tombstones from tail.
      while ((!biggers.empty()) && (biggers.back() == nullptr)) {
        biggers.pop_back();
      }

      // Search for large enough entry and leave a tombstone.
      for (int i = biggers.size() - 1; i >= big_limit; i--) {
        auto g = biggers[i];
        if (!g) continue;
        auto size = linegroup_size_in_lines(g);
        if (size >= num_lines) {
          biggers[i] = trim_linegroup(g, size, num_lines, max_lines_wanted);
          //fprintf(gclog, "marking to-be-allocated span of %zd bytes at %p - %p\n", distance(g, g->bound), g, g->bound);
          //fflush(gclog);
          mark_slots_used(g, distance(g, g->bound)); // mark until cleared
          //clear_object_mark_bits_for_group(g);
          return g;
        }
      }

      if (curr_frame15 == frame15s.size()) {
        return nullptr;
      }

      big_limit = biggers.size();

      process_frame15(frame15s[curr_frame15]);

      ++curr_frame15;
    }
  }

  // TODO compute/update mark histograms here; it's now the only place, more or less,
  //      where we naturally inspect full frame15s.   num_marked_lines and num_holes_found.
  /*
  */
  void process_frame15(frame15_id fid) {
    //uint8_t* linemarks = linemap_for_frame15_id(fid);
    uint8_t* line_status = line_used_for_frame15_id(fid);
    auto f15 = frame15_for_frame15_id(fid);

    if (GCLOG_PRINT_USED_GROUPS) {
      fprintf(gclog, "PF15: "); display_usedmap_for_frame15_id(fid);
    }

    int num_holes_found = 0;
    int num_available_lines = 0;
    for (int i = 0; i < IMMIX_LINES_PER_FRAME15; ++i) {
      if (line_is_marked(i, line_status)) {
        continue;
      }
      int i0 = i;

      ++num_holes_found;
      free_linegroup* g = (free_linegroup*) offset(f15, i * IMMIX_BYTES_PER_LINE);
      //PREFETCH_FOR_WRITES(g);
      while (true) {
        ++i;
        if (i == IMMIX_LINES_PER_FRAME15 || line_is_marked(i, line_status)) {
          break;
        }
      }
      num_available_lines += (i - i0);
      g->bound = offset(f15, i * IMMIX_BYTES_PER_LINE);
      helpers::clear_line_and_object_mark_bits_for_used_group(used_group_of_free_group(g));

      if (i == i0 + 1) {
        singles.push_back(g);
      } else {
        //fprintf(gclog, "bigger: i0 =  %d; i = %d; size = %d; g=%p; g->bound=%p;; frame=%u\n", i0, i, distance(g, g->bound), g, g->bound, frame15_id_of(g));
        biggers.push_back(g);
      }
    }

    int num_marked_lines = IMMIX_LINES_PER_FRAME15 - num_available_lines;
    auto finfo = frame15_info_for(f15);


    if (num_marked_lines == 0) {
      finfo->shared_lines = 0;
    }

    //fprintf(gclog, "LSFA: ");
    //display_linemap_for_frame15_id(fid);

    if (gcglobals.allocator == gcglobals.default_allocator) {
      finfo->num_available_lines_at_last_collection = num_available_lines;
      finfo->num_holes_at_last_full_collection = num_holes_found;
      gcglobals.marked_histogram[num_holes_found] += num_marked_lines;
      gcglobals.marked_histogram_frames[num_holes_found] += 1;
      gcglobals.residency_histogram[num_holes_found] += gcglobals.lazy_mapped_frame_liveness[fid];
    }

    gcglobals.lazy_mapped_frame_liveness[fid] = 0;
  }

public:
  double  full_heap_line_count() { return double(frame15s.size() * IMMIX_LINES_PER_FRAME15); }
};

class immix_line_space;
immix_line_space* get_owner_for_immix_line_frame15(immix_line_frame15* f, int line);

space_allocator_t global_space_allocator;

// Returns a number between zero and 63.
//uint8_t frame15_id_within_f21(frame15_id global_fid) { return uint8_t(low_n_bits(global_fid, 21 - 15)); }

uint8_t count_marked_lines_for_frame15(frame15* f15, uint8_t* linemap_for_frame);

void display_usedmap_for_frame15_id(frame15_id fid) {
  bool shared = frame15_info_for_frame15_id(fid)->shared_lines > 0;
  uint8_t* linemap = line_used_for_frame15_id(fid);
  fprintf(gclog, "frame %u: (used)       ", fid);
  for (int i = 0; i < IMMIX_LINES_PER_FRAME15; ++i) { fprintf(gclog, "%c", linemap[i] ? 'd' : '_'); }
  fprintf(gclog, "\n");
}

void display_linemap_for_frame15_id(frame15_id fid) {
  bool shared = frame15_info_for_frame15_id(fid)->shared_lines > 0;
  uint8_t* linemap = linemap_for_frame15_id(fid);
  fprintf(gclog, "frame %u:              ", fid);
  for (int i = 0; i < IMMIX_LINES_PER_FRAME15; ++i) { fprintf(gclog, "%c", linemap[i] ? 'd' : '_'); }

  int byte_residency_out_of_32 = int((double(gcglobals.lazy_mapped_frame_liveness[fid]) / 32768.0) * 32.0);
  int num_marked_lines = count_marked_lines_for_frame15(frame15_for_frame15_id(fid), linemap);
  int line_residency_out_of_32 = num_marked_lines / 4;
  fprintf(gclog, "  |");
  for (int i = 31; i >= 0; --i) {
    fprintf(gclog, (i < byte_residency_out_of_32) ? "-" :
                  ((i < line_residency_out_of_32) ? "=" : " ")); }
  fprintf(gclog, "|");
  fprintf(gclog, " %c", shared ? 'S' : '.');
  fprintf(gclog, "\n");
}

void display_used_linegroup_linemap(used_linegroup* g, uint8_t* linemap, immix_space* space) {
  if (g->count == IMMIX_LINES_PER_FRAME15) {
    auto fid = frame15_id_of(g->base);
    display_linemap_for_frame15_id(fid);
  } else {
    fprintf(gclog, "  used linegroup (%u): ", frame15_id_of(g->base));
    for (int i = 0; i < IMMIX_LINES_PER_FRAME15; ++i) {
      if (i < g->startline() || i >= g->endline()) fprintf(gclog, "?");
      else {
        fprintf(gclog, "%c", linemap[i] ? 'd' : '_');
      }
    }
    bool shared = frame15_info_for_frame15_id(frame15_id_of(g->base))->shared_lines > 0;
    fprintf(gclog, " in space %p; shared? %d\n", space, shared);
  }
}


void used_linegroup::clear_line_and_object_mark_bits() {
  uint8_t* linemap = linemap_for_frame15_id(associated_frame15_id());
  auto lineframe = associated_lineframe();

  gc_assert(startline() != endline(), "used linegroup had same start and end line...?");

  // Note: must clear only our bits, since those of other groups may not yet have been inspected.
  for (int i = startline(); i < endline(); ++i) {
    //fprintf(gclog, "clearing linemap entry %d for (%u), linemap addr: %p\n", i, associated_frame15_id(), &linemap[i]);  fflush(gclog);
    do_unmark_line(i, linemap);
  }
  gc_assert(startline() >= 0, "invalid startline when clearing bits");
  gc_assert(endline() <= IMMIX_LINES_PER_BLOCK, "invalid endline when clearing bits");
  gc_assert(startline() < endline(), "invalid: startline after endline when clearing bits");
  //clear_object_mark_bits_for_frame15(lineframe, startline(), (endline() - startline()) + 1);
  clear_object_mark_bits_for_used_group(*this);
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
  if ((map = tryGetTypemap(cell))) {
    if (GCLOG_DETAIL > 4) { inspect_typemap(map); }
    if (map->isArray) {
      arr = heap_array::from_heap_cell(cell);
    }
  }
  
  // {{{
  if (!map) {
    cell_size = cell->cell_size();
    if (GCLOG_DETAIL > 3 && cell_size <= 0) { fprintf(gclog, "obj %p in frame (%u) has size %zd (0x%zx)\n", cell,
      frame15_id_of(cell), cell_size, cell_size); fflush(gclog); }
    gc_assert(cell_size > 0, "cannot copy cell lacking metadata or length");
  } else if (!arr) {
    cell_size = map->cell_size; // probably an actual pointer
  } else {
    cell_size = array_size_for(arr->num_elts(), map->cell_size);
    if (GCLOG_DETAIL > 1) {
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

int64_t large_array_allocator::approx_size_in_bytes() {
  int64_t rv = 0;
  auto it = allocated.begin();
  while (it != allocated.end()) {
    void* base = *it;
    heap_array* arr = align_as_array(base);
    rv += array_size_for(arr->num_elts(), arr->get_meta()->cell_size);
  }
  return rv;
}
// }}}

// {{{

void mark_slot_used(void* slot) {
  uint8_t* linemap = line_used_for_frame15_id(frame15_id_of(slot));
  do_mark_line(line_offset_within_f15(slot), linemap);

  set_current_line_stamp(slot, line_stamp_t(gcglobals.num_gcs_triggered & 0xFFFF));
}

void mark_slots_used(void* slot, uint64_t cell_size) {
  uint8_t* linemap = line_used_for_frame15_id(frame15_id_of(slot));
  void* lastslot = offset(slot, cell_size - 8);
  auto firstoff = line_offset_within_f15(slot);
  auto lastoff  = line_offset_within_f15(lastslot);

  auto stamp = line_stamp_t(gcglobals.num_gcs_triggered & 0xFFFF);

  if (firstoff == lastoff) {
    linemap[firstoff] = 1;
    set_current_line_stamp(slot, stamp);
  } else {
    //fprintf(gclog, "marking slots %d to %d (ptrs %p to %p) used...\n", firstoff, lastoff, slot, lastslot); fflush(gclog);
    auto slotsused = (lastoff - firstoff) + 1; // +1 because we want an inclusive count.
    memset(&linemap[firstoff], 1, slotsused + 1);
    for (int i = 0 ; i < slotsused; ++i) {
      set_current_line_stamp(offset(slot, i * IMMIX_BYTES_PER_LINE), stamp);
    }
  }
}

void mark_line_for_slot(void* slot) {
  uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(slot));
  do_mark_line(line_offset_within_f15(slot), linemap);
}

// Precondition: slot is located in a markable frame.
bool line_for_slot_is_marked(void* slot) {
  uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(slot));
  return line_is_marked(line_offset_within_f15(slot), linemap);
}

// Precondition: slot in small/medium/linemap frame,
// therefore slot and lastslot guaranteed to be in the same frame.
void mark_lines_for_slots(void* slot, uint64_t cell_size) {
  uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(slot));

  void* lastslot = offset(slot, cell_size - 8);

  auto firstoff = line_offset_within_f15(slot);
  auto lastoff  = line_offset_within_f15(lastslot);

  //if (MARK_FRAME21S) { mark_frame21_for_slot(slot); }
  //if (MARK_FRAME21S_OOL) { mark_frame21_ool_for_slot(slot); }

  if (/*gcglobals.num_gcs_triggered < 2 ||*/ GCLOG_DETAIL > 3) {
    fprintf(gclog, "gc %d: marking lines %d - %d for slot %p of size %zd; first @ %p in line %d of frame %u\n",
      gcglobals.num_gcs_triggered,
      firstoff, lastoff, slot, cell_size, &linemap[firstoff],
      line_offset_within_f15(slot), frame15_id_of(slot)); }

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

template <condemned_set_status condemned_portion>
bool should_opportunistically_evacuate(heap_cell* obj);


template <typename CellThunk>
void apply_thunk_to_child_slots_of_cell(intr* body, const typemap* map, uint8_t ptrMap, CellThunk thunk) {
  switch (ptrMap & 7) {
    case 0x1:
      thunk((intr*) body);
      break;
    case 0x3:
      thunk((intr*) body);
      thunk((intr*) offset(body, 8));
      break;
    default:
      for (int i = 0; i < map->numOffsets; ++i) {
        thunk((intr*) offset(body, map->offsets[i]));
      }
  }
}

template <typename CellThunk>
void for_each_child_slot_with(heap_cell* cell, heap_array* arr, const typemap* map,
                              int64_t cell_size, CellThunk thunk) {
  if (!map) { return; }

  //refPatterns[refPattern(map)]++;

  uint8_t ptrMap = map->ptrMap;
  if (ptrMap == 0) { return; }

  if (!arr) {
    apply_thunk_to_child_slots_of_cell(from_tidy(cell->body_addr()), map, ptrMap, thunk);
  //} else if (map->numOffsets == 1 && map->offsets[0] == 0 && map->cell_size == sizeof(void*)) {
  //  int64_t numcells = arr->num_elts();
  //  for (int64_t cellnum = 0; cellnum < numcells; ++cellnum) {
  //    thunk(arr->elt_body(cellnum, map->cell_size));
  //  }
  } else {
    int64_t numcells = arr->num_elts();
    for (int64_t cellnum = 0; cellnum < numcells; ++cellnum) {
      apply_thunk_to_child_slots_of_cell(arr->elt_body(cellnum, map->cell_size), map, ptrMap, thunk);
    }
  }

  if (map->isCoro == 1) {
    // Coroutines reference stacks which contain embedded references to the heap
    // that (for performance) are not tracked by write barriers.
    // TODO fix
    foster_bare_coro* coro = reinterpret_cast<foster_bare_coro*>(cell->body_addr());
    collect_roots_from_stack_of_coro(coro);
    //fprintf(gclog, "for_each_child_slot noticed a coro object...\n");
  }
}

template <typename CellThunk>
void for_each_child_slot(heap_cell* cell, CellThunk thunk) {
  heap_array* arr = NULL;
  const typemap* map = NULL;
  int64_t cell_size;
  get_cell_metadata(cell, arr, map, cell_size);
  for_each_child_slot_with(cell, arr, map, cell_size, thunk);
}

// This struct contains per-frame state and code shared between
// regular and line-based immix frames.
namespace immix_common {

  void* evac_with_map_and_arr(heap_cell* cell, const typemap* map,
                             heap_array* arr, int64_t cell_size,
                             immix_space* tospace);

  // Precondition: cell is part of the condemned set.
  // Precondition: cell is not forwarded.
  void* scan_and_evacuate_to(immix_space* tospace, heap_cell* cell) {

    heap_array* arr = NULL;
    const typemap* map = NULL;
    int64_t cell_size;
    get_cell_metadata(cell, arr, map, cell_size);

    // Without metadata for the cell, there's not much we can do...
    if (map && gcglobals.typemap_memory.contains((void*) map)) {
      return evac_with_map_and_arr(cell, map, arr, cell_size, tospace);
    }
    return nullptr;
  }

  // Precondition: cell is part of the condemned set and not yet marked.
  void scan_cell(heap_cell* cell) {
    heap_array* arr = NULL;
    const typemap* map = NULL;
    int64_t cell_size;
    get_cell_metadata(cell, arr, map, cell_size);

    do_mark_obj_of_size(cell, cell_size);

#if 0
    if (cell_size > 8192) {
      fprintf(gclog, "WARN: scan_cell marking corrupt cell %p of size %zd\n", cell, cell_size);
      fprintf(gclog, "   header was %zx\n", cell->raw_header());
    }
#endif

    for_each_child_slot_with(cell, arr, map, cell_size, [cell](intr* slot) {
      if (!non_markable_addr(* (void**)slot)) {
        if (0) {
        fprintf(gclog, "gc %d: adding to worklist slot %p of cell %p holding ptr %p\n",
                        gcglobals.num_gcs_triggered,
                        slot,
                        cell,
                        * (void**)slot);
        }
        immix_worklist.add_root((unchecked_ptr*) slot);
      }
    });

    if (TRACK_NUM_OBJECTS_MARKED) { gcglobals.num_objects_marked_total++; }
    if (TRACK_NUM_OBJECTS_MARKED) { gcglobals.alloc_bytes_marked_total += cell_size; }

    frame15info* finfo = frame15_info_for_frame15_id(frame15_id_of(cell));
    auto frameclass = finfo->frame_classification;
    if (/*gcglobals.num_gcs_triggered < 2 ||*/ GCLOG_DETAIL > 3) { fprintf(gclog, "frame classification for obj %p in line %d of frame %u is %d\n", cell, line_offset_within_f15(cell), frame15_id_of(cell), int(frameclass)); }

    if (frameclass == frame15kind::immix_smallmedium) {
        mark_lines_for_slots((void*) cell, cell_size);
        gcglobals.lazy_mapped_frame_liveness[frame15_id_of(cell)] += uint16_t(cell_size);
    } else if (frameclass == frame15kind::unknown) {
      gcglobals.condemned_set.unframed_and_marked.insert(cell);
      // malloc_start/malloc_continue needs no line marks at all.
    }
  }

  // Jones/Hosking/Moss refer to this function as "process(fld)".
  // Returns 1 if root was located in a condemned space; 0 otherwise.
  // Precondition: root points to an unmarked, unforwarded, markable object.
  template <condemned_set_status condemned_portion>
  void immix_trace(unchecked_ptr* root, heap_cell* obj) {
    //       |------------|       obj: |------------|
    // root: |    body    |---\        |  size/meta |
    //       |------------|   |        |------------|
    //                        \- tidy->|            |
    //                        |       ...          ...
    //                        \-*root->|            |
    //                                 |------------|

    if (ENABLE_OPPORTUNISTIC_EVACUATION &&
        should_opportunistically_evacuate<condemned_portion>(obj)) {
      auto tidyn = scan_and_evacuate_to((immix_space*)gcglobals.default_allocator, obj);
      *root = make_unchecked_ptr((tori*) tidyn);
    } else {
      scan_cell(obj);
    }
  }

  template <condemned_set_status condemned_portion>
  uint64_t process_remset(immix_space* space) {
    remset_with_obj_t& incoming_ptr_addrs = space_incoming_ptr_addrs(space);
    uint64_t numRemSetRoots = 0;
    //fprintf(gclog, "copying incoming ptrs to vector for space %p (linked? %d)\n", space, space->is_linked_to_default_subheap); fflush(gclog);

    auto slots = incoming_ptr_addrs.copy_to_vector();

    //fprintf(gclog, "starting with %zd slots\n", slots.size()); fflush(gclog);
    int n = 0;
    for (auto p : slots) {
      tori** src_slot = p.first;
      tidy*  src_obj  = p.second.first;
      uint16_t orig_stamp = p.second.second;

      if (0) {
        fprintf(gclog, "gc %d: examining remsetx slot %d of space %p; src slot is %p; obj is %p ;; holding %p; rss %d vs cos %d (css %d)\n",
          gcglobals.num_gcs_triggered, n, space, src_slot, src_obj, *src_slot,
          orig_stamp, get_current_line_stamp(src_obj), get_current_line_stamp(src_slot)
          ); ++n;  fflush(gclog);
      }

      bool header_definitely_stale = get_current_line_stamp(src_obj) != orig_stamp;

      if (header_definitely_stale) {
        //fprintf(gclog, "INFO: definitely stale entry for src slot %p\n", src_slot);
        continue;
      }

      // We can ignore the remembered set root if the source is also getting collected.
      // TODO fix
      if (obj_is_condemned<condemned_portion>(src_obj)) {
        if (GCLOG_DETAIL > 3) {
          fprintf(gclog, "space %p skipping ptr %p, from remset, in co-condemned slot %p\n", space, *src_slot, src_slot);
        }
        continue;
      }

      // TODO ptr can be arbitrary garbage! We can't assume it's tidy or even interior...
      tori* ptr = *src_slot;
      //fprintf(gclog, "  slot contains %p\n", ptr);

      auto cell = heap_cell::for_tidy((tidy*)ptr);
 
      // Otherwise, we must check whether the source slot was modified;
      // if so, it might not point into our space (or might point to a
      // non-condemned portion of our space).
      if ((classification_for_frame15_id(frame15_id_of(*src_slot)) == frame15kind::immix_smallmedium)
        && heap_for_header(cell->raw_header()) == space
        && obj_is_condemned<condemned_portion>((tidy*) ptr)) {
        uint64_t rawheader = heap_cell::for_tidy(assume_tori_is_tidy(untag(make_unchecked_ptr(ptr))))->raw_header();
        const typemap* purported_typemap = heap_cell::for_tidy(assume_tori_is_tidy(untag(make_unchecked_ptr(ptr))))->get_meta();
        if (gcglobals.typemap_memory.contains((void*) purported_typemap)) {
          if (TRACK_NUM_REMSET_ROOTS) { numRemSetRoots++; }

          if (0) {
            fprintf(gclog, "gc %d: space %p visiting root slot with ptr %p: slot %p with raw header %zx; src obj header is %zx\n",
              gcglobals.num_gcs_triggered,
              space, ptr, src_slot, rawheader,
              heap_cell::for_tidy(src_obj)->raw_header()); fflush(gclog);
          }

          helpers::visit_root((unchecked_ptr*) src_slot, "remembered_set_root");
        } else {
          fprintf(gclog, "gc %d: space %p skipping remset bad-typemap ptr %p in slot %p\n",
              gcglobals.num_gcs_triggered,
              space, ptr, src_slot);
        }
      } else {
        if (GCLOG_DETAIL > 3) {
          if (classification_for_frame15_id(frame15_id_of(*src_slot)) == frame15kind::immix_smallmedium) {
            fprintf(gclog, "gc %d: space %p skipping remset non-condemned ptr %p in slot %p with hdr %zx, cond %d\n",
                gcglobals.num_gcs_triggered,
                space, ptr, src_slot,
                cell->raw_header(),
                obj_is_condemned<condemned_portion>((tidy*) ptr)
                );
          } else {
            // can't derf ptr
            fprintf(gclog, "gc %d: space %p skipping remset non-condemned ptr %p in slot %p\n",
                gcglobals.num_gcs_triggered,
                space, ptr, src_slot
                //cell->raw_header());
                //obj_is_condemned<condemned_portion>((tidy*) ptr)
                );
          }
        }
      }
    }
    return numRemSetRoots;
  }

  uint64_t process_subheap_remsets(immix_space* space) {
    // To boost tracing efficiency, pre-compile different variants of the tracing code
    // (using templates) specialized to what portion of the heap is being traced.
    switch (gcglobals.condemned_set.status) {
    case                    condemned_set_status::per_frame_condemned:
      return process_remset<condemned_set_status::per_frame_condemned>(space);
    case                    condemned_set_status::whole_heap_condemned:
      return process_remset<condemned_set_status::whole_heap_condemned>(space);
    case                    condemned_set_status::default_and_linked:
      return process_remset<condemned_set_status::default_and_linked>(space);
    }
  }

  // Returns true if we should immediately retry GC (e.g. to switch to full-heap non-sticky collection).
  bool common_gc(bool voluntary, bool emergency);
};

class immix_space_tracking {
  std::vector<used_linegroup> used_lines;
  ssize_t lines_tracked;

public:
  immix_space_tracking() : lines_tracked(0) {}
  ~immix_space_tracking() {}

  void add_free_group(free_linegroup* fg) {
     used_linegroup ug = { .base = fg, .count = linegroup_size_in_lines(fg) };
     note_used_group(ug);
  }
  void note_used_group(used_linegroup g) { used_lines.push_back(g); lines_tracked += g.count; }

  template<typename WasUncleanThunk>
  void iter_used_lines_taking_ownership(WasUncleanThunk thunk) {
    std::vector<used_linegroup> holder;
    holder.swap(used_lines);
    lines_tracked = 0;
    for (auto g : holder) {
      thunk(g);
    }
  }

  template<typename WasUncleanThunk>
  void iter_used_lines_void(WasUncleanThunk thunk) {
    for (auto g : used_lines) {
      thunk(g);
    }
  }

  size_t num_lines_tracked() { return lines_tracked; }
  size_t num_groups_tracked() { return used_lines.size(); }
};


/*

                Subheap frame state transition diagram
                ======================================

 +----------+
 |          |
 |  global  |
 |   pool   |
 |          | <---------------------------+
 +--------+-+                             +
          |                          condemned  <--------+
          |                      (5)      +              |
          |                            .-+++-.           |
     (3)  |                           /       \          |
          |                           |       |          |
          |                           |       |          |
          v                           |       |          |
                                      v       v          |
        current <--------------- recycled    full        |
    (1) ~~~~~~~       (2)        ........    ....        |
             ...                ..          ..           |
               ..              ..         ...            |
                ..            ..       ....              |
                 ..          ..    .....                 |
                  ...................                    |
                         +                               |
                    (4)  |                               |
                         +-------------------------------+


  (1) Allocations go into the current frame.
      When it fills up, it is sent to the full bucket.

  (2) Replacement frames are drawn from the recycled bucket, or from
  (3) the global pool (as permitted by per-subheap limits).

  (4) `subheapCondemn` siphons the subheap's used (i.e. non-clean)
      frames into the condemned bucket. The current frame is treated
      as clean if it is completely empty. Siphoned frames are marked
      to permit constant time identification during collection.

      If the condemned bucket is empty when collection is implicitly
      triggered,  an implicit collection

  (5) ``subheapCollect`` first inspects the remembered set.
      followed by the stack. We note, when inspecting stack roots,
      whether any point to condemned objects. If there are no roots
      (from the stack or remembered set) to condemned objects from
      uncondemned objects, the subheap can be immediately reclaimed.
      Otherwise, we trace from the roots as usual, producing object
      and line marks. When tracing completes, line marks are used to
      sort frames into the appropriate buckets.

      When the condemned set carries frames from multiple subheaps,
      we can inspect each frame to determine its subheap of origin.


      ``(subheapReclaim S)`` combines steps (4) and (5), without
      explicitly representing the condemned set -- instead, every
      frame in S is considered condemned.

      Steps (4) and (5) each have a component that is linear in the
      size of the condemned set, but the constant factor is roughly
      three orders of magnitude faster than allocation itself.

      Back of the envelope calculation: 1GB = 32k * 32KB.
                                       64GB = 32k * 2MB.
      What's the approximate cost **of a round trip to memory** for ~32k frames?
            200 cycles * 32e3 / 4e6 cycles/ms => 1.6 ms

      In practice, prefetching and locality of reference helps quite a lot:
        we can scan linemaps for 32k frame15s in ~325us (on a Core i5 6600k)
               and set condemned status bytes in ~100us (when densely packed).
      Interestingly, when status bytes are embedded at the start of a frame15,
      setting condemned marks is much more expensive: 800us instead of 100us.

      The increased locality from tracking 2MB frame21s helps a little bit with
      latency of line marking, on the order of ~40%.
      If we mark 2MB frame21s in addition to lines, being able to rapidly identify
      unmarked frames speeds reclamation by ~3.5x (~250%).

      But note here that static/inline mark bytes are advantageous for coarser marks,
      because it allows us to avoid loading a global variable during marking,
      and since multiple frame15s share a frame21, hardware (store buffers & caches)
      are significantly more effective.

      According to (my testing of) https://github.com/wrl/thread-sync-latency-tests
      mean latency of thread wakeup is ~20us and worst case is ~8ms, suggesting that
      waking a sleeping thread is too risky from a latency perspective to be worth it.

*/


// Opportunistically merges when line groups are inserted in sorted order.
void append_linegroup(std::vector<used_linegroup>& lines, used_linegroup u) {
  if (lines.empty()) { lines.push_back(u); return; }

  used_linegroup& last = lines.back();
  if (frame15_id_of(last.base) == frame15_id_of(u.base)
             && last.endline() == u.startline()) {
    //fprintf(gclog, "append_linegroup() extending count %d by %d for base %p\n", last.count, u.count, last.base);
    //fprintf(gclog, "   last: base %p, count %d, lines %d to %d\n", last.base, last.count, last.startline(), last.endline());
    //fprintf(gclog, "      u: base %p, count %d, lines %d to %d\n", u.base, u.count, u.startline(), u.endline());
    last.count += u.count;
  } else {
    lines.push_back(u);
  }
}

#if DEBUG_VERIFY_MARK_BITS
std::set<heap_cell*> g_marked_this_cycle;
#endif

void process_worklist();
void do_compactify_via_granule_marks(immix_space* default_subheap,
                                     std::vector<frame15_id>& all_ids,
                                     std::vector<used_linegroup>& shared_lines);

bool immix_common::common_gc(bool voluntary, bool emergency) {
#if DEBUG_VERIFY_MARK_BITS
    g_marked_this_cycle.clear();
#endif

    g_approx_lines_allocated_since_last_collection = 0;
    auto num_marked_at_start   = gcglobals.num_objects_marked_total;
    auto bytes_marked_at_start = gcglobals.alloc_bytes_marked_total;

    bool should_compact = !voluntary
                      && (gcglobals.last_full_gc_compaction_headroom_estimate
                          >= __foster_globals.compaction_threshold);

    bool is_sticky_collection = !voluntary && !emergency && !should_compact
                                && gcglobals.next_collection_sticky;
    if (is_sticky_collection) { gcglobals.num_gcs_triggered_nurseryonly++; }
    bool unstick_next_coll = false;


    if (GCLOG_PRINT_LINE_MARKS) {
      if (is_sticky_collection) {
        fprintf(gclog, "Sticky collection starting with the following marks:\n");
        global_space_allocator.display_heap_linemaps();
      }
    }

    gcglobals.num_gcs_triggered += 1;
    if (!voluntary) { gcglobals.num_gcs_triggered_involuntarily++; }
    if (PRINT_STDOUT_ON_GC) { fprintf(stdout, "                        start GC #%d\n", gcglobals.num_gcs_triggered); fflush(stdout); }
    if (ENABLE_GCLOG_ENDGC) { fprintf( gclog, "                        start GC #%d; voluntary? %d; sticky? %d; compact? %d; emergency? %d; typ %d\n",
          gcglobals.num_gcs_triggered, voluntary, is_sticky_collection, should_compact, emergency,
          (int) gcglobals.condemned_set.status); fflush(gclog); }

    clocktimer<false> gcstart; gcstart.start();
    clocktimer<false> phase;
#if ENABLE_GC_TIMING_TICKS
    int64_t t0 = __foster_getticks_start();
#endif

    if (!voluntary) {
      if (is_sticky_collection && (num_avail_defrag_lines() < (num_assigned_defrag_lines() / 2))) {
        fprintf(gclog, "Scheduling un-sticky collection due to defrag reserve shortage.\n");
        unstick_next_coll = true;
      }

      if (gcglobals.last_full_gc_fragmentation_percentage > 0.0) {
        // This dynamically corrects for the (a priori unknown) density
        // of lines on defragmented frames. A factor of 2.0 implies that
        // lines selected for defragmentation are, on average, half full.
        // The density of lines on defragmentation-candidate frames is
        // a priori unknown. We assume lines are 50% full. Note: the goal
        // of this guess is not to maximize the amount of data copied into
        // our defrag reserve; the ideal is to defrag just enough that
        // (rare) medium allocations don't cause premature triggering of GC.
        // A runtime-adaptive scheme to adjust the pad factor can consistently
        // use more of the defrag reserve, but doing so usually just degrades
        // performance, since the extra copying has more cost than benefit.
        double defrag_pad_factor = 2.0;
        gcglobals.evac_threshold = select_defrag_threshold(defrag_pad_factor);
        reset_marked_histogram();
      } else {
        if (GCLOG_DETAIL > 0) {
          // Disable evacuation because there isn't much fragmentation to eliminate.
          fprintf(gclog, "disabling evacuation because there isn't much fragmentation to eliminate (%.1f).\n",
              gcglobals.last_full_gc_fragmentation_percentage);
          gcglobals.evac_threshold = 0;

          fprintf(gclog, "should compact? %d  :::  %f vs %f\n", 
              should_compact,
              gcglobals.last_full_gc_compaction_headroom_estimate,
              __foster_globals.compaction_threshold);
        }
      }

      if (should_compact) {
        gcglobals.evac_threshold = 0; // Make sure we don't evacuate; not much point in duplicating work!
        if (is_sticky_collection) {
          fprintf(gclog, "disabling sticky collection (and evacuation) because we want to compact.\n");
          is_sticky_collection = false;
        }
      }
    }

    phase.start();
    uint64_t numGenRoots = 0;
    uint64_t numRemSetRoots = 0;
    gcglobals.condemned_set.prepare_for_collection(voluntary, is_sticky_collection, emergency, &numGenRoots, &numRemSetRoots);
    auto markResettingAndRemsetCollection_us = phase.elapsed_us();

    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "# generational roots: %zu; # subheap roots: %zu (sticky=%d)\n", numGenRoots, numRemSetRoots, is_sticky_collection);
    }


    phase.start();
#if FOSTER_GC_TIME_HISTOGRAMS && ENABLE_GC_TIMING_TICKS
    int64_t phaseStartTicks = __foster_getticks_start();
#endif

    collect_roots_from_stack(__builtin_frame_address(0));

    auto rootCollection_us = phase.elapsed_us();

#if FOSTER_GC_TIME_HISTOGRAMS && ENABLE_GC_TIMING_TICKS
    hdr_record_value(gcglobals.hist_gc_rootscan_ticks, __foster_getticks_elapsed(phaseStartTicks, __foster_getticks_end()));
#endif

    //hdr_record_value(gcglobals.hist_gc_stackscan_roots, gNumRootsScanned);
    phase.start();
    foster_bare_coro** coro_slot = __foster_get_current_coro_slot();
    foster_bare_coro*  coro = *coro_slot;
    if (coro) {
      if (GCLOG_DETAIL > 1) {
        fprintf(gclog, "==========visiting current coro: %p\n", coro); fflush(gclog);
      }
      helpers::visit_root((unchecked_ptr*)coro_slot, NULL);
      if (GCLOG_DETAIL > 1) {
        fprintf(gclog, "==========visited current coro: %p\n", coro); fflush(gclog);
      }
    }

    if (GCLOG_DETAIL > 1) { fprintf(gclog, "    THRESHOLD IS %d\n", gcglobals.evac_threshold); }

    process_worklist();

    auto deltaRecursiveMarking_us = phase.elapsed_us();

    if (GCLOG_PRINT_LINE_MARKS) { global_space_allocator.display_heap_linemaps(); }

    phase.start();

    auto bytes_marked = gcglobals.alloc_bytes_marked_total - bytes_marked_at_start;

    if (!voluntary) {
      g_bytes_marked = bytes_marked;
    }
    g_should_compact = !voluntary && should_compact;

    gcglobals.condemned_set.lines_live = 0;
    bool hadEmptyRootSet = false; // (numCondemnedRoots + numRemSetRoots + numGenRoots) == 0;
    int64_t num_lines_tracked = 0;
    int64_t num_groups_tracked = 0;
    int64_t num_lines_reclaimed = gcglobals.condemned_set.sweep_condemned(
                                                phase, emergency, hadEmptyRootSet,
                                                &num_lines_tracked, &num_groups_tracked);
    double sweep_us = phase.elapsed_us();

    auto line_footprint = gcglobals.condemned_set.lines_live; // Note: only valid for involuntary collections.
    auto line_footprint_in_bytes = line_footprint * IMMIX_BYTES_PER_LINE;
    auto gains_from_perfect_compaction =
            (line_footprint_in_bytes < bytes_marked)
                ? 0
                : (line_footprint_in_bytes - bytes_marked) / IMMIX_BYTES_PER_LINE;
    auto estimated_reclaimed_lines_from_compaction =
          int64_t(double(gains_from_perfect_compaction) * 0.85);

    if (!voluntary && GCLOG_DETAIL > 0) {
      fprintf(gclog, "Compaction estimate:\n");
      fprintf(gclog, "   Bytes marked: %zd; line footprint in bytes: %zd\n", bytes_marked, line_footprint_in_bytes);
      fprintf(gclog, "   Absolute gain in lines: %zd\n", estimated_reclaimed_lines_from_compaction);
      fprintf(gclog, "   As a percentage of line footprint: %.1f\n",
          double(estimated_reclaimed_lines_from_compaction * IMMIX_BYTES_PER_LINE)/double(line_footprint_in_bytes));
    }

    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "%zd groups tracking %zd lines (avg %.1f lines/group).\n",
        num_groups_tracked, num_lines_tracked, double(num_lines_tracked)/double(num_groups_tracked));
    }

    if (!voluntary) {
      double reclamation_headroom_factor =
            double(estimated_reclaimed_lines_from_compaction) / double(num_lines_reclaimed + 1);

      gcglobals.last_full_gc_compaction_headroom_estimate
          = reclamation_headroom_factor;

      if (!voluntary || GCLOG_DETAIL > 0) {
        fprintf(gclog, "Estimated gains from compaction: %zd lines (vs %zd; %.1fx)\n",
          estimated_reclaimed_lines_from_compaction, num_lines_reclaimed, reclamation_headroom_factor);
      }

      double byte_level_fragmentation_percentage =
        ((double(line_footprint_in_bytes) / double(bytes_marked)) - 1.0) * 100.0;

      gcglobals.last_full_gc_fragmentation_percentage =
        byte_level_fragmentation_percentage;

      if (GCLOG_DETAIL > 0) {
        fprintf(gclog, "Byte level fragmentation percentage: %.1f\n",
            byte_level_fragmentation_percentage);
      }
    }

    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "Line footprint in bytes: %zd; bytes marked: %zd\n",
          line_footprint_in_bytes, bytes_marked);
    }

    /*
    fprintf(gclog, "xGC %d bytesmarked: %zd linesleft:gg %zd linefootprint: %zd bytesleft: %zd bytefootprint: %zd\n",
      gcglobals.num_gcs_triggered, bytes_marked,
      int64_t(global_space_allocator.full_heap_line_count()) - line_footprint,
      line_footprint,
      (int64_t(global_space_allocator.full_heap_line_count()) - line_footprint) * IMMIX_BYTES_PER_LINE,
      (line_footprint) * IMMIX_BYTES_PER_LINE);
      */

  if (GCLOG_DETAIL > 0 || ENABLE_GCLOG_ENDGC) {
    if (TRACK_NUM_OBJECTS_MARKED) {
      if (!voluntary) {
        gcglobals.max_bytes_live_at_whole_heap_gc =
          std::max(gcglobals.max_bytes_live_at_whole_heap_gc, bytes_marked);
      }
      if (is_sticky_collection) {
        auto bytes_alloc = g_approx_lines_allocated_since_last_collection * IMMIX_BYTES_PER_LINE;
        auto s_bytes_live  = foster::humanize_s(bytes_marked, "");
        auto s_bytes_alloc = foster::humanize_s(bytes_alloc, "");
        auto s_bytes_used  = foster::humanize_s(line_footprint_in_bytes, "");
        fprintf(gclog, "%s bytes live / %s line bytes allocated = %f%% overhead (%s bytes used); ",
          s_bytes_live.c_str(), s_bytes_alloc.c_str(),
              (double(bytes_alloc) / double(bytes_marked)) * 100.0,
          s_bytes_used.c_str());

        //fprintf(gclog, "%.1f%% of %zd condemned lines are live\n",
        //  ((double(gcglobals.lines_live_at_whole_heap_gc) / double(approx_condemned_space_in_lines)) * 100.0),
        //  approx_condemned_space_in_lines);
      } else {
        //fprintf(gclog, "%zu bytes live in %zu line bytes; %f%% overhead; %f%% of %zd condemned lines are live\n",
        //  bytes_marked, line_footprint_in_bytes,
        //  byte_level_fragmentation_percentage,
        //  ((double(gcglobals.lines_live_at_whole_heap_gc) / double(approx_condemned_space_in_lines)) * 100.0),
        //  approx_condemned_space_in_lines);
      }
    }
  }

  if (ENABLE_GC_TIMING && GCLOG_MUTATOR_UTILIZATION) {
    auto ems = gcstart.elapsed_ms();
    auto now = gcglobals.init_start.elapsed_s();
    fprintf(gclog, "MUTUTIL %f %f\n", // pause duration in ms, pause start time in s
                    ems, now - (ems / 1000.0));
  }

#if ((GCLOG_DETAIL > 1) || ENABLE_GCLOG_ENDGC)
#   if TRACK_NUM_OBJECTS_MARKED
      fprintf(gclog, "\t%zu objects marked in this GC cycle, %zu marked overall\n",
              gcglobals.num_objects_marked_total - num_marked_at_start,
              gcglobals.num_objects_marked_total);
#   endif

      if (ENABLE_GC_TIMING) {
        double delta_us = gcstart.elapsed_us();
        double other_us = delta_us - (rootCollection_us + deltaRecursiveMarking_us + sweep_us + markResettingAndRemsetCollection_us);
        fprintf(gclog, "\ttook %zd us which was %.2f%% stack root collection, %.2f%% (%.1f us) from remsets & mark resetting, %.2f%% marking, %.2f%% sweeping (%.1f us), %.2f%% other (%.1f us)\n",
                          int64_t(delta_us),
                          (rootCollection_us * 100.0)/delta_us,
                          (markResettingAndRemsetCollection_us * 100.0)/delta_us, markResettingAndRemsetCollection_us,
                          (deltaRecursiveMarking_us * 100.0)/delta_us,
                          (sweep_us * 100.0)/delta_us, sweep_us,
                          (other_us * 100.0)/delta_us, other_us
                          );

        //double collection_us = deltaRecursiveMarking_us + sweep_us;
        //g_sweeping_total_us += sweep_us;
        double lines_per_us = double(num_lines_reclaimed) / delta_us;
        double ns_per_line = (delta_us * 1000.0) / double(num_lines_reclaimed);
        fprintf(gclog, "    lines/us: %.2f;  ns/line: %.2f\n", lines_per_us, ns_per_line);
        
        //fprintf(gclog, "Sweeping reclaimed %zd lines in %f us.     (total RC sweeping time: %.2f us)\n", num_lines_reclaimed, sweeping_us, g_rc_sweeping_total_us);

      }

    if (!voluntary) {
      fprintf(gclog, "\t/endgc %d; voluntary? %d; gctype %d\n\n", gcglobals.num_gcs_triggered,
                                            int(voluntary), int(gcglobals.condemned_set.status));
      fflush(gclog);
    }
#endif

  if (PRINT_STDOUT_ON_GC) { fprintf(stdout, "                              endgc\n"); fflush(stdout); }

  if (ENABLE_GC_TIMING) {
    double delta_us = gcstart.elapsed_us();
    if (FOSTER_GC_TIME_HISTOGRAMS) {
      hdr_record_value(gcglobals.hist_gc_pause_micros, int64_t(delta_us));
    }
    gcglobals.gc_time_us += delta_us;
  }

#if ENABLE_GC_TIMING_TICKS
    int64_t t1 = __foster_getticks_end();
    if (FOSTER_GC_TIME_HISTOGRAMS) {
      hdr_record_value(gcglobals.hist_gc_pause_ticks, __foster_getticks_elapsed(t0, t1));
    }
    auto elapsed_ticks = __foster_getticks_elapsed(t0, t1);
    gcglobals.subheap_ticks += elapsed_ticks;
    if (!voluntary) { gcglobals.involuntary_ticks += elapsed_ticks; }
#endif

    global_space_allocator.reset_scan(num_lines_reclaimed);

    if (unstick_next_coll) gcglobals.next_collection_sticky = false;

    if (is_sticky_collection && !gcglobals.next_collection_sticky) {
      // We're close to running out of room. If we're REALLY close, trigger a non-sticky collection to reclaim more.

      int64_t defrag_headroom_lines = num_assigned_defrag_lines();
      bool need_immediate_recollection = num_lines_reclaimed <= (defrag_headroom_lines / 4);
      // Our "nursery" is full; need a full-heap collection to reset it.
      // Question is, do we trigger an immediate collection or not?
      //  Current heuristic: immediately collect if we didn't reclaim enough to fill the headroom.
      
      if (need_immediate_recollection) {
        // Raise the yield threshold so we make it less likely to trigger a double collection.
        gcglobals.yield_percentage_threshold += 5.0;
        fprintf(gclog, "Triggering immediate non-sticky collection!\n");
      } else {
        // Lower the yield threshold if we've raised it.
        if (gcglobals.yield_percentage_threshold >= (4.0 + __foster_globals.sticky_base_threshold)) {
          gcglobals.yield_percentage_threshold -= 5.0;
          fprintf(gclog, "Adjusted the sticky yield threshold to %.1f\n", gcglobals.yield_percentage_threshold);
        }
      }

      fprintf(gclog, "Sticky->nonsticky, need immediate recollection? %d\n", need_immediate_recollection);
      return need_immediate_recollection;
    }

    if (!voluntary) {
      // Be unsatisfied if we reclaim less than 1% of the heap in a (mostly-)full-heap
      // collection.
      auto fraction_reclaimed = double(num_lines_reclaimed) /
                                global_space_allocator.full_heap_line_count();
      if (GCLOG_DETAIL > 0) {
        fprintf(gclog, "whole heap GC reclaimed %.1f%%\n", 100.0 * fraction_reclaimed);
      }
      bool need_immediate_reclamation = fraction_reclaimed <= 0.01;
      if (need_immediate_reclamation) {
        gcglobals.next_collection_sticky = false;
      }
      return need_immediate_reclamation;
    }

    // Voluntary collections should never trigger a bigger collection.
    return false;
  }

// }}}

// Invariant: IMMIX_LINES_PER_BLOCK <= 256
// Invariant: marked lines have value 1, unmarked are 0.
uint8_t count_marked_lines_for_frame15(frame15* f15, uint8_t* linemap_for_frame) {
  uint8_t count = 0; // Note: Clang compiles this to straight-line code using vector ops.
  for (int i = 0; i < IMMIX_LINES_PER_BLOCK; ++i) { count += linemap_for_frame[i]; }
  return count;
}

#if 0
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
#endif


class immix_space {
public:
  immix_space(bool is_linked, int lines_at_a_time) : condemned_flag(false) {
    this->is_linked_to_default_subheap = is_linked;
    this->lines_at_a_time = lines_at_a_time;
    approx_lines_allocated_since_last_collection = 0;
    if (GCLOG_DETAIL > 2) { fprintf(gclog, "new immix_space %p\n", this); }
  }

  virtual void dump_stats(FILE* json) {
    return;
  }

  virtual uint64_t prepare_for_collection(bool sticky) {
    if (ENABLE_GCLOG_PREP) { fprintf(gclog, "GCPREP space %p for collection; sticky: %d\n", this, sticky); }
    // Default-linked subheaps cannot be sticky---if they could, then pointers into
    // the default subheap could be missed due to objects in the DLS not getting traced.
    if (sticky && !this->is_linked_to_default_subheap) {
      std::vector<tori**> roots = generational_remset.copy_to_vector();
      fprintf(gclog, "visiting %zd generational remset roots for space %p\n", roots.size(), this);
      // Process generational remset.
      // We must be careful not to process the same root more than once;
      // otherwise, we might evacuate the same object multiple times.
      for (auto slot : roots) {
        //fprintf(gclog, "visiting generational remset root %p in slot %p\n", *slot, slot); fflush(gclog);
        helpers::visit_root((unchecked_ptr*) slot, "generational_remset_root");
      }
      return roots.size();
    } else {
      clear_line_and_object_mark_bits();
      generational_remset.clear();
      return 0;
    }
  }

  void clear_line_and_object_mark_bits() {
      laa.reset_large_array_marks();

      tracking.iter_used_lines_void([this](used_linegroup g) {
          /*
          fprintf(gclog, "GCPREP: clearing linegroup at line %d of (%u)(+%d)\n",
              line_offset_within_f15(g.base),
              frame15_id_of(g.base),
              g.count);
              */
        helpers::clear_line_and_object_mark_bits_for_used_group(g);
      });
      if (MARK_FRAME21S || MARK_FRAME21S_OOL) {
        exit(42); // TODO
      }
  }

  virtual void condemn() { condemned_flag = true; }
  virtual void uncondemn() { condemned_flag = false; }
  virtual bool is_condemned() { return condemned_flag; }

  void clear_current_blocks() {
    if (GCLOG_DETAIL > 3) {
      fprintf(gclog, "clear_current_blocks: small %p (%u), medium %p (%u)\n",
          small_bumper.base,
          frame15_id_of(small_bumper.base),
          medium_bumper.base,
          frame15_id_of(medium_bumper.base)
          );
    }
    // TODO clear mem to avoid conservative pointer leaks
    small_bumper.base = small_bumper.bound;
    medium_bumper.base = medium_bumper.bound;
  }

  virtual void force_gc_for_debugging_purposes() {
    if (GCLOG_DETAIL > 2) { fprintf(gclog, "force_gc_for_debugging_purposes triggering immix gc\n"); }
    immix_common::common_gc(true, false);
  }

  // {{{ Prechecked allocation functions
  template <int N>
  tidy* allocate_cell_prechecked_N(const typemap* map) {
    return helpers::allocate_cell_prechecked(&small_bumper, map, N, gcglobals.current_subheap_hash);
  }

  tidy* allocate_cell_prechecked(const typemap* map) {
    return helpers::allocate_cell_prechecked(&small_bumper, map, map->cell_size, gcglobals.current_subheap_hash);
  }
  // }}}

  // {{{ Allocation, in various flavors & specializations.

  // If this function returns false, we'll trigger a GC and try again.
  // If the function still returns false after GCing, game over!
  template <bool small>
  inline bool try_establish_alloc_precondition(bump_allocator* bumper, int64_t cell_size) {
     if (bumper->size() < cell_size) return try_prep_allocatable_block<small>(bumper, cell_size);
     return true;
  }

  template <bool small>
  bool try_prep_allocatable_block(bump_allocator* bumper, int64_t cell_size) __attribute__((noinline)) {
    // Note the implicit policy embodied below in the preference between
    // using recycled frames, clean used frames, or fresh/new frames.
    //
    // The immix paper uses a policy of expansion -> recycled -> clean used.
    // The order below is different.

    // Round up, not down.
    auto lines_needed = small ? 1 : ((cell_size + (IMMIX_BYTES_PER_LINE - 1)) / IMMIX_BYTES_PER_LINE);
    free_linegroup* g = global_space_allocator.grab_free_linegroup<small>(lines_needed, lines_at_a_time);
    //if (lines_at_a_time < IMMIX_LINES_PER_FRAME15) { lines_at_a_time *= 2; }
    if (!g) return false;

    install_free_group(*bumper, g);
    approx_lines_allocated_since_last_collection += linegroup_size_in_lines(g);
    tracking.add_free_group(g);

    if (ENABLE_GCLOG_PREP) {
      fprintf(gclog, "after gc %d: Prepared allocatable block: %d lines at %p  (%d in %u) for space %p\n",
          gcglobals.num_gcs_triggered,
          linegroup_size_in_lines(g), g,
          line_offset_within_f15(g),
          frame15_id_of(g), this);
      //display_linemap_for_frame15_id(frame15_id_of(g));
      //display_usedmap_for_frame15_id(frame15_id_of(g));
    }

    if (g_in_non_default_subheap) {
      frame15_info_for_frame15_id(frame15_id_of(g))->shared_lines += linegroup_size_in_lines(g);
    }

    if (MEMSET_FREED_MEMORY) {
      auto dist = distance(g, g->bound);
      memset(offset(g, 16), 0xef, dist - 16);
      /*
      if (dist > 16) {
        fprintf(gclog, "INFO: prepared block from %p to %p; size %d\n",
          g, g->bound, dist);
        fflush(gclog);
        
      } else {
        fprintf(gclog, "WARN: prepared too-tiny allocable block from %p to %p; size in bytes is %d; in lines %zd\n",
          g, g->bound,
          dist,
          linegroup_size_in_lines(g));
        fflush(gclog);
        return false;
      }
      */
    }
    return true;
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

  // Precondition: needed_bytes is less than one line.
  bool can_alloc_for_defrag(int64_t needed_bytes) {
    if (small_bumper.size() >= needed_bytes) return true;

    free_linegroup* g = defrag_reserve.try_get_lines_for_defrag();
    if (!g) {
      // Make sure we short-circuit further attempts to defrag.
      gcglobals.evac_threshold = 0;
      return false;
    } else {
      //memset(&linemap[g.startline()], 0, g.size_in_lines());
      helpers::clear_line_and_object_mark_bits_for_used_group(used_group_of_free_group(g));
      tracking.add_free_group(g);
      install_free_group(small_bumper, g);
    }
    return true;
  }

  tidy* defrag_copy_cell(heap_cell* cell, typemap* map, int64_t cell_size) {
    tidy* newbody = helpers::allocate_cell_prechecked(&small_bumper, map, cell_size, space_id_of_header(cell->raw_header()));
    heap_cell* mcell = heap_cell::for_tidy(newbody);
    //fprintf(gclog, "defrag copying cell %p to %p\n", cell, mcell);
    memcpy(mcell, cell, cell_size);
    cell->set_forwarded_body(newbody);

    if (TRACK_NUM_OBJECTS_MARKED) { gcglobals.num_objects_marked_total++; }
    if (TRACK_NUM_OBJECTS_MARKED) { gcglobals.alloc_bytes_marked_total += cell_size; }
    mark_lines_for_slots(newbody, cell_size);
    do_mark_obj_of_size(mcell, cell_size);

    return newbody;
  }

  // Quick benchmark suggests we can use the line-mark map
  // to skip full blocks at a rate of 3 microseconds per 2 MB.
  // Use of SIMD could probably reduce that to ~100 ns per MB.
  //                                         ~~ 100 us per GB

  // Invariant: cell size is less than one line.
  virtual void* allocate_cell(typemap* typeinfo) {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.

    if (try_establish_alloc_precondition<true>(&small_bumper, cell_size)) {
      return allocate_cell_prechecked(typeinfo);
    } else {
      return allocate_cell_slowpath(typeinfo);
    }
  }

  // Invariant: N is less than one line.
  template <int N>
  void* allocate_cell_N(typemap* typeinfo) {
    if (try_establish_alloc_precondition<true>(&small_bumper, N)) {
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

    if (GCLOG_DETAIL > 2) { fprintf(gclog, "allocate_cell_slowpath for size-%zd cell triggering immix gc\n", cell_size); }

    // When we run out of memory, we should collect the whole heap, regardless of
    // what the active subheap happens to be -- the underlying principle being that
    // subheap-enabled code shouldn't needlessly diverge from more traditional
    // runtime's behavior in these cases.
    // An alternative would be to collect the current subheap and then, if that
    // doesn't reclaim "enough", to try the whole heap, but that's a shaky heuristic
    // that can easily lead to nearly-doubled wasted work.
    {
      condemned_set_status_manager tmp(condemned_set_status::default_and_linked);
      if (immix_common::common_gc(false, false)) {
          condemned_set_status_manager tmp(condemned_set_status::whole_heap_condemned);
          immix_common::common_gc(false, true);
      }
    }

    if (!try_establish_alloc_precondition<true>(&small_bumper, cell_size)) {
      helpers::oops_we_died_from_heap_starvation("allocate_cell_slowpath"); return NULL;
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

    //fprintf(gclog, "immix space allocating array, %d elts * %d b = %d bytes\n", n, slot_size, req_bytes);

    if (false && FOSTER_GC_ALLOC_HISTOGRAMS) {
      hdr_record_value(gcglobals.hist_gc_alloc_array, req_bytes);
    }

    if (req_bytes <= IMMIX_LINE_SIZE) {
      return allocate_array_into_bumper<true>(&small_bumper, elt_typeinfo, n, req_bytes, init);
    } else if (req_bytes > (1 << 13)) {
      // The Immix paper, since it built on top of Jikes RVM, uses an 8 KB
      // threshold to distinguish medium-sized allocations from large ones.
      return laa.allocate_array(elt_typeinfo, n, req_bytes, init, this);
    } else {
      // If it's not small and it's not large, it must be medium.
      return allocate_array_into_bumper<false>(&medium_bumper, elt_typeinfo, n, req_bytes, init);
    }
  }

  template <bool small>
  void* allocate_array_into_bumper(bump_allocator* bumper, typemap* elt_typeinfo, int64_t n, int64_t req_bytes, bool init) {
    if (try_establish_alloc_precondition<small>(bumper, req_bytes)) {
      return helpers::allocate_array_prechecked(bumper, elt_typeinfo, n, req_bytes, gcglobals.current_subheap_hash, init);
    } else {
      if (GCLOG_DETAIL > 2) { fprintf(gclog, "allocate_array_into_bumper needing %zd bytes triggering immix gc\n", req_bytes); }
      fprintf(gclog, "bumper size before GC: %zd\n", bumper->size());
      {
        //condemned_set_status_manager tmp(condemned_set_status::default_and_linked);
        condemned_set_status_manager tmp(condemned_set_status::whole_heap_condemned);
        if (immix_common::common_gc(false, true)) {
            condemned_set_status_manager tmp(condemned_set_status::whole_heap_condemned);
            fprintf(gclog, "allocate_array_into_bumper: running emergency GC...\n");
            immix_common::common_gc(false, true);
        }
      }

      fprintf(gclog, "bumper size after GC: %zd\n", bumper->size());
      if (try_establish_alloc_precondition<small>(bumper, req_bytes)) {
        fprintf(gclog, "gc collection freed space for array...\n");
        fflush(gclog);
        return helpers::allocate_array_prechecked(bumper, elt_typeinfo, n, req_bytes, gcglobals.current_subheap_hash, init);
      } else {
        helpers::oops_we_died_from_heap_starvation("allocate_array_into_bumper"); return NULL; }
    }
  }

  // }}}

  virtual tidy* tidy_for(tori* t) { return (tidy*) t; }

  virtual bool is_empty() { return laa.empty() && tracking.num_lines_tracked() == 0; }

  virtual uint64_t approx_size_in_bytes() {
    return (tracking.num_lines_tracked() * IMMIX_BYTES_PER_LINE)
           + laa.approx_size_in_bytes();
  }

  int64_t tally_line_footprint_in_bytes(const std::vector<frame15_id>& all_ids) {
    int64_t rv = 0;
    for (auto fid : all_ids) {
      uint8_t* linemap = linemap_for_frame15_id(fid);
      auto f15 = frame15_for_frame15_id(fid);
      uint8_t count = count_marked_lines_for_frame15(f15, linemap);
      rv += count;

      // This field is read by should_skip_compaction_for_frame15_id...
      auto finfo = frame15_info_for(f15);
      finfo->num_available_lines_at_last_collection = (IMMIX_LINES_PER_BLOCK - count);
    }
    return rv * IMMIX_BYTES_PER_LINE;
  }

  virtual void trim_remset() { helpers::do_trim_remset(incoming_ptr_addrs, this); }
  virtual remset_with_obj_t& get_incoming_ptr_addrs() { return incoming_ptr_addrs; }

  virtual int64_t immix_sweep(clocktimer<false>& phase, int64_t* num_lines_tracked, int64_t* num_groups_tracked) {
    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "space %p tracking %zd lines at start of sweep.\n",
        this, tracking.num_lines_tracked());
    }

    *num_lines_tracked += tracking.num_lines_tracked();
    *num_groups_tracked += tracking.num_groups_tracked();

    // The current block will probably get marked recycled;
    // rather than trying to stop it, we just accept it and reset the base ptr
    // so that the next allocation will trigger a fetch of a new block to use.
    clear_current_blocks();

    int64_t num_lines_reclaimed = 0;

    //// TODO how/when do we sweep arrays from "other" subheaps for full-heap collections?
    laa.sweep_arrays();

    if (this == gcglobals.default_allocator && g_should_compact /*compact_this_subheap*/) {
      clocktimer<false> ct_compact; ct_compact.start();
      // We can use the shared_lines count to determine which frames have
      // live data belonging only to us; these are the *target* candidates
      // for compaction.
      std::set<frame15_id> ours;
      std::vector<used_linegroup> shared_lines;
      tracking.iter_used_lines_taking_ownership([&ours, &shared_lines, this](used_linegroup g) {
          auto fid = frame15_id_of(g.base);
          bool shared = frame15_info_for_frame15_id(fid)->shared_lines > 0;
          if (shared) {
            //uint8_t* linemap = linemap_for_frame15_id(fid);
            //display_used_linegroup_linemap(&g, linemap, this);
            shared_lines.push_back(g);
          } else {
            ours.insert(fid);
          }
      });

      std::vector<frame15_id> unshared(ours.begin(), ours.end());

      // Restore used groups; now, any formerly-shared lines that were slurped up due to
      // becoming unshared by sweeping non-default subheaps will be properly accounted for.
      for (auto fid : unshared) {
        used_linegroup ug = { .base = frame15_for_frame15_id(fid), .count = IMMIX_LINES_PER_FRAME15 };
                                     tracking.note_used_group(ug); }
      for (auto ug : shared_lines) { tracking.note_used_group(ug); }

      for (auto hh : gcglobals.condemned_set.non_default_handles) {
        immix_space* subheap = hh->body;
        ((immix_space*)subheap)->tracking.iter_used_lines_void([&shared_lines](used_linegroup g) {
          //fprintf(gclog, "Adding %d shared lines from non-default subheap.\n", g.count);
          shared_lines.push_back(g);
        });
      }

      // For now we'll not compact out of shared lines, but it would be interesting
      // to see if we could do so easily in the future.
      do_compactify_via_granule_marks(this, unshared, shared_lines);
      fprintf(gclog, "Compaction took %.1f us\n", phase.elapsed_us()); fflush(gclog);
    }

    clocktimer<false> insp_ct; insp_ct.start();
    std::set<frame15_id> compactable_frames;
    tracking.iter_used_lines_taking_ownership([&](used_linegroup g) {
      int reclaimed = this->inspect_lines_postgc(g, compactable_frames);
      num_lines_reclaimed += reclaimed;
    });
    auto inspectFrame15Time_us = insp_ct.elapsed_us();

    for (frame15_id fid : compactable_frames) {
      frame15_info_for_frame15_id(fid)->compactable = false;
    }

    auto deltaPostMarkingCleanup_us = phase.elapsed_us();


    //size_t frame15s_total = tracking.logical_frame15s();
    size_t lines_tracked = tracking.num_lines_tracked();
    size_t lines_allocated = this->approx_lines_allocated_since_last_collection;
    double nursery_ratio = double(lines_allocated) / double(lines_tracked);
    double yield_rate   = double(num_lines_reclaimed) / double(lines_tracked);
    double local_yield  = double(num_lines_reclaimed) / double(lines_allocated);
    double yield_percentage = 100.0 * yield_rate; // usually around 75% - 95%
    double survival_rate = 1.0 - yield_rate; // usually around 0.05 to 0.25

    bool was_sticky = gcglobals.next_collection_sticky;

    if (this == gcglobals.default_allocator) {
      // If we see signs that we're running out of space, discard sticky bits to get more space next time.
      // High survival rates mean both less room to run until the next collection,
      // and also higher cost per collection.
      if (yield_percentage <= gcglobals.yield_percentage_threshold) {
        fprintf(gclog, "Scheduling a non-sticky collection because our yield percentage (%.1f) was below our threshold (%.1f).\n",
            yield_percentage, gcglobals.yield_percentage_threshold);
      }
      else if (yield_rate <= 0.02) {
        fprintf(gclog, "Scheduling a non-sticky collection because our upcoming nursery percentage (%.1f) was below 2%%.\n",
            100.0 * yield_rate);
      }
      gcglobals.next_collection_sticky = (!__foster_globals.disable_sticky)
                                      && !g_should_compact
                                      && (yield_percentage > gcglobals.yield_percentage_threshold)
                                      && (yield_rate > 0.02);
      if (GCLOG_DETAIL > 1) {
        fprintf(gclog, "gcglobals.next_collection_sticky now %d.\n", gcglobals.next_collection_sticky);
      }
    }

    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "Reclaimed (%zd) lines.\n", num_lines_reclaimed);
    }

#if ((GCLOG_DETAIL > 1) && ENABLE_GCLOG_ENDGC)
      { auto s = foster::humanize_s(nursery_ratio * double(lines_tracked * IMMIX_BYTES_PER_LINE), "B");
      fprintf(gclog, "Allocated into %zd lines ('nursery' was %.1f%% = %s of %zd total)\n", lines_allocated, 100.0 * nursery_ratio, s.c_str(), lines_tracked);
      }
      fprintf(gclog, "    global yield rate: %f\n", 100.0 * yield_rate);
      fprintf(gclog, "     local yield rate: %f\n", 100.0 * local_yield);
      //fprintf(gclog, "                                     defrag frame15s left: %zd (before reclaiming clean frames)\n",
      //  defrag_reserve.defrag_frame15s.size());
      
      if (was_sticky) {
        fprintf(gclog, "Reclaimed %.2f%% (%zd) of %zd new lines.\n", 100.0 * local_yield, num_lines_reclaimed, lines_allocated);
      } else {
        fprintf(gclog, "Reclaimed %.2f%% (%zd) of %zd lines.\n", yield_percentage, num_lines_reclaimed, lines_tracked);
      }

#endif

    g_approx_lines_allocated_since_last_collection += approx_lines_allocated_since_last_collection;
    approx_lines_allocated_since_last_collection = 0;
    //tracking.release_clean_frames();
    return num_lines_reclaimed;
  }

  void describe_frame15s_count(const char* start, size_t f15s) {
    auto h = foster::humanize_s(double(f15s) * (1 << 15), "B");
    fprintf(gclog, "%s: %6zd f15s == %s\n", start, f15s, h.c_str());
  }

  // Returns the number of reclaimed lines from the line group.
  int inspect_lines_postgc(used_linegroup& g, std::set<frame15_id>& compactable_frames) {
    // Iterate through the lines, collecting groups of used lines.
    // Free line groups need not be explicitly constructed; they will
    // be reconstructed on demand by the global allocator.
    used_linegroup ug = { .base = g.base, .count = 0 };
    bool was_free = false;
    int num_marked_lines = 0;
    uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(g.base));

    uint8_t* usedmap = line_used_for_frame15_id(frame15_id_of(g.base));
    //fprintf(gclog, "usedmap[%u][100] = %p\n", frame15_id_of(g.base), &usedmap[100]);

    if (GCLOG_PRINT_USED_GROUPS) {
      display_usedmap_for_frame15_id(frame15_id_of(g.base));
    }

    auto finfo = frame15_info_for_frame15_id(frame15_id_of(g.base));
    if (finfo->compactable) {
      compactable_frames.insert(frame15_id_of(g.base));
      if (GCLOG_PRINT_LINE_MARKS) {
        fprintf(gclog, "Leaving used marks alone for compactable frame %u\n", frame15_id_of(g.base));
      }
    } else {
      if (GCLOG_PRINT_LINE_MARKS && GCLOG_DETAIL > 0) {
        fprintf(gclog, "Copying line->used for non-compactable frame %u\n", frame15_id_of(g.base));
      }
      // Selectively copy to used map in preparation for allocation.
      memcpy(&usedmap[g.startline()], &linemap[g.startline()], g.count);

      if (GCLOG_PRINT_USED_GROUPS) {
        display_used_linegroup_linemap(&g, linemap, this);
      }
      //if (GCLOG_PRINT_LINE_MARKS) {
      //  display_usedmap_for_frame15_id(frame15_id_of(g.base));
      //}
    }

    // Invariant: usedmap[x] for x in g is nonzero iff line x is used.

    for (int i = 0; i < g.count; ++i) {
      bool is_marked = line_is_marked(g.startline() + i, usedmap);
      if (is_marked) {
        ++num_marked_lines;

        if (was_free) { // start new used group
          if (ug.count > 0) {
            tracking.note_used_group(ug); // return used group
          }
          ug.base = offset(g.base, i * IMMIX_BYTES_PER_LINE);
          ug.count = 1;
        } else { // continue used group
          ug.count++;
        }
      } else {
        if (GCLOG_DETAIL > 2) {
          fprintf(gclog, "gc %d: INFO: clearing line %d of frame %u @ %p; space=%p\n",
              gcglobals.num_gcs_triggered,
            line_offset_within_f15(offset(g.base, i * IMMIX_BYTES_PER_LINE)),
            frame15_id_of(offset(g.base, i * IMMIX_BYTES_PER_LINE)),
            offset(g.base, i * IMMIX_BYTES_PER_LINE), this);
        }
        if (MEMSET_FREED_MEMORY) {
          memset(offset(g.base, i * IMMIX_BYTES_PER_LINE), 0xdf, IMMIX_BYTES_PER_LINE);
        }
        // Nothing to do!
        #if 0
        if (was_free) { // continue free group
          // fallthrough
        } else { // was used, now free: start new free group
          free_linegroup* new_fg = (free_linegroup*) offset(g->base, i * IMMIX_BYTES_PER_LINE);
          new_fg->next = fg;
          fg = new_fg;
          fg->bound = offset(g->base, i * IMMIX_BYTES_PER_LINE);
        }

        fg->bound += IMMIX_BYTES_PER_LINE;
        #endif
      }
      was_free = !is_marked;
    }

    if (ug.count > 0) {
      tracking.note_used_group(ug); // return used group
    }

    gcglobals.condemned_set.lines_live += num_marked_lines;
    auto num_available_lines = g.count - num_marked_lines;

    if (this != gcglobals.default_allocator) {
      frame15_info_for_frame15_id(frame15_id_of(g.base))->shared_lines -= num_available_lines;
    }

    return num_available_lines;

#if 0
    uint8_t* linemap = linemap_for_frame15_id(fid);
    int num_marked_lines = count_marked_lines_for_frame15(f15, linemap);
    gcglobals.lines_live_at_whole_heap_gc += num_marked_lines;
    
    if (GCLOG_PRINT_LINE_MARKS) {
      fprintf(gclog, "frame %u: ", fid);
      for(int i = 0;i < IMMIX_LINES_PER_BLOCK; ++i) { fprintf(gclog, "%c", (linemap[i] == 0) ? '_' : 'd'); }
      fprintf(gclog, "\n");
    }

    auto num_available_lines = (IMMIX_LINES_PER_BLOCK - num_marked_lines);

    auto finfo = frame15_info_for(f15);
    finfo->num_available_lines_at_last_collection = num_available_lines;

    if (num_marked_lines == 0) {
      tracking.note_clean_frame15(f15);
      return num_available_lines;
    }

    free_linegroup* singlegroup = nullptr;

    // The first line of the next block is off-limits (implicitly marked).
    int cursor = IMMIX_LINES_PER_BLOCK;

    // One or more holes left to process?
    int num_lines_to_process = num_available_lines;
    int num_holes_found = 0;
    while (num_lines_to_process > 0) {
      // At least one available line means this loop will terminate before cursor == 0
      // Precondition: cursor is marked
      while (line_is_marked(cursor - 1, linemap)) --cursor;
      // Postcondition: cursor is marked; cursor - 1 is unmarked.
      int rightmost_unmarked_line = --cursor;

      while (cursor >= 0 && line_is_unmarked(cursor, linemap)) --cursor;
      // Postcondition: line_is_marked(cursor), line_is_unmarked(cursor + 1), cursor >= -1
      int leftmost_unmarked_line = cursor + 1;

      free_linegroup* g = (free_linegroup*) offset(f15,   leftmost_unmarked_line      * IMMIX_BYTES_PER_LINE);
      g->bound =                            offset(f15, (rightmost_unmarked_line + 1) * IMMIX_BYTES_PER_LINE);

      if (MEMSET_FREED_MEMORY) { memset(offset(g, 16), 0xda, distance(g, g->bound) - 16);
        fprintf(gclog, "cleared lines from %p to %p in frame %u\n", g, g->bound, frame15_id_of(g)); }

      int num_lines_in_group = (rightmost_unmarked_line - leftmost_unmarked_line) + 1;
      if (num_lines_in_group == 1) {
        g->next = singlegroup;
        singlegroup = g;
      } else {
        g->next = recycled_lines_medium;
        recycled_lines_medium = g;
      }

      num_lines_to_process -= num_lines_in_group;
      ++num_holes_found;
      //fprintf(gclog, "num lines in group: %d\n", num_lines_in_group); fflush(gclog);
      if (num_lines_in_group <= 0) abort();
    }
    // Postcondition: singlegroup refers to leftmost hole, if any

    if (singlegroup) {
      //if (GCLOG_DETAIL > 0) { fprintf(gclog, "Adding frame %p to recycled list; n marked = %d\n", f15, num_marked_lines); }
      recycled_lines_single.push_back(singlegroup);
    }

    // Previous (non-sticky-mark-bits) versions reset line and object mark bits here,
    // after inspecting each frame. The problem with doing so is a situation like the following:
    //   * The nursery gradually shrinks; eventually, it falls below the threshold, and
    //     the next collection is scheduled to be unsticky.
    //   * The next collection finds all new objects live, and reclaims zero lines, because
    //     mark bits are reset at the *end* of a collection instead of the beginning, so
    //     none of the old data is inspected yet.

    // Increment mark histogram for default subheap.
    if (this == gcglobals.default_allocator) {
      finfo->num_holes_at_last_full_collection = num_holes_found;
      gcglobals.marked_histogram[num_holes_found] += num_marked_lines;
      gcglobals.marked_histogram_frames[num_holes_found] += 1;
      gcglobals.residency_histogram[num_holes_found] += gcglobals.lazy_mapped_frame_liveness[fid];
    }

    // Coarse marks must be reset after all frames have been processed.
    return num_available_lines;
#endif
  }

#if 0
  void copy_frame15_ids(std::vector<frame15_id>& ids) {
    return tracking.copy_frame15_ids(ids);
  }
#endif

  uint32_t hash_for_object_headers() {
    if (this == gcglobals.default_allocator) return 0;
    return fold_64_to_32(uint64_t(this));
  }

  void remember_into(void** slot, void* obj) {
    //fprintf(gclog, "space %p remembering external object %p with slot %p\n", this, obj, slot); fflush(gclog);
    incoming_ptr_addrs.insert((tori**) slot, (tidy*) obj);
  }

  void remember_generational(void* obj, void** slot) {
    generational_remset.insert((tori**)slot);
  }

public:
  bool is_linked_to_default_subheap;

private:
  // These bumpers point into particular frame15s.
  bump_allocator small_bumper;
  bump_allocator medium_bumper;

  large_array_allocator laa;

  immix_space_tracking tracking;

  // Stores the empty spaces that the previous collection
  // identified as being viable candidates for allocation into.
  //std::vector<free_linegroup*> recycled_lines_single;
  //free_linegroup*              recycled_lines_medium;

  // The points-into remembered set; each frame in this set needs to have its
  // card table inspected for pointers that actually point here.
  //std::set<frame15_id> frames_pointing_here;
  remset_with_obj_t incoming_ptr_addrs;
  remset_t generational_remset;

  uint64_t approx_lines_allocated_since_last_collection;
  bool condemned_flag;
  uint8_t lines_at_a_time;
  // immix_space_end
};

bool is_condemned_for_default_and_linked(immix_space* space) {
  if (space->is_linked_to_default_subheap) return true;
  if (space == gcglobals.default_allocator) return true;
  return false;
}



template<typename Allocator>
void condemned_set<Allocator>::prepare_for_collection(bool voluntary,
                                                      bool was_sticky,
                                                      bool emergency,
                                                      uint64_t* numGenRoots,
                                                      uint64_t* numRemSetRoots) {

  switch (this->status) {
    case condemned_set_status::per_frame_condemned: {
      for (auto space : spaces) {
        *numGenRoots += space->prepare_for_collection(was_sticky);
      }
      for (auto space : spaces) {
        *numRemSetRoots += immix_common::process_subheap_remsets(space);
      }
      break;
    }

    case condemned_set_status::default_and_linked:
    case condemned_set_status::whole_heap_condemned: {
      *numGenRoots += gcglobals.default_allocator->prepare_for_collection(was_sticky);
      for (auto handle : gcglobals.default_linked_subheaps) {
        *numGenRoots += handle->body->prepare_for_collection(was_sticky);
      }
      if (emergency) {
        for (auto handle : gcglobals.non_default_linked_subheaps) {
          *numGenRoots += handle->body->prepare_for_collection(was_sticky);
        }
      }

      if (emergency || this->status == condemned_set_status::whole_heap_condemned) {
        // Full-heap collection; no need to process remsets.
        fprintf(gclog, "WARN: not processing remsets for full-heap collection...\n");
      } else {
        *numRemSetRoots += immix_common::process_subheap_remsets(gcglobals.default_allocator);
        for (auto handle : gcglobals.default_linked_subheaps) {
          *numRemSetRoots += immix_common::process_subheap_remsets(handle->body);
        }
      }
      break;
    }
  }
}

template<typename Allocator>
int64_t condemned_set<Allocator>::sweep_condemned(
             clocktimer<false>& phase, bool emergency, bool hadEmptyRootSet,
             int64_t* num_lines_tracked, int64_t* num_groups_tracked) {
  int64_t num_lines_reclaimed = 0;
  //std::vector<heap_handle<immix_space>*> subheap_handles;

  switch (this->status) {
    case condemned_set_status::per_frame_condemned: {
      // Whole-heap collections ignore the condemned set, and single-subheap
      // collections by definition have an implicit condemned set.

      //fprintf(gclog, "Collection type: PerFrameCondemned; emerg %d; # subheaps: %zd\n", emergency, spaces.size() + 1);
      
      for (auto space : spaces) {
        space->trim_remset();
      }

      for (auto space : spaces) {
        space->uncondemn();
      }

      for (auto space : spaces) {
        num_lines_reclaimed += space->immix_sweep(phase, num_lines_tracked, num_groups_tracked);
      }
      spaces.clear();
      //status = condemned_set_status::single_subheap_condemned;
      break;
    }

    case condemned_set_status::default_and_linked:
    case condemned_set_status::whole_heap_condemned: {
      if (GCLOG_DETAIL > 0) {
        fprintf(gclog, "Default linked subheap count: %zd\n", gcglobals.default_linked_subheaps.size());
      }
      gcglobals.condemned_set.non_default_handles.swap(gcglobals.default_linked_subheaps);

      if (emergency) {
        for (auto h : gcglobals.non_default_linked_subheaps) {
          gcglobals.condemned_set.non_default_handles.push_back(h);
        }
        gcglobals.non_default_linked_subheaps.clear();
      }

      if (this->status == condemned_set_status::default_and_linked) {
        fprintf(gclog, "Collection type: DefaultAndLinked; emerg %d; # subheaps: %zd\n", emergency, gcglobals.condemned_set.non_default_handles.size() + 1);
      }

      if (this->status == condemned_set_status::whole_heap_condemned) {
        fprintf(gclog, "Collection type: WholeHeapCondemned; emerg %d; # subheaps: %zd\n", emergency, gcglobals.condemned_set.non_default_handles.size() + 1);
      }

      // Before we clear line marks, remove any stale remset entries.
      // If we don't do this, the following bad thing can happen:
      //   * Object A stored in slot B, so A's space records slot B in its remset.
      //   * Slot B becomes dead.
      //      (keep in mind B's space doesn't know what other spaces have B in their remsets)
      //   * Whole-heap GC (or any other configuration with A and B co-condemned)
      //                   leaves A unmarked, because co-condemned spaces ignore remsets,
      //                   and B was (in this scenario) the last object referring to A.
      //   * So object A and slot B are both dead, but slot B is still recorded in A's remset
      //                                                    (and still points to A).
      //   * Allocation in A puts an arbitrary bit pattern in B's referent
      //     (especially the header/typemap)
      //   * Single-subheap GC of A follows the remset entry for B and goes off the rails.
      //clocktimer<false> remset_trimming;
      //remset_trimming.start();
      gcglobals.default_allocator->trim_remset();
      for (auto handle : gcglobals.condemned_set.non_default_handles) {
        handle->body->trim_remset();
      }
      //fprintf(gclog, "Remset trimming: %.1f us\n", remset_trimming.elapsed_us());

      for (auto handle : gcglobals.condemned_set.non_default_handles) {
        num_lines_reclaimed += handle->body->immix_sweep(phase, num_lines_tracked, num_groups_tracked);
      }
      // Sweep the default space last so that we maximize the number
      // of unshared frames available.
      num_lines_reclaimed += gcglobals.default_allocator->immix_sweep(phase, num_lines_tracked, num_groups_tracked);

      break;
    }
  }

  // Invariant: default_linked_subheaps and non_default_linked_subheaps are both empty.

  // Subheap deallocation effectively only happens for whole-heap collections.
  for (auto handle : gcglobals.condemned_set.non_default_handles) {
    // A space should be deallocated only if it is: condemned, inaccessible (meaning unmarked),
    // and empty. A marked space, empty or not, might be activated in the future.
    // A non-empty unmarked space won't be activated, but it's not dead until the objects
    // within it become inaccessible.
    heap_cell* handle_cell = handle->as_cell();
    auto space = handle->body;
    if (obj_is_condemned_d(handle_cell->body_addr(), gcglobals.condemned_set.status)
            && (!obj_is_marked(handle_cell)) && space->is_empty()) {
      fprintf(gclog, "DELETING SPACE %p because handle cell %p was condemned and unmarked; markable? %d\n",
          space, handle_cell, !non_markable_addr(handle_cell));
      //delete space;
      //free_markable_handle(handle);
    } else {
      if (space->is_linked_to_default_subheap) {
        gcglobals.default_linked_subheaps.push_back(handle);
      } else {
        gcglobals.non_default_linked_subheaps.push_back(handle);
      }
    }
  }
  gcglobals.condemned_set.non_default_handles.clear();

  // Handles (and other unframed allocations) must be unmarked too.
  for (auto c : unframed_and_marked) {
    //fprintf(gclog, "Unmarking unframed object %p\n", c);
    do_unmark_granule(c);
  }
  unframed_and_marked.clear();

  return num_lines_reclaimed;
}

// TODO improve via lookup table of bitmap?
// 1 byte = 8 bits = 8 granules = 128 bytes
//         64 bits            => 1024 bytes = 1 sliver
// frame15 => 256 bytes == 32 slivers
uint64_t byte_offset_in_sliver(void* addr) {
  uintptr_t ga = global_granule_for(addr);
  uintptr_t gb = global_granule_for(sliver_addr(sliver_id_of(addr)));
  uint64_t sum = 0;
  // This loop can execute up to 2048 iterations -- 1024 on average...
  for (auto i = gb; i < ga; ++i) { sum += gcglobals.lazy_mapped_granule_marks[i] & 0x7F; }
  return sum * 16;
}

bool was_zero_mark(uintptr_t g) { return gcglobals.lazy_mapped_granule_marks[g] == 0; }
bool was_continuation_granule_mark(uintptr_t g) { return (gcglobals.lazy_mapped_granule_marks[g] & 0x80) == 0; }

uint64_t sum_sliver_live_bytes(uint64_t sliver) {
  uintptr_t gb = global_granule_for(sliver_addr(sliver));
  uintptr_t gn = global_granule_for(sliver_addr(sliver + 1));
  uint64_t sum = 0;
  //fprintf(gclog, "Sliver %zd (frame %u) granules:\n", sliver, frame15_id_of(sliver_addr(sliver)));
  // Must account for the case in which a medium-sized allocation is split across a sliver boundary.
  // In such a case, we ignore continuation marks at the start of a split frame...
  while (was_continuation_granule_mark(gb) && gb < gn) { ++gb; }
  for (auto i = gb; i < gn; ++i) {
    sum += gcglobals.lazy_mapped_granule_marks[i] & 0x7F;
    //fprintf(gclog, "    %d: %d (sum %zd)\n", i - gb, gcglobals.lazy_mapped_granule_marks[i] & 0x7F, sum);
  }
  // ... and incorporate such marks into the previous frame.
  if (gb < gn) {
    // Max allocation size is 8192 / 16 = 512 granules, which can be split across at most 5 marks.
    while (was_continuation_granule_mark(gn) && !was_zero_mark(gn)) {
      sum += gcglobals.lazy_mapped_granule_marks[gn] & 0x7F; ++gn;
    }
  }
  return sum * 16;
}

uint64_t starting_addr(frame15_id fid) { return uint64_t(realigned_for_allocation(frame15_for_frame15_id(fid))); }

void compute_sliver_offsets(std::vector<frame15_id>& ids) {
  auto curr_id = 0;
  auto prev_sliver = frame15_id_to_sliver( ids[curr_id] );
  gcglobals.lazy_mapped_sliver_offsets[ prev_sliver ] = starting_addr( ids[curr_id] );

  uint64_t summed_bytes = 0;

  // fprintf(gclog, "computing block offsets for logical blocks 1-%zd\n", ids.size());
  for (auto i = 0; i < ids.size(); ++i) {
    auto base_sliver = frame15_id_to_sliver( ids[i] );
    //auto num_slivers = sliver_id_of(offset((void*)0, linegroups[i].count * IMMIX_BYTES_PER_LINE)) + 1;
    auto num_slivers = 32;
    // We process chunks of slivers corresponding to the used lines of a frame/group.
    // The loop effectively starts with sliver 1, since sliver 0 was taken care of above.
    // For sliver 1:
    //     prev_offset would be s0.
    //     delta_bytes would be the size of the live data in *sliver 0* (!).
    //     new_offset would be s0 + delta_bytes.
    //     Eventually new_offset and prev_offset will be in different frames;
    //     when that happens, we retroactively update prev_offset to be the start
    //     of the next frame/group.
    // slivers:  [   s0   |   s1   |   s2   | ...  ]
    //
    // offsets:  [   o0   | 
    for (int sliver = 0; sliver < num_slivers; ++sliver) {
      if (i == 0 && sliver == 0) continue;

      auto prev_offset = gcglobals.lazy_mapped_sliver_offsets[ prev_sliver ];
      auto delta_bytes =                sum_sliver_live_bytes( prev_sliver );
      summed_bytes += delta_bytes;
      auto new_offset = prev_offset + delta_bytes;
      // fprintf(gclog, "prev_offset: %zx; delta: %zu; new offset: %zx; frame_ids %u vs %u\n",
      //     prev_offset, delta_bytes, new_offset,
      //     frame15_id_of((void*) prev_offset),
      //     frame15_id_of((void*) new_offset));
      // Make sure we don't inadvertently create a frame-crossing object during compaction.
      if (frame15_id_of((void*) prev_offset) != frame15_id_of((void*) new_offset)) {
        ++curr_id;
        auto new_prev_offset = starting_addr( ids[curr_id] );
        gcglobals.lazy_mapped_sliver_offsets[ prev_sliver ] = new_prev_offset;
        new_offset = new_prev_offset + delta_bytes;
        //fprintf(gclog, "avoiding frame-crossing offset by jumping ahead to id %zd\n", curr_id);
        //fprintf(gclog, "  prev offset updated to %zx; new offset now %zx\n", new_prev_offset, new_offset);
      }
      prev_sliver = base_sliver + sliver;
      gcglobals.lazy_mapped_sliver_offsets[ prev_sliver ] = new_offset;
    }
  }
  // // Forcibly make sure the last frame doesn't cross a boundary.
  ++curr_id;
  if (curr_id < ids.size()) {
    gcglobals.lazy_mapped_sliver_offsets[ prev_sliver ] = starting_addr( ids[curr_id] );
  } else {
    fprintf(gclog, "WARN: ran out of ids to prevent frame-crossing pointers??\n");
  }
}

heap_cell* compute_forwarding_addr(heap_cell* old) {
  if (!frame15_info_for_frame15_id(frame15_id_of(old))->compactable) { return nullptr; }

  uint64_t base = gcglobals.lazy_mapped_sliver_offsets[ sliver_id_of(old) ];
  uint64_t offset = byte_offset_in_sliver(old);
  //fprintf(gclog, "forwarding addr was base %zx + offset %6zu (%6zx) for ptr %p\n", base, offset, offset, old);
  return (heap_cell*) (base + offset);
}

bool should_skip_compaction_for_frame15_id(frame15_id fid) {
  int byte_residency_in_lines  = int((double(gcglobals.lazy_mapped_frame_liveness[fid]) / 32768.0) * 128.0);
  if (byte_residency_in_lines > 104) return true; // too much data to move (~90% full)
  if (byte_residency_in_lines <  16) return false; // always move small amounts of data to reclaim whole frames.

  // finfo metadata set by earlier tally.
  auto finfo = frame15_info_for_frame15_id(fid);
  int num_marked_lines = IMMIX_LINES_PER_FRAME15 - finfo->num_available_lines_at_last_collection;
  int lines_freed_by_compaction = num_marked_lines - byte_residency_in_lines;
  if (double(lines_freed_by_compaction) < (0.2 * double(byte_residency_in_lines))) {
    return true; // skip compaction if we free up too few lines.
  }
  return false;
}

void immix_worklist_t::process_for_compaction() {
  while (!empty()) {
    unchecked_ptr* root = pop_root();
    tori* body = unchecked_ptr_val(*root);
    heap_cell* obj = heap_cell::for_tidy(reinterpret_cast<tidy*>(body));
    if (heap_cell* fwded = compute_forwarding_addr(obj)) {
      *root = make_unchecked_ptr((tori*) fwded->body_addr());
    }
  }
  initialize();
}

void update_pointer_if_compacted(tidy** slot) {
  tidy* ptr = *slot;
  if (!non_markable_addr(ptr)) {
    if (heap_cell* obj = compute_forwarding_addr(heap_cell::for_tidy(ptr))) {
      *slot = (tidy*) obj->body_addr();
    }
  }
}

void update_pointers_in_remset_of(immix_space* space) {
  auto remset = space_incoming_ptr_addrs(space);
  auto pairs = remset.copy_to_vector();
  fprintf(gclog, "Remset size is %zd for space %p\n", pairs.size(), space);
  for (auto p : pairs) {
    auto val = *p.first;
    if (!non_kosher_addr(val) && is_in_default_subheap((tidy*)val)) {
      update_pointer_if_compacted((tidy**) p.first);
    }
  }
}

void update_slots_in_remset_of(immix_space* space) {
  auto remset = space_incoming_ptr_addrs(space);
  auto pairs = remset.copy_to_vector();
  fprintf(gclog, "Remset size is %zd for space %p\n", pairs.size(), space);
  for (auto p : pairs) {
    tori** old_slot = p.first;
    tidy*  old_obj  = p.second.first;
    if (!non_kosher_addr(old_slot) && is_in_default_subheap(old_obj)) {
      if (heap_cell* cell = compute_forwarding_addr(heap_cell::for_tidy(old_obj))) {
        auto new_obj  = cell->body_addr();
        auto new_slot = (tori**) offset(new_obj, distance(old_obj, old_slot));
        fprintf(gclog, "Updating remset from old slot %p to new slot %p with object %p\n", old_slot, new_slot, new_obj);
        remset.update(old_slot, new_slot, new_obj);
      }
    }
  }
}
void do_compactify_via_granule_marks(immix_space* default_subheap,
                                     std::vector<frame15_id>& all_ids,
                                     std::vector<used_linegroup>& shared_lines) {
  clocktimer<false> ct; ct.start();

  // Compute up-to-date count of available lines for each frame, stored in per-frame metadata.
  auto precise_line_footprint_in_bytes = default_subheap->tally_line_footprint_in_bytes(all_ids);
  fprintf(gclog, "tallying line footprint: %.1f us\n", ct.elapsed_us());
  {
    auto line_footprint = gcglobals.condemned_set.lines_live; // Note: only valid for involuntary collections.
    auto line_footprint_in_bytes = line_footprint * IMMIX_BYTES_PER_LINE;
    auto marked_over_footprint =
          double(g_bytes_marked)/double(precise_line_footprint_in_bytes);
    fprintf(gclog, "   Line footprint@prior GC: %zd\n", line_footprint_in_bytes);
    fprintf(gclog, "   Curr footprint in bytes: %zd\n", precise_line_footprint_in_bytes);
    fprintf(gclog, "   marked/footprint: %.1f\n", marked_over_footprint);
  }

  //gfx::timsort(ids.begin(), ids.end());
  std::sort(all_ids.begin(), all_ids.end());//, sort_linegroup_by_base);
  // We now have a virtualized list of frame ids, in address order.
  fprintf(gclog, "do_compactify: acquiring %zd sorted linegroups: %.1f us\n", all_ids.size(), ct.elapsed_us());

  fprintf(gclog, "remset size for default space: %zd\n", default_subheap->get_incoming_ptr_addrs().size());

  std::vector<frame15_id> selected_ids;
  selected_ids.reserve(all_ids.size());
  for (auto fid : all_ids) {
    bool do_skip = should_skip_compaction_for_frame15_id(fid);
    if (!do_skip) {
      selected_ids.push_back(fid);
    }
    frame15_info_for_frame15_id(fid)->compactable = !do_skip;
  }
  fprintf(gclog, "do_compactify: selected %zd source frames (of %zd)\n", selected_ids.size(), all_ids.size()); fflush(gclog);

  if (selected_ids.size() <= 1) {
    fprintf(gclog, "do_compactify: too few source frames.\n");
    return;
  }

  ct.start();
  compute_sliver_offsets(selected_ids);
  fprintf(gclog, "do_compactify: computing new forwarding addresses: %.1f us\n", ct.elapsed_us()); fflush(gclog);

  int64_t examined_bytes = 0;

  ct.start();
  // Update references and relocate.
  for (auto fid : all_ids) {
    examined_bytes += (IMMIX_BYTES_PER_LINE * IMMIX_LINES_PER_FRAME15);
    auto f15 = frame15_for_frame15_id(fid);
    bool compacting = frame15_info_for_frame15_id(fid)->compactable;

    if (compacting) {
      //uint8_t* linemap = linemap_for_frame15_id(fid);
      //memset(linemap, 0, IMMIX_LINES_PER_FRAME15);
      uint8_t* usedmap = line_used_for_frame15_id(fid);
      memset(usedmap, 0, IMMIX_LINES_PER_FRAME15);
    }

    // TODO also need to update large arrays...
    heap_cell* base = (heap_cell*) realigned_for_allocation(f15);
    uint8_t* marks = &gcglobals.lazy_mapped_granule_marks[global_granule_for(f15)];
    for (int i = 0; i < 2048; ++i) {
      auto mark = marks[i];
      if (mark & 0x80) {
        // object start
        heap_cell* cell = (heap_cell*) offset(base, 16 * i);

        //fprintf(gclog, "examining cell %p with header %zx; fwded? %d\n", cell, cell->raw_header(), cell->is_forwarded()); fflush(gclog);

        heap_array* arr = NULL;
        const typemap* map = NULL;
        int64_t cell_size;
        get_cell_metadata(cell, arr, map, cell_size);

#if 0
        if (cell_size <= 0 || cell_size > 8192) {
          fprintf(gclog, "WARN: corrupted cell size %zd for %p! header %zx, fwded? %d; map %p\n",
              cell_size, cell, cell->raw_header(), cell->is_forwarded(), map);
          fflush(gclog);
        }
#endif

        for_each_child_slot_with(cell, arr, map, cell_size, [](intr* slot) {
          update_pointer_if_compacted((tidy**) slot);
        });

        if (!compacting) {
          // skip!
        } else if (heap_cell* dest = compute_forwarding_addr(cell)) {
          /*
          fprintf(gclog, "sliding cell of size %zd (mark %x) from %p [sliver %zd] (header %zx) to new dest %p (line %d @ %u)\n",
                    cell_size, mark & 0x7F, cell, sliver_id_of(cell),
                    cell->raw_header(), dest, line_offset_within_f15(dest), frame15_id_of(dest));
          fflush(gclog);
          */
                    
          memmove(dest, cell, cell_size);
          //mark_lines_for_slots(dest, cell_size);
          // Note: modify used map, not line map, because compaction can use lines that were just reclaimed from
          // other subheaps and thus would not get copied from the line map.
          // Non-compactable frames copy information from line map to used map;
          // compactable frames do the inverse (because the line map determines what gets cleared).
          mark_slots_used(dest, cell_size);

          // Can't reset granule mark for old cell because it would interfere with byte_offset_in_sliver().
          //do_mark_obj_of_size(dest, cell_size);
          gcglobals.lazy_mapped_frame_liveness[frame15_id_of(cell)] -= uint16_t(cell_size);
          gcglobals.lazy_mapped_frame_liveness[frame15_id_of(dest)] += uint16_t(cell_size);
        }
      }
    }
  }

  // TODO figure out interaction between compaction and subheaps.
  // Maybe related to root trimming? But probably not...

  for (auto ug : shared_lines) {
    examined_bytes += (IMMIX_BYTES_PER_LINE * ug.count);
    //fprintf(gclog, "updating run of %d shared lines\n", ug.count);
    heap_cell* base = (heap_cell*) realigned_for_allocation(ug.base);
    uint8_t* marks = &gcglobals.lazy_mapped_granule_marks[global_granule_for(ug.base)];
    auto num_granules = ug.count * IMMIX_GRANULES_PER_LINE;
    for (int i = 0; i < num_granules; ++i) {
      auto mark = marks[i];
      if (mark & 0x80) {
        // object start
        heap_cell* cell = (heap_cell*) offset(base, 16 * i);

        //fprintf(gclog, "examining cell %p with header %zx; fwded? %d\n", cell, cell->raw_header(), cell->is_forwarded()); fflush(gclog);

        heap_array* arr = NULL;
        const typemap* map = NULL;
        int64_t cell_size;
        get_cell_metadata(cell, arr, map, cell_size);

        for_each_child_slot_with(cell, arr, map, cell_size, [](intr* slot) {
          update_pointer_if_compacted((tidy**) slot);
        });
      }
    }
  }
  fprintf(gclog, "do_compactify: updating heap references: %.1f us\n", ct.elapsed_us());
  fprintf(gclog, "do_compactify: examined bytes: %zd\n", examined_bytes);

  // The remset for the default space D refers to slots in other subheaps
  // that (may) contain pointers into D. Such *pointers* need to be updated to
  // account for relocation of objects in D.
  update_pointers_in_remset_of(default_subheap);

  // The remsets for other spaces, S, may refer to slots in D containing
  // pointers into S. These *slots* must likewise be updated.
  for (auto handle : gcglobals.condemned_set.non_default_handles) {
    fprintf(gclog, "Updating slots in remset of space %p\n", handle->body);
    update_slots_in_remset_of(handle->body);
  }

  ct.start();

  fprintf(gclog, "Collecting roots from stack in do_compactify().\n");
  collect_roots_from_stack(__builtin_frame_address(0));
  fprintf(gclog, "Done Collecting roots from stack in do_compactify().\n");
  immix_worklist.process_for_compaction();

  fprintf(gclog, "do_compactify: updating stack references: %.1f us\n", ct.elapsed_us());

  {
    // Current coro slot must be updated manually.
    // TODO probably a better solution is to just bite the bullet and adopt per-object pinning...
    foster_bare_coro** coro_slot = __foster_get_current_coro_slot();
    foster_bare_coro*  coro = *coro_slot;
    heap_cell* coro_cell = heap_cell::for_tidy((tidy*) coro);
    if (auto fwded = compute_forwarding_addr(coro_cell)) {
      *coro_slot = (foster_bare_coro*) fwded->body_addr();
    }
  }

  /*
  for (auto fid : all_ids) {
    //auto f15 = frame15_for_frame15_id(fid);
    if (GCLOG_PRINT_LINE_MARKS) { display_linemap_for_frame15_id(fid); }
    //clear_object_mark_bits_for_frame15(f15);
    frame15_info_for_frame15_id(fid)->compactable = false;
  }
  */

  gcglobals.next_collection_sticky = false;
}

void process_worklist() {
  if (GCLOG_DETAIL > 0) { fprintf(gclog, "Before processing, immix worklist contained %zd roots\n", immix_worklist.size()); }
  switch (gcglobals.condemned_set.status) {
    case condemned_set_status::per_frame_condemned:
      immix_worklist.process<condemned_set_status::per_frame_condemned>(); break;
    case condemned_set_status::whole_heap_condemned:
      immix_worklist.process<condemned_set_status::whole_heap_condemned>(); break;
    case condemned_set_status::default_and_linked:
      immix_worklist.process<condemned_set_status::default_and_linked>(); break;
  }
}

template <condemned_set_status condemned_status>
void immix_worklist_t::process() {
  while (true) {
    unchecked_ptr* root;
#if USE_FIFO_SIZE > 0
    if (!empty()) {
      root = pop_root();
      __builtin_prefetch(*(void**)root);

      unchecked_ptr* hopefully_prefetched_by_now = (unchecked_ptr*) fifo.pull_and_push((void*) root);
      root = hopefully_prefetched_by_now;
      if (!root) { continue; }
    } else {
      root = (unchecked_ptr*) fifo.pull_and_push(nullptr);
      if (!root) {
        root = (unchecked_ptr*) fifo.pull_and_push(nullptr);
      }
      if (!root) { break; }
    }
      /*
      if (fifo.full()) {
        unchecked_ptr* hopefully_prefetched_by_now = (unchecked_ptr*) fifo.pull_and_push((void*) root);
        root = hopefully_prefetched_by_now;
      } else {
        fifo.push((void*) root);
        continue;
      }
    } else {
      if (fifo.empty()) { break; }
      root = (unchecked_ptr*) fifo.pull();
    }
    */
#else
    if (empty()) {
      //fprintf(gclog, "gc %d: marking stack empty\n", gcglobals.num_gcs_triggered);
      break;
    }
    root = pop_root();
#endif

    tori* body = unchecked_ptr_val(*root); // TODO drop the assumption that body is a tidy pointer.
    heap_cell* obj = heap_cell::for_tidy(reinterpret_cast<tidy*>(body));

    if (0) {
      fprintf(gclog, "gc %d: root %p contains object %p (line %d of frame %u)\n", // with header %zx\n",
          gcglobals.num_gcs_triggered,
          root, obj,
          line_offset_within_f15(root),
                  frame15_id_of(root)
          //, obj->raw_header()
          );
    }

    if ( (condemned_status == condemned_set_status::per_frame_condemned
          && !per_frame_cell_is_condemned(obj)) )
    {
        // When collecting a subset of the heap, we only look at condemned objects,
        // and ignore objects stored in non-condemned regions.
        // The remembered set is guaranteed to contain all incoming pointers
        // from non-condemned regions.
        if (GCLOG_DETAIL > 3) {
          auto f15id = frame15_id_of((void*) obj);
          fprintf(gclog, "WARN: immix_trace() ignoring non-condemned cell %p in line %d of (%u)\n",
            obj, line_offset_within_f15(obj), f15id); }
        continue;
    }

    if (obj->is_forwarded()) {
      // fprintf(gclog, "worklist.process: root=%p, body = %p, obj = %p, header=%zx\n", root, body, obj, obj->raw_header()); fflush(gclog);
      *root = make_unchecked_ptr((tori*) obj->get_forwarded_body());
    } else if (obj_is_marked(obj)) {
#if DEBUG_VERIFY_MARK_BITS
      if (g_marked_this_cycle.count(obj) == 0) {
        fprintf(gclog, "WARN: mark bits not properly cleared for obj %p\n", obj);
      }
#endif
      // Skip marked objects.
      //fprintf(gclog, "gc %d: skipping marked object cell %p\n", gcglobals.num_gcs_triggered, obj);
    } else {
#if DEBUG_VERIFY_MARK_BITS
      g_marked_this_cycle.insert(obj);
#endif
      immix_common::immix_trace<condemned_status>(root, obj);
    }
  }
  initialize();
}


template <condemned_set_status condemned_portion>
bool should_opportunistically_evacuate(heap_cell* obj) {
  if (condemned_portion == condemned_set_status::per_frame_condemned) return false;
  if (gcglobals.evac_threshold == 0) return false;
  if (!is_in_default_subheap((tidy*)obj)) return false;

  auto f15info = frame15_info_for((void*) obj);
  bool want_to_opportunistically_evacuate =
             f15info->num_holes_at_last_full_collection >= gcglobals.evac_threshold
          && f15info->frame_classification == frame15kind::immix_smallmedium;

  if (want_to_opportunistically_evacuate) {
    heap_array* arr; const typemap* map; int64_t cell_size;
    get_cell_metadata(obj, arr, map, cell_size);
    if (cell_size < IMMIX_BYTES_PER_LINE) {
      bool can = ((immix_space*)gcglobals.default_allocator)->can_alloc_for_defrag(cell_size);
      if (!can) { fprintf(gclog, "unable to continue opportunistic evacuation...\n"); }
      return can;
    }
  }
  return false;
}

bool space_is_condemned(immix_space* space) {
  return space->is_condemned();
}

remset_with_obj_t& space_incoming_ptr_addrs(immix_space* space) {
  return space->get_incoming_ptr_addrs();
}

void* immix_common::evac_with_map_and_arr(heap_cell* cell, const typemap* map,
                            heap_array* arr, int64_t cell_size,
                            immix_space* tospace) {
  // We have separate functions for allocating arrays vs non-array cells in order
  // to initialize the number-of-elements field. But here, the field is already
  // there; all we need to do is copy the whole blob and trace is as usual.
  tidy* newbody = tospace->defrag_copy_cell(cell, (typemap*)map, cell_size);
  heap_cell* newcell = heap_cell::for_tidy(newbody);
  heap_array* newarr = arr ? heap_array::from_heap_cell(newcell) : nullptr;
  for_each_child_slot_with(newcell, newarr, map, cell_size, [](intr* slot) {
      if (!non_markable_addr(* (void**)slot)) {
        immix_worklist.add_root((unchecked_ptr*) slot);
      }
  });
  return newbody;
}

#include "foster_gc_backtrace_x86-inl.h"

// {{{ Walks the call stack and inserts roots into immix_worklist.
void collect_roots_from_stack(void* start_frame) {
  enum { MAX_NUM_RET_ADDRS = 4024 };
  // Garbage collection requires 16+ KB of stack space due to these arrays.
  ret_addr  retaddrs[MAX_NUM_RET_ADDRS];
  frameinfo frames[MAX_NUM_RET_ADDRS];

  // Collect frame pointers and return addresses
  // for the current call stack.
  int nFrames = foster_backtrace((frameinfo*) start_frame, frames, MAX_NUM_RET_ADDRS);
  //fprintf(gclog, "Number of frames in backtrace: %d\n", nFrames);
  if (nFrames > 500) {
    gcglobals.num_big_stackwalks += 1;
  }
  if (nFrames == MAX_NUM_RET_ADDRS) {
    fprintf(gclog, "ERROR: backtrace is probably incomplete due to oversized stack! (%d frames)\n", nFrames); fflush(gclog);
    exit(2);
  }
  if (FOSTER_GC_TIME_HISTOGRAMS) {
    hdr_record_value(gcglobals.hist_gc_stackscan_frames, int64_t(nFrames));
  }

  const bool SANITY_CHECK_CUSTOM_BACKTRACE = false;
  if (SANITY_CHECK_CUSTOM_BACKTRACE) {
    // backtrace() fails when called from a coroutine's stack...
    int numRetAddrs = backtrace((void**)&retaddrs, MAX_NUM_RET_ADDRS);
    if (GCLOG_DETAIL > 2) {
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
        exit(11);
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
    frameptr sp = (i == 0) ? fp : offset(frames[i - 1].frameptr, 2 * sizeof(void*));

    const stackmap::PointCluster* pc = gcglobals.clusterForAddress[safePointAddr];
    if (!pc) {
      if (GCLOG_DETAIL > 3) {
        fprintf(gclog, "no point cluster for address %p with frame ptr%p\n", safePointAddr, fp);
      }
      continue;
    }

    if (GCLOG_DETAIL > 3) {
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
      void*  rootaddr = (off <= 0) ? offset(fp, off)
                                   : offset(sp, off);
      helpers::visit_root((unchecked_ptr*) rootaddr, (const char*) m);
/*
      if (!non_markable_addr(*(void**)rootaddr)) {
        immix_worklist.add_root((unchecked_ptr*) rootaddr);
      }
      */
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
  } else if (GCLOG_DETAIL > 2) {
    coro_print(coro);
  }
}

// Declared in libfoster_coro.cpp
extern "C"
void foster_coro_ensure_self_reference(foster_bare_coro* coro);

void collect_roots_from_stack_of_coro(foster_bare_coro* coro) {
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

  if (GCLOG_DETAIL > 1) {
    fprintf(gclog, "========= scanning coro (%p, fn=%p, %s) stack from %p\n",
        coro, foster::runtime::coro_fn(coro), coro_status_name(coro), frameptr);
  }

  collect_roots_from_stack(frameptr);

  if (GCLOG_DETAIL > 1) {
    fprintf(gclog, "========= scanned coro stack from %p\n", frameptr);
    fflush(gclog);
  }
}

//////////////////////////////////////////////////////////////}}}

// {{{ GC startup & shutdown
void register_stackmaps(ClusterMap&); // see foster_gc_stackmaps.cpp

int address_space_prefix_size_log() {
  if (sizeof(void*) == 4) { return 32; }
  if (sizeof(void*) == 8) { return 47; }
  exit(3); return 0;
}

template<typename T>
T* allocate_lazily_zero_mapped(size_t num_elts) {
  size_t len = sizeof(T) * num_elts;
#if OS_MACOSX
  // On macOS, multi-page malloc() will lazily zero-initialize:
  // https://developer.apple.com/library/content/documentation/Performance/Conceptual/ManagingMemory/Articles/MemoryAlloc.html
  return (T*) malloc(len);
#elif OS_LINUX
  bool commit = true; // On Linux, this means (to pages_jemalloc) "map read/write"
  return (T*) pages_map(NULL, len, 16, &commit);
#else
#error Need to determine how to lazy allocate pages on this platform
#endif
}

size_t lazy_mapped_frame15_condemned_size() { return (size_t(1) << (address_space_prefix_size_log() - 15)); }
size_t lazy_mapped_granule_marks_size() {     return (size_t(1) <<  address_space_prefix_size_log()     ) / (16 * 1); } 

extern "C" void* opaquely_ptr(void*);

void initialize(void* stack_highest_addr) {
  gcglobals.init_start.start();
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  pages_boot();

  gcglobals.lazy_mapped_markable_handles        = (void**) allocate_lazily_zero_mapped<heap_handle<immix_space> >(1 << 20);
  // First entry reserved for free list.
  (*gcglobals.lazy_mapped_markable_handles) = offset(gcglobals.lazy_mapped_markable_handles, sizeof(heap_handle<immix_space>));

  gcglobals.lazy_mapped_frame15info             = allocate_lazily_zero_mapped<frame15info>(     size_t(1) << (address_space_prefix_size_log() - 15));
  gcglobals.lazy_mapped_coarse_marks            = allocate_lazily_zero_mapped<uint8_t>(         size_t(1) << (address_space_prefix_size_log() - COARSE_MARK_LOG));
  //gcglobals.lazy_mapped_coarse_condemned        = allocate_lazily_zero_mapped<condemned_status>(size_t(1) << (address_space_prefix_size_log() - COARSE_MARK_LOG));
  //gcglobals.lazy_mapped_frame15info_associated  = allocate_lazily_zero_mapped<void*>(      size_t(1) << (address_space_prefix_size_log() - 15));
  //
  gcglobals.lazy_mapped_granule_marks           = allocate_lazily_zero_mapped<uint8_t>(lazy_mapped_granule_marks_size()); // byte marks
  gcglobals.lazy_mapped_frame_liveness          = allocate_lazily_zero_mapped<uint16_t>(     size_t(1) << (address_space_prefix_size_log() - 15));
  gcglobals.lazy_mapped_sliver_offsets          = allocate_lazily_zero_mapped<uint64_t>(     size_t(1) << (address_space_prefix_size_log() - IMMIX_SLIVER_SIZE_LOG));
  gcglobals.lazy_mapped_line_stamps             = allocate_lazily_zero_mapped<uint16_t>(     size_t(1) << (address_space_prefix_size_log() - IMMIX_LINE_SIZE_LOG));
  gcglobals.lazy_mapped_line_marks              = allocate_lazily_zero_mapped<uint8_t>(      size_t(1) << (address_space_prefix_size_log() - IMMIX_LINE_SIZE_LOG));
  gcglobals.lazy_mapped_line_used               = allocate_lazily_zero_mapped<uint8_t>(      size_t(1) << (address_space_prefix_size_log() - IMMIX_LINE_SIZE_LOG));


  global_space_allocator.set_heap_size(gSEMISPACE_SIZE());
  gcglobals.allocator = new immix_space(true, 128);
  gcglobals.default_allocator = gcglobals.allocator;
  gcglobals.allocator_handle = nullptr;
  gcglobals.current_subheap_hash = gcglobals.allocator->hash_for_object_headers();

  gcglobals.condemned_set.status = condemned_set_status::default_and_linked;

  gcglobals.had_problems = false;
  gcglobals.logall = false;

  register_stackmaps(gcglobals.clusterForAddress);

  gcglobals.gc_time_us = 0.0;
  gcglobals.num_gcs_triggered = 0;
  gcglobals.num_gcs_triggered_involuntarily = 0;
  gcglobals.num_gcs_triggered_nurseryonly = 0;
  gcglobals.num_big_stackwalks = 0;
  gcglobals.subheap_ticks = 0.0;
  gcglobals.involuntary_ticks = 0.0;
  gcglobals.num_allocations = 0;
  gcglobals.num_alloc_bytes = 0;
  gcglobals.num_alloc_bytes_in_subheaps = 0;
  gcglobals.num_subheaps_created = 0;
  gcglobals.num_subheap_activations = 0;
  gcglobals.write_barrier_phase0_hits = 0;
  gcglobals.write_barrier_phase0b_hits = 0;
  gcglobals.write_barrier_phase1_hits = 0;
  gcglobals.write_barrier_phase1g_hits = 0;
  gcglobals.num_objects_marked_total = 0;
  gcglobals.alloc_bytes_marked_total = 0;
  gcglobals.max_bytes_live_at_whole_heap_gc = 0;
  gcglobals.num_closure_calls = 0;
  gcglobals.evac_candidates_found = 0;
  gcglobals.evac_threshold = 0;
  gcglobals.next_collection_sticky = !__foster_globals.disable_sticky;
  gcglobals.yield_percentage_threshold = __foster_globals.sticky_base_threshold;
  gcglobals.last_full_gc_compaction_headroom_estimate = 0.0;
  gcglobals.last_full_gc_fragmentation_percentage = 0.0;

  hdr_init(1, 6000000, 2, &gcglobals.hist_gc_stackscan_frames);
  hdr_init(1, 6000000, 2, &gcglobals.hist_gc_stackscan_roots);
  hdr_init(1, 600000000, 3, &gcglobals.hist_gc_pause_micros); // 600M us => 600 seconds => 10 minutes
  hdr_init(1, 600000000, 2, &gcglobals.hist_gc_pause_ticks);
  hdr_init(1, 600000000, 2, &gcglobals.hist_gc_rootscan_ticks); // 600M ticks ~> 10ms (@ 6 GHz...)
  hdr_init(1, 1000000000000, 3, &gcglobals.hist_gc_alloc_array); // 1 TB
  hdr_init(129, 1000000, 3, &gcglobals.hist_gc_alloc_large); // 1 MB
  memset(gcglobals.enum_gc_alloc_small, 0, sizeof(gcglobals.enum_gc_alloc_small));

  reset_marked_histogram();

  if (foster__typeMapList[0]) {
    // We've gotta go out of our way to prevent Clang from trying to statically
    // unroll this loop over constant data into a multi-gigabyte select tree.
    void** tML = (void**) opaquely_ptr(&foster__typeMapList[0]);
    void* min_addr_typemap = tML;
    void* max_addr_typemap = tML;
    // Determine the bounds of the typemap
    for (void** typemap = &tML[1]; *typemap; ++typemap) {
      min_addr_typemap = std::min(min_addr_typemap, *typemap);
      max_addr_typemap = std::max(max_addr_typemap, *typemap);
    }
    gcglobals.typemap_memory.base = min_addr_typemap;
    gcglobals.typemap_memory.bound = offset(max_addr_typemap, 8);
  } else {
    fprintf(gclog, "skipping type map list registration\n");
  }
}


void gclog_time(const char* msg, double secs, FILE* json) {
  auto ss = fmt_secs(secs);
  fprintf(gclog, "%s: %s\n", msg, ss.c_str());
  if (json) {
  fprintf(json, "'%s_s' : %f\n", msg, secs);
  fprintf(json, "'%s_ms': %f\n", msg, secs * 1000.0);
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


static const char HDR_FOSTER_FOOTER[] =
    "#[Mean    = %12.3f, StdDeviation   = %12.3f]\n"
    "#[Max     = %12.3f, Total count    = %12" PRIu64 "]\n";

int64_t foster_hdr_percentiles_bucket_max(struct hdr_histogram* h, int32_t tphd) {
  struct hdr_iter iter;
  hdr_iter_percentile_init(&iter, h, tphd);
  int64_t prev_total = 0;
  int64_t bucket_max = -1;

  while (hdr_iter_next(&iter))
  {
      double  value               = iter.highest_equivalent_value;
      int64_t total_count         = iter.cumulative_count;
      int64_t bucket_count        = total_count - prev_total;

      if (bucket_count == 0) continue;
      bucket_max = (std::max)(bucket_max, bucket_count);
      prev_total = total_count;
  }
  return bucket_max;
}

int foster_hdr_percentiles_print(
        struct hdr_histogram* h, FILE* stream, int32_t ticks_per_half_distance)
{
    double value_scale = 1.0;
    const char* line_format = "%12" PRId64 "..+%-8" PRId64 " %12f %12" PRId64 " %12" PRId64 " %12.2f";
    int rc = 0;
    int64_t value_hi = 0;
    int64_t prev_total = 0;
    int64_t prev_value_lo = 0;
    int64_t bucket_max = foster_hdr_percentiles_bucket_max(h, ticks_per_half_distance);
    int64_t bucket_count = 0;

    struct hdr_iter iter;
    hdr_iter_percentile_init(&iter, h, ticks_per_half_distance);

    struct hdr_iter_percentiles * percentiles = &iter.specifics.percentiles;

    if (h->total_count == 0) {
      fprintf(stream, "\t(no samples recorded)\n");
      return 0;
    }

    if (fprintf(
            stream, "%22s %12s %12s %12s %12s     (chart, linear scale)\n\n",
            "Range", "Percentile", "BucketCount", "TotalCount", "1/(1-Percentile)") < 0)
    {
        rc = EIO;
        goto cleanup;
    }

    while (hdr_iter_next(&iter))
    {
                value_hi            = iter.highest_equivalent_value;
        int64_t value_lo            = iter.lowest_equivalent_value;
        double  percentile          = percentiles->percentile / 100.0;
        int64_t total_count         = iter.cumulative_count;
        double  inverted_percentile = (1.0 / (1.0 - percentile));
        bucket_count               += total_count - prev_total;

        int chart_bar_size = int(60.0 * double(bucket_count)/double(bucket_max));
        if (chart_bar_size == 0) continue;

        if (fprintf(
                stream, line_format, prev_value_lo, value_hi - prev_value_lo, percentile,
                  total_count - prev_total, total_count, inverted_percentile) < 0)
        {
            rc = EIO;
            goto cleanup;
        }

        if (fprintf(stream, "    ") < 0) { rc = EIO; goto cleanup; }
        for (int i = 0; i < chart_bar_size; ++i) {
          if (fprintf(stream, "-") < 0) { rc = EIO; goto cleanup; }
        }
        if (chart_bar_size == 0) {
          if (fprintf(stream, ".") < 0) { rc = EIO; goto cleanup; }
        }
        if (fprintf(stream, "\n") < 0) { rc = EIO; goto cleanup; }

        prev_total = total_count;
        prev_value_lo = value_hi;
        bucket_count = 0;
    }

    {
      double mean   = hdr_mean(h)   / value_scale;
      double stddev = hdr_stddev(h) / value_scale;
      double max    = hdr_max(h)    / value_scale;
      
      if (fprintf(stream, HDR_FOSTER_FOOTER,  mean, stddev, max, h->total_count) < 0)
      {
          rc = EIO;
          goto cleanup;
      }
      fprintf(stream, "             (keep in mind that standard deviations may not mean\n"
                      "              what you think for non-normal distributions)\n");
    }

    cleanup:
    return rc;
}

FILE* print_timing_stats() {
  auto total_elapsed = gcglobals.init_start.elapsed_s();
  auto gc_elapsed = gcglobals.gc_time_us / 1e6;
  auto mut_elapsed = total_elapsed - gc_elapsed;

  fprintf(gclog, "'F21_Marking': %d\n", MARK_FRAME21S);
  fprintf(gclog, "'F21_Marking_OOL': %d\n", MARK_FRAME21S_OOL);
  fprintf(gclog, "'F21_UnsafeAssumedClean': %s\n", UNSAFE_ASSUME_F21_UNMARKED ? "true" : "false");

  FILE* json = __foster_globals.dump_json_stats_path.empty()
                ? NULL
                : fopen(__foster_globals.dump_json_stats_path.c_str(), "w");
  if (json) fprintf(json, "{\n");

  if (!json && FOSTER_GC_ALLOC_HISTOGRAMS) {
    fprintf(gclog, "hist_gc_alloc_array:\n");
    foster_hdr_percentiles_print(gcglobals.hist_gc_alloc_array, gclog, 4);

    fprintf(gclog, "hist_gc_alloc_large:\n");
    foster_hdr_percentiles_print(gcglobals.hist_gc_alloc_large, gclog, 4);

    for (int i = 0; i <= 128; ++i) {
      int64_t nallocs = gcglobals.enum_gc_alloc_small[i];
      if (nallocs > 0) {
        fprintf(gclog, "# allocs @ size %d bytes: %" PRId64 "\n", i, nallocs);
      }
    }
  }

  if (!json && FOSTER_GC_TIME_HISTOGRAMS) {
    if (ENABLE_GC_TIMING_TICKS) {
      fprintf(gclog, "hist_gc_rootscan_ticks:\n");
      foster_hdr_percentiles_print(gcglobals.hist_gc_rootscan_ticks, gclog, 4);
    }

    if (ENABLE_GC_TIMING_TICKS) {
      fprintf(gclog, "gc_pause_ticks:\n");
      foster_hdr_percentiles_print(gcglobals.hist_gc_pause_ticks, gclog, 4);
    }

    if (ENABLE_GC_TIMING) {
      fprintf(gclog, "hist_gc_pause_micros:\n");
      foster_hdr_percentiles_print(gcglobals.hist_gc_pause_micros, gclog, 4);
    }

    fprintf(gclog, "gc_stackscan_frames:\n");
    foster_hdr_percentiles_print(gcglobals.hist_gc_stackscan_frames, gclog, 4);

    fprintf(gclog, "gc_stackscan_roots:\n");
    foster_hdr_percentiles_print(gcglobals.hist_gc_stackscan_roots, gclog, 4);
  }

  if (!json && FOSTER_GC_EFFIC_HISTOGRAMS) {
    fprintf(gclog, "gc_pause_ticks:\n");
    foster_hdr_percentiles_print(gcglobals.hist_gc_pause_ticks, gclog, 4);
  }

  fflush(gclog);

  dump_alloc_site_stats(gclog);

  fprintf(gclog, "'Num_Big_Stackwalks': %d\n", gcglobals.num_big_stackwalks);
  fprintf(gclog, "'Num_GCs_Triggered': %d\n", gcglobals.num_gcs_triggered);
  fprintf(gclog, "'Num_GCs_Involuntary': %d\n", gcglobals.num_gcs_triggered_involuntarily);
  fprintf(gclog, "'Num_GCs_NurseryOnly': %d\n", gcglobals.num_gcs_triggered_nurseryonly);
  {
    auto s = foster::humanize_s(double(gcglobals.num_subheaps_created), "");
    fprintf(gclog, "'Num_Subheaps_Created': %s\n", s.c_str());
  }
  {
    auto s = foster::humanize_s(double(gcglobals.num_subheap_activations), "");
    fprintf(gclog, "'Num_Subheap_Activations': %s\n", s.c_str());
  }
  if (TRACK_NUM_ALLOCATIONS) {
    auto s = foster::humanize_s(double(gcglobals.num_allocations), "");
    fprintf(gclog, "'Num_Allocations': %s\n", s.c_str());
  }
  if (TRACK_NUM_ALLOC_BYTES) {
    auto s = foster::humanize_s(double(gcglobals.num_alloc_bytes), "B");
    fprintf(gclog, "'Num_Alloc_Bytes': %s\n", s.c_str());
  }
  if (TRACK_NUM_ALLOC_BYTES) {
    auto s = foster::humanize_s(double(gcglobals.num_alloc_bytes_in_subheaps), "B");
    fprintf(gclog, "'Num_Alloc_Bytes_In_Subheaps': %s\n", s.c_str());
  }
  if (TRACK_NUM_OBJECTS_MARKED && gcglobals.max_bytes_live_at_whole_heap_gc > 0) {
    auto s = foster::humanize_s(double(gcglobals.max_bytes_live_at_whole_heap_gc), "B");
    fprintf(gclog, "'Max_LiveAtFullGC_Bytes': %s\n", s.c_str());
  }
  if (TRACK_NUM_OBJECTS_MARKED && TRACK_NUM_ALLOCATIONS) {
    fprintf(gclog, "'MarkCons_Obj_div_Obj': %e\n",
        double(gcglobals.num_objects_marked_total) / double(gcglobals.num_allocations));
  }
  if (TRACK_NUM_OBJECTS_MARKED && TRACK_NUM_ALLOCATIONS) {
    fprintf(gclog, "'MarkCons_Obj_div_Bytes': %e\n",
        double(gcglobals.num_objects_marked_total) / double(gcglobals.num_alloc_bytes));
  }
  if (TRACK_NUM_OBJECTS_MARKED) {
    fprintf(gclog, "'MarkCons_Bytes_div_Bytes': %e\n",
        double(gcglobals.alloc_bytes_marked_total) / double(gcglobals.num_alloc_bytes));
  }
  if (TRACK_WRITE_BARRIER_COUNTS) {
    fprintf(gclog, "'Num_Write_Barriers_Subheap': %lu\n",  gcglobals.write_barrier_phase1_hits);
    fprintf(gclog, "'Num_Write_Barriers_Gen': %lu\n",  gcglobals.write_barrier_phase1g_hits);
  }
  if (TRACK_WRITE_BARRIER_COUNTS > 3) {
    fprintf(gclog, "'Num_Write_Barriers_Started': %lu\n",  gcglobals.write_barrier_phase0_hits);
    fprintf(gclog, "'Num_Write_Barriers_NonNull': %lu\n",  gcglobals.write_barrier_phase0b_hits);
    fprintf(gclog, "'Num_Write_Barriers_Null': %lu\n", gcglobals.write_barrier_phase0_hits - gcglobals.write_barrier_phase0b_hits);
  }
  if (ENABLE_GC_TIMING_TICKS) {
    {
      auto s = foster::humanize_s(gcglobals.subheap_ticks, "");
      fprintf(gclog, "'Subheap_Ticks': %s\n", s.c_str());
    }
    if (gcglobals.num_gcs_triggered > 0) {
      auto v = foster::humanize_s(gcglobals.subheap_ticks / double(gcglobals.num_gcs_triggered), "");
      fprintf(gclog, "'Avg_GC_Ticks': %s\n", v.c_str());
    }
    if (gcglobals.num_gcs_triggered > 0) {
      auto v = foster::humanize_s(gcglobals.involuntary_ticks / double(gcglobals.num_gcs_triggered_involuntarily), "");
      fprintf(gclog, "'Avg_GC_Ticks_Involuntary': %s\n", v.c_str());
    }
  }
  {
    auto s = foster::humanize_s(gcglobals.num_closure_calls, "");
    fprintf(gclog, "'Num_Closure_Calls': %s\n", s.c_str());
  }

  fprintf(gclog, "'FosterlowerConfig': %s\n", (const char*)&__foster_fosterlower_config);
  fprintf(gclog, "'FosterGCConfig': {'FifoSize': %d, 'DefragReserveFraction: %.2f}\n", USE_FIFO_SIZE, kFosterDefragReserveFraction);

  /*
  fprintf(gclog, "Ref patterns seen:\n");
  std::map<int, int> refOrderPatterns;
  int totalSeen = 0;
  for (auto it : refPatterns) {
    fprintf(gclog, "     ");
    for (int i = 0; i < 32; ++i) { fprintf(gclog, (x & (1<<i)) ? '1' : '_'); }
    fprintf(gclog, ": %d\n", it.second);
    totalSeen += it.second;
    refOrderPatterns[__builtin_popcount(it.first)] += it.second;
  }
  for (auto it : refOrderPatterns) {
    fprintf(gclog, "           %d: %d (%.2f%%)\n", it.first, it.second, 100.0 * double(it.second)/double(totalSeen));
  }
  */

  //fprintf(gclog, "sizeof immix_space: %lu\n", sizeof(immix_space));
  //fprintf(gclog, "sizeof immix_line_space: %lu\n", sizeof(immix_line_space));

  gclog_time("Elapsed_runtime", total_elapsed, json);
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
  hdr_close(gcglobals.hist_gc_stackscan_frames);
  hdr_close(gcglobals.hist_gc_stackscan_roots);
  hdr_close(gcglobals.hist_gc_pause_micros);
  hdr_close(gcglobals.hist_gc_pause_ticks);
  hdr_close(gcglobals.hist_gc_rootscan_ticks);
  hdr_close(gcglobals.hist_gc_alloc_array);
  hdr_close(gcglobals.hist_gc_alloc_large);
  return had_problems ? 99 : 0;
}
// }}}

/////////////////////////////////////////////////////////////////

//  {{{ Debugging utilities
void gc_assert(bool cond_expected_true, const char* msg) {
  if (GC_ASSERTIONS) {
    if (!cond_expected_true) {
      gcglobals.allocator->dump_stats(NULL);
    }
    foster_assert(cond_expected_true, msg);
  }
}

void inspect_typemap(const typemap* ti) {
  fprintf(gclog, "typemap: %p\n", ti); fflush(gclog);
  if (!ti) return;
  fprintf(gclog, "\tsize:       %" PRId64 "\n", ti->cell_size);   fflush(gclog);
  if (ti->cell_size < 0 || ti->cell_size > (size_t(1) << 40)) {
    fprintf(gclog, "invalid typemap in inspect_typemap\n");
  } else {
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
  // Reminder: cell_size() and map are the same bit pattern.
  const typemap* map = cell->get_meta();
  if (GC_ASSERTIONS) {
    bool is_corrupted = (
          ((map->isCoro  != 0) && (map->isCoro  != 1))
       || ((map->isArray != 0) && (map->isArray != 1))
       || (map->numOffsets < 0)
       || (map->cell_size  < 0)
       || (map->cell_size  > (uint64_t(1)<<31)));
    if (is_corrupted) {
      fprintf(gclog, "Found corrupted type map for cell %p (body %p):\n", cell, cell->body_addr()); fflush(gclog);
      inspect_typemap(map);
      gc_assert(!is_corrupted, "tryGetTypemap() found corrupted typemap");
    }
  }
  
  if (!gcglobals.typemap_memory.contains((void*) map)) {
    return nullptr;
  }

  return map;
}
// }}}

/////////////////////////////////////////////////////////////////

extern "C" {
void foster__record_closure_call() {
  gcglobals.num_closure_calls++;
}

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

__attribute__((noinline))
void foster_generational_write_barrier_slowpath(void* val, void* obj, void** slot) {
  if (obj_is_marked(heap_cell::for_tidy((tidy*)val))) {
    return; // Don't bother recording old-to-old pointers.
  }
  immix_space* hs = heap_for_tidy( (tidy*) obj);
  //fprintf(gclog, "gen barr slowpath: val=%p, obj=%p, space: %p\n", val, obj, hs); fflush(gclog);
  ((immix_space*)hs)->remember_generational(obj, slot); // TODO fix this assumption
  if (TRACK_WRITE_BARRIER_COUNTS) { ++gcglobals.write_barrier_phase1g_hits; }
}

__attribute__((noinline))
void foster_write_barrier_with_obj_fullpath(void* val, void* obj, void** slot, bool into_default) {
  immix_space* hs = heap_for_tidy((tidy*) obj);
  // If we have a pointer being created from subheap X into the default subheap,
  // and X is linked to the default subheap, we need not record the pointer,
  // because every time we collect the default, we will also collect X.
  if (into_default && hs->is_linked_to_default_subheap) {
   return;
  }

  immix_space* hv = heap_for_tidy((tidy*) val);
  //fprintf(gclog, "val %p (header %zx) heap: %p\n", val, heap_cell::for_tidy((tidy*)val)->raw_header(), hv); fflush(gclog);

  // Invariant: hv != hs
  // Invariant: hv != nullptr
  if (TRACK_WRITE_BARRIER_COUNTS) { ++gcglobals.write_barrier_phase1_hits; }
  if (GCLOG_DETAIL > 3) { fprintf(gclog, "post gc %d: space %p remembering slot %p of obj %p with inc ptr %p; slot heap is %p; slot badge %d\n",
      gcglobals.num_gcs_triggered, hv, slot, obj, val, hs, int(get_current_line_stamp(obj))); }
  hv->remember_into(slot, obj);
}

__attribute__((noinline)) // this attribute will be removed once the barrier optimizer runs.
void foster_write_barrier_with_obj_generic(void* val, void* obj, void** slot, uint8_t gen, uint8_t subheap) {
  *slot = val;

  if (TRACK_WRITE_BARRIER_COUNTS > 3) { ++gcglobals.write_barrier_phase0_hits; }
  if (non_markable_addr(val)) { return; }
  if (TRACK_WRITE_BARRIER_COUNTS > 3) { ++gcglobals.write_barrier_phase0b_hits; }

  auto val_header = heap_cell::for_tidy((tidy*) val)->raw_header();
  auto obj_header = heap_cell::for_tidy((tidy*) obj)->raw_header();

  if (space_id_of_header(val_header) == space_id_of_header(obj_header)) {
    // Note we can't use raw line marks (even as an approximation/filter)
    // since large arrays do not have line marks.
    if (gen && !header_is_young(obj_header)) {
      if (!__foster_globals.disable_sticky) {
        foster_generational_write_barrier_slowpath(val, obj, slot);
      }
    }
  } else if (subheap) {
    foster_write_barrier_with_obj_fullpath(val, obj, slot, space_id_of_header(val_header) == 0);
  }
}

// Malloc can return low addresses, but it's convenient to use low addresses
// for un-markable data: static objects, null-ish constants, etc.
void* malloc_markable_handle() {
  //return malloc(sizeof(heap_handle<immix_space>));

  freelist* entry = (freelist*) *(gcglobals.lazy_mapped_markable_handles);
  freelist* next = entry->next;
  if (!next) { next = (freelist*) offset(entry, sizeof(heap_handle<immix_space>)); }
  *(gcglobals.lazy_mapped_markable_handles) = next;
  return entry;
}

void* foster_subheap_create_linkedp(bool is_linked) {
  ++gcglobals.num_subheaps_created;
  bool lines_at_a_time = 1;
  immix_space* subheap = new immix_space(is_linked, lines_at_a_time);
  void* alloc = malloc_markable_handle();
  heap_handle<immix_space>* h = (heap_handle<immix_space>*) realigned_for_heap_handle(alloc);
  h->header           = 32;
  h->unaligned_malloc = alloc;
  h->body             = subheap;
  if (is_linked) {
    gcglobals.default_linked_subheaps.push_back(h);
  } else {
    gcglobals.non_default_linked_subheaps.push_back(h);
  }
  return h->as_tidy();
}

// We need a degree of separation between the possibly-moving
// traced immix heap, which does not currently support finalizers/destructors,
// and the fact that immix_space is a C++ object with a non-trivial "dtor".
// There's also an issue of alignment: pointers in the immix heap ought to be
// aligned (though I guess it's not strictly necessary for types without any
// constructors).
void* foster_subheap_create_raw() {
  //return foster_subheap_create_linkedp(false);
  return foster_subheap_create_linkedp(true);
}

void* foster_subheap_create_small_raw() {
  return foster_subheap_create_linkedp(true);
  //return foster_subheap_create_linkedp(false);
}

void* foster_subheap_activate_raw(void* generic_subheap) {
  ++gcglobals.num_subheap_activations;
  // TODO make sure we properly retain (or properly remove!)
  //      a subheap that is created, installed, and then silently dropped
  //      without explicitly being destroyed.
  //fprintf(gclog, "subheap_activate: generic %p\n", generic_subheap); fflush(gclog);
  heap_handle<immix_space>* handle = heap_handle<immix_space>::for_tidy((tidy*) generic_subheap);
  // Clang appears to assume handle is non-null; handle will be null if generic_subheap is
  // the tidy pointer for the null heap cell.
  immix_space* subheap = (uintptr_t(generic_subheap) <= FOSTER_GC_DEFAULT_ALIGNMENT)
                          ? gcglobals.default_allocator
                          : handle->body;
  //fprintf(gclog, "subheap_activate: subheap %p)\n", subheap); fflush(gclog);
  heap_handle<immix_space>* prev = gcglobals.allocator_handle;
  //fprintf(gclog, "subheap_activate(generic %p, handle %p, subheap %p, prev %p)\n", generic_subheap, handle, subheap, prev);
  gcglobals.allocator = subheap;
  gcglobals.allocator_handle = handle;
  gcglobals.current_subheap_hash = subheap->hash_for_object_headers();

  g_in_non_default_subheap = (subheap != gcglobals.default_allocator);

  //fprintf(gclog, "subheap_activate: prev %p (tidy %p))\n", prev, prev->as_tidy()); fflush(gclog);
  //if (gcglobals.num_gcs_triggered < 2) { fprintf(gclog, "activated subheap %p\n", subheap); }
  return prev ? prev->as_tidy() : nullptr;
}

void foster_subheap_condemn_raw(void* generic_subheap) {
  //return;
  heap_handle<immix_space>* handle = heap_handle<immix_space>::for_tidy((tidy*) generic_subheap);
  auto subheap = handle->body;
  //fprintf(gclog, "condemning subheap %p\n", subheap);
  subheap->condemn();
  //fprintf(gclog, "condemned subheap %p\n", subheap);
  gcglobals.condemned_set.status = condemned_set_status::per_frame_condemned;
  gcglobals.condemned_set.spaces.insert(subheap);
}

void foster_subheap_collect_raw(void* generic_subheap) {
  //return;
  foster_subheap_condemn_raw(generic_subheap);

  heap_handle<immix_space>* handle = heap_handle<immix_space>::for_tidy((tidy*) generic_subheap);
  auto subheap = handle->body;
  //fprintf(gclog, "collecting subheap %p\n", subheap);
  subheap->force_gc_for_debugging_purposes();
  //fprintf(gclog, "subheap-collect done\n");
}

void foster_subheap_ignore_raw(void*) { return; }

} // extern "C"

void force_gc_for_debugging_purposes() {
  gcglobals.allocator->force_gc_for_debugging_purposes();
}

} // namespace foster::runtime::gc

uint8_t ctor_id_of(void* constructed) {
  uintptr_t i = uintptr_t(constructed);
  if (i < 64) {
    return uint8_t(i);
  }

  gc::heap_cell* cell = gc::heap_cell::for_tidy((gc::tidy*) constructed);

/*
  fprintf(gc::gclog, "ctor_id_of(%p)\n", constructed);
  if (cell->is_forwarded()) {
    fprintf(gc::gclog, "ctor_id_of observed a forwarded pointer... huh!\n");
  }
*/

  const gc::typemap* map = tryGetTypemap(cell);
  gc_assert(map, "foster_ctor_id_of() was unable to get a usable typemap");
  int8_t ctorId = map->ctorId;
  if (GC_ASSERTIONS && ctorId < 0) {
    fprintf(gc::gclog, "foster_ctor_id_of inspected bogus ctor id %d from cell %p in line %d of frame %u\n", ctorId, cell, line_offset_within_f15(cell), frame15_id_of(cell));
    gc::inspect_typemap(map);
    exit(3);
  }
  return ctorId;
}

} // namespace foster::runtime
} // namespace foster

