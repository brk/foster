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
#include "memory_range.h"
#include "gc_helpers.h"

#include "build/build_config.h" // from chromium_base
#include "hdr_histogram.h"

#include "execinfo.h" // for backtrace

#include <functional>
#include <stddef.h> // offsetof

// jemalloc_pages
bool  pages_boot(void);
void* pages_map(void* addr, size_t size, size_t alignment, bool* commit);
void  pages_unmap(void* addr, size_t size);



extern "C" char* __foster_fosterlower_config;

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)
#define PREFETCH_FOR_WRITES(addr) __builtin_prefetch(addr, 1, 3)
#define PREFETCH_FOR_MARKING(addr) __builtin_prefetch(addr, 0, 0)

// TODO: we currently don't evacuate, but when we do, we must first set up lazy_mapped_line_pins.
#define GCLOG_DETAIL 0
#define GCLOG_PRINT_LINE_MARKS 0
#define GCLOG_PRINT_LINE_HISTO 0
#define GCLOG_PRINT_USED_GROUPS 0
#define GCLOG_MUTATOR_UTILIZATION 0
#define ENABLE_GCLOG_PREP 0
#define ENABLE_GCLOG_ENDGC 0
#define PRINT_STDOUT_ON_GC 0
#define FOSTER_GC_ALLOC_HISTOGRAMS    0
#define FOSTER_GC_TIME_HISTOGRAMS     1 // Adds ~300 cycles per collection
#define ENABLE_GC_TIMING              1
#define GC_ASSERTIONS 0
#define TRACK_NUM_ALLOCATIONS         1
#define TRACK_NUM_ALLOC_BYTES         1
#define TRACK_NUM_OBJECTS_MARKED      1
#define TRACK_WRITE_BARRIER_COUNTS    1
#define TRACK_BYTES_ALLOCATED_PINHOOK 0
#define GC_BEFORE_EVERY_MEMALLOC_CELL 0
#define USE_FIFO_SIZE 0
#define DEBUG_VERIFY_MARK_BITS        0
#define DEBUG_PRINT_ALLOCATIONS  0
#define DEBUG_INITIALIZE_ALLOCATIONS  0 // Initialize even when the middle end doesn't think it's necessary
#define ELIDE_INITIALIZE_ALLOCATIONS  0 // Unsafe: ignore requests to initialize allocated memory.
#define MEMSET_FREED_MEMORY           0

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

#define IMMIX_LINE_SIZE_LOG 8
#define IMMIX_LINES_PER_FRAME15_LOG 7 /*15 - 8*/
#define IMMIX_LINES_PER_FRAME15   128

#define IMMIX_F15_PER_F21 64
#define IMMIX_BYTES_PER_LINE 256
#define IMMIX_GRANULES_PER_LINE (IMMIX_BYTES_PER_LINE / 16)
#define IMMIX_GRANULES_PER_BLOCK (128 * IMMIX_GRANULES_PER_LINE)

static_assert(IMMIX_GRANULES_PER_LINE == 16,    "documenting expected values");
static_assert(IMMIX_GRANULES_PER_BLOCK == 2048, "documenting expected values");

extern "C" {
  void foster_pin_hook_memalloc_cell(uint64_t nbytes);
  void foster_pin_hook_memalloc_array(uint64_t nbytes);
}

namespace foster {
namespace runtime {
namespace gc {

FILE* gclog = NULL;

// {{{ Type definitions for GC globals


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
 return roundUpToNearestMultipleWeak(bump, IMMIX_BYTES_PER_LINE);
}

// The pointer itself is the base pointer of the equivalent memory_range.
struct free_linegroup {
  void*           bound;
  free_linegroup* next;
};

class bump_allocator : public memory_range {
public:
  int group;
  bump_allocator() {
    this->base = nullptr;
    this->bound = nullptr;
    this->group = -1;
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

  free_linegroup* trim_trailing_lines() {
    if (this->base == this->bound) { return nullptr; }

    void* line_after_base = realigned_to_line_flat(this->base);

    if (line_after_base == this->bound) { return nullptr; }

    //fprintf(gclog, "trim_trailing_lines: base %p, line after base %p, bound %p\n", this->base, line_after_base, this->bound);
    
    free_linegroup* fg = (free_linegroup*) line_after_base;
    fg->bound = this->bound;

    this->bound = line_after_base;
    
    return fg;
  }
};

struct freelist { freelist* next; };

int address_space_prefix_size_log() {
  if (sizeof(void*) == 4) { return 32; }
  if (sizeof(void*) == 8) { return 47; }
  exit(3); return 0;
}

size_t lazy_mapped_frame15_condemned_size() { return (size_t(1) << (address_space_prefix_size_log() - 15)); }
size_t lazy_mapped_granule_marks_size() {     return (size_t(1) <<  address_space_prefix_size_log()     ) / (16 * 1); }

// On a 64-bit machine, physical address space will only be 48 bits usually.
// If we use 47 of those bits, we can drop the low-order 15 bits and be left
// with 32 bits! (47 bits gives 140 TB of usable virtual address space.)
typedef uint32_t frame15_id;
typedef uint32_t frame21_id;

frame15_id frame15_id_of(void* p) { return frame15_id(uintptr_t(p) >> 15); }
frame21_id frame21_id_of(void* p) { return frame21_id(uintptr_t(p) >> 21); }

uintptr_t low_n_bits(uintptr_t val, uintptr_t n) { return val & ((1 << n) - 1); }

int line_offset_within_f15(void* slot) {
  return int(low_n_bits(uintptr_t(slot) >> 8, 15 - 8));
}

class frame15;
class frame21;

frame15* frame15_for_frame15_id(frame15_id f15) {
  return (frame15*)(uintptr_t(f15) << 15);
}

int linegroup_size_in_lines(free_linegroup* g) { return distance((void*) g, g->bound) / IMMIX_BYTES_PER_LINE; }

struct used_linegroup {
  void*           base;
  int             count;

  int startline() const { return line_offset_within_f15(base); }
  int endline()   const { return line_offset_within_f15(base) + count; }

  size_t size_in_bytes() const { return count * IMMIX_BYTES_PER_LINE; }
  size_t size_in_lines() const { return count; }

  frame15_id associated_frame15_id() const { return frame15_id_of(base); }

  used_linegroup singleton(int i) const {
    return used_linegroup { .base  = offset(base,  i      * IMMIX_BYTES_PER_LINE),
                            .count = 1 };
  }

  bool contains(void* slot) const { return slot > base && distance(base, slot) < size_in_bytes(); }

  void clear_line_and_object_mark_and_validity_bits();
};

used_linegroup used_group_of_free_group(free_linegroup* g) {
  return {
    .base = (void*) g,
    .count = linegroup_size_in_lines(g)
  };
}

// }}}

struct immix_space;

struct immix_worklist_t {
    void       initialize()      { roots.clear(); }
    void       drain();
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
  uint8_t          num_holes_at_last_full_collection;
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

struct condemned_set {
  // Some objects (in particular, subheap handles) are not allocated on regular frames
  // and thus would otherwise not get their granule mark bits reset at the end of each collection.
  // We track, above, the set of all created subheaps (in order to identify unmarked subheaps),
  // but to avoid O(full-heap) work on a subheap collection,
  // we only want to reset the marks we established during each collection.
  std::set<heap_cell*> unframed_and_marked;

  // Use line marks to reclaim space, then reset linemaps and object marks.
  int64_t sweep_condemned(clocktimer<false>& phase,
                          int64_t* num_lines_tracked, int64_t* num_groups_tracked);

  int64_t lines_live;

  void prepare_for_tracing();
};

struct GCGlobals {
  immix_space* allocator = NULL;

  condemned_set condemned_set;

  memory_range typemap_memory;

  bool had_problems;
  bool logall;

  std::map<std::pair<const char*, typemap*>, int64_t> alloc_site_counters;
  std::map<void*, std::pair<const char*, const char*> > alloc_site_locs;

  std::set<frame21*> all_frame21s;

  double gc_time_us;

  clocktimer<true> init_start;

  int num_gcs_triggered;
  int num_big_stackwalks;

  uint64_t num_allocations;
  uint64_t num_alloc_bytes;

  uint64_t num_closure_calls;

  uint64_t write_barrier_phase0_hits;
  uint64_t write_barrier_phase0b_hits;
  uint64_t write_barrier_phase1_hits;
  uint64_t write_barrier_phase1g_hits;

  uint64_t num_objects_marked_total;
  uint64_t alloc_bytes_marked_total;

  uint64_t max_bytes_live_at_whole_heap_gc;

  void**            lazy_mapped_markable_handles;

  frame15info*      lazy_mapped_frame15info;

  // Granule marks are set for objects which were live at last collection.
  // Rather than a simple bitset, we encode object sizes in granule marks.
  // Small and medium-sized objects (< 128 granules, or 2 KB) store their
  // granule count in a single byte. Larger objects have the high bit set in
  // their first granule mark.
  uint8_t*          lazy_mapped_granule_marks;

  // Granule validity is set for objects which might be live:
  //    those live at the last collection,
  //    or those which have been subsequently allocated.
  // In the literature, this is sometimes called an object map.
  uint8_t*          lazy_mapped_granule_validity;

  // Count of live bytes (per line) traced, used for defragmentation/evacuation.
  uint16_t*         lazy_mapped_frame_liveness;

  uint8_t*          lazy_mapped_line_marks;
  uint8_t*          lazy_mapped_line_pins;

  struct hdr_histogram* hist_gc_stackscan_roots;
  struct hdr_histogram* hist_gc_pause_micros;
  struct hdr_histogram* hist_gc_pause_ticks;
  struct hdr_histogram* hist_gc_rootscan_ticks;
  struct hdr_histogram* hist_gc_alloc_array;
  struct hdr_histogram* hist_gc_alloc_large;
  uint64_t enum_gc_alloc_small[129];

  int64_t marked_histogram[128];
  int64_t marked_histogram_frames[128];
  int64_t residency_histogram[128];
};

GCGlobals gcglobals;

void reset_marked_histogram() {
  if (GCLOG_PRINT_LINE_HISTO) {
    int64_t sum_x = 0;
    int64_t sum_f = 0;
    int64_t sum_u = 0;
    int64_t sum_v = 0;
    for (int i = 0; i < 128; ++i) {
      auto x = gcglobals.marked_histogram[i];
      auto f = gcglobals.marked_histogram_frames[i];
      auto u = (f * IMMIX_LINES_PER_FRAME15) - x;
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
    int64_t all = sum_f * IMMIX_LINES_PER_FRAME15;
    for (int i = 127; i >= 0; --i) {
      auto x = gcglobals.marked_histogram[i];
      auto f = gcglobals.marked_histogram_frames[i];
      auto u = (f * IMMIX_LINES_PER_FRAME15) - x;
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

// The worklist would be per-GC-thread in a multithreaded implementation.
immix_worklist_t immix_worklist;
std::vector<tori*> conservative_roots; // Invariant: contains valid tidy pointers.

template <typename T>
inline T num_granules(T size_in_bytes) { return size_in_bytes / T(16); }

uintptr_t global_granule_for(void* p) { return num_granules(uintptr_t(p)); }

frame21* frame21_of_id(frame21_id x) { return (frame21*) (uintptr_t(x) << 21); }

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
  uint8_t* markbyte = &gcglobals.lazy_mapped_granule_marks[global_granule_for(obj)];
  return *markbyte != 0;
}
inline bool arr_is_marked(heap_array* obj) { return obj_is_marked((heap_cell*)obj); }

inline bool is_actually_tidy(void* ptr) {
  uint8_t* markbyte = &gcglobals.lazy_mapped_granule_validity[global_granule_for(ptr)];
  return *markbyte != 0;
}

inline void designate_as_valid_object_start_addr(void* ptr) {
  gcglobals.lazy_mapped_granule_validity[global_granule_for(ptr)] = 1;
}

// Roughly 3% degredation to incorporate size bits..
inline void do_mark_obj_of_size(heap_cell* obj, int64_t cell_size) {
  //obj->mark_not_young();

  designate_as_valid_object_start_addr(obj->body_addr());

  uintptr_t g0 = global_granule_for(obj);
  int64_t size_in_granules = (cell_size + 15) / 16;

  if (GCLOG_DETAIL > 3) { fprintf(gclog, "designated valid, now setting granule mark for object %p in frame %u; granule %zd ; #grans %d\n", obj, frame15_id_of(obj), g0, int(size_in_granules)); }
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

inline void do_unmark_granule(void* obj) {
  gcglobals.lazy_mapped_granule_marks[global_granule_for(obj)] = 0;
}

void clear_object_mark_and_validity_bits_for_used_group(used_linegroup& g) {
  //fprintf(gclog, "Clearing object mark and validity bits for used group @ %p (size %d lines)\n", g.base, g.count); fflush(gclog);
  memset(&gcglobals.lazy_mapped_granule_marks   [global_granule_for(g.base)], 0, g.count * IMMIX_GRANULES_PER_LINE);
  memset(&gcglobals.lazy_mapped_granule_validity[global_granule_for(g.base)], 0, g.count * IMMIX_GRANULES_PER_LINE);
}

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
    allot->set_header(arr_elt_map);
    allot->set_num_elts(num_elts);
    designate_as_valid_object_start_addr(allot->body_addr());
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_array(total_bytes); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += total_bytes; }

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
    if ((b != e) && (line_offset_within_f15(last) == IMMIX_LINES_PER_FRAME15 - 1)) {
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
  finfo->frame_classification = frame15kind::immix_smallmedium;
}

// Markable objects live in the upper bits of address space.
// Unfortunately it appears to be surprisingly hard to force a malloc implementation
// to not use the lower 4 GB of virtual memory.
bool non_markable_addr_toosmall(void* addr) { return uintptr_t(addr) <   uintptr_t(0x400000); }
bool non_markable_addr_toobig(void* addr) {   return uintptr_t(addr) >= (uintptr_t(1) << address_space_prefix_size_log()); }
// The compiler, runtime,  and GC cooperate to represent "small" integer values
// as tagged pointer-sized words; if we see the tag, the other bits aren't an address!
bool non_markable_addr_taggedInt(void* addr) { return (uintptr_t(addr) & 1) != 0; }
// Pointers on the heap aren't arbitrary bitstrings; type safety ensures they can't
// point past the heap, so we don't need the toobig check.
bool non_markable_addr_toosmall_or_taggedInt(void* addr) {
  return non_markable_addr_toosmall(addr) || non_markable_addr_taggedInt(addr);
}
// Conservative stack scans need to consider every kind of invalid pointer.
bool are_addr_bits_invalid(void* addr) {
  return non_markable_addr_toosmall_or_taggedInt(addr) || non_markable_addr_toobig(addr);
}

tidy* assume_tori_is_tidy(tori* p) { return (tidy*) p; }

// }}}

// {{{ Helpers (notably, for allocation and stack scanning).
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

uint8_t* markmap_for_frame15_id(frame15_id fid) {
  return &gcglobals.lazy_mapped_granule_marks[size_t(fid) * IMMIX_LINES_PER_FRAME15 * IMMIX_GRANULES_PER_LINE];
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
                                  bool     init) {
    //auto bumper_size_at_start = bumper->size();
    heap_array* allot = static_cast<heap_array*>(bumper->prechecked_alloc_noinit(total_bytes));

    if (GC_ASSERTIONS) { gc_assert(frame15_id_of(allot) == frame15_id_of(allot->body_addr()), "pre array: metadata and body address on different frames!"); }
    if (DEBUG_INITIALIZE_ALLOCATIONS ||
      (init && !ELIDE_INITIALIZE_ALLOCATIONS)) { memset((void*) allot, 0x00, total_bytes); }
    if (DEBUG_PRINT_ALLOCATIONS) {
      fprintf(gclog, "alloc'a %d @ %p; num elts = %d; size at start was %zd\n", int(total_bytes), allot, int(num_elts), bumper->size() + total_bytes);
    }
    allot->set_header(arr_elt_map);
    allot->set_num_elts(num_elts);
    designate_as_valid_object_start_addr(allot->body_addr());
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_array(total_bytes); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += total_bytes; }

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
                                 int64_t  cell_size) {
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
    if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_cell(cell_size); }
    if (TRACK_NUM_ALLOCATIONS) { ++gcglobals.num_allocations; }
    if (TRACK_NUM_ALLOC_BYTES) { gcglobals.num_alloc_bytes += cell_size; }
    if (FOSTER_GC_ALLOC_HISTOGRAMS) { allocate_cell_prechecked_histogram((int) cell_size); }
    allot->set_header(map);
    designate_as_valid_object_start_addr(allot->body_addr());

    if (GC_ASSERTIONS && line_for_slot_is_marked(allot)) {
      fprintf(gclog, "INVARIANT VIOLATED: allocating cell (%p) on a pre-marked line?!?\n", allot);
      exit(4);
    }
    if (GC_ASSERTIONS && obj_is_marked(allot)) {
      fprintf(gclog, "INVARIANT VIOLATED: allocating cell (%p)      pre-marked     ?!?\n", allot);
      exit(4);
    }

    if (DEBUG_PRINT_ALLOCATIONS) {
      fprintf(gclog, "Allocated prechecked cell of size %zd bytes at %p (line %d of %u)\n", cell_size, allot->body_addr(),
          line_offset_within_f15(allot->body_addr()), frame15_id_of(allot->body_addr()));
    }

    return allot->body_addr();
  }

  tidy* tidy_for(tori* t) { return (tidy*) t; }

  // Note: in conservative operation, all roots (including those from coros)
  // must be collected before tracing. Otherwise, evacuation (if we re-implemented
  // it) might move an object pointed to by a heap-allocated stack root.
  void consider_conservative_root(unchecked_ptr* root) {
    gc_assert(root != NULL, "someone passed a NULL root addr!");
    auto maybe_obj = unchecked_ptr_val(*root);
    bool trivially_unmarkable = are_addr_bits_invalid(maybe_obj);

    if (GCLOG_DETAIL > 1) {
      fprintf(gclog, "\t\tgc %d: STACK SLOT slot (%p) holds %12p; might be markable? %d [tidy %d]\n",
                        gcglobals.num_gcs_triggered,
                        root,
                        maybe_obj,
                        trivially_unmarkable ? 0 : 1,
                        (!trivially_unmarkable && is_actually_tidy(maybe_obj)) ? 1 : 0
                        );
    }

    if (trivially_unmarkable) { return; }

    // Tidy objects are 16-byte aligned and thus have four zero low bits.
    if ((uintptr_t(maybe_obj) & 0xF) == 0) {
      if (is_actually_tidy(maybe_obj)) {
        conservative_roots.push_back(maybe_obj);
      }
    } else {
      // In case we get a pointer that isn't properly aligned to be tidy,
      // we'll act as though it could be either of the nearest two tidy pointers.
      auto tidy_obj = (tori*) ((uintptr_t(maybe_obj) + 15) & ~0xF);
      maybe_obj     = (tori*) ((uintptr_t(maybe_obj)     ) & ~0xF);

      if (is_actually_tidy(maybe_obj)) {
        conservative_roots.push_back(maybe_obj);
      }
      if (is_actually_tidy(tidy_obj)) {
        conservative_roots.push_back(tidy_obj);
      }
    }
  }

  void clear_line_and_object_mark_and_validity_bits_for_used_group(used_linegroup g) {
    auto fid = frame15_id_of(g.base);
    uint8_t* linemap = linemap_for_frame15_id(fid);

    //fprintf(gclog, "clearing linemap of size %zd\n", g.size_in_lines());
    memset(&linemap[g.startline()], 0, g.size_in_lines());
    clear_object_mark_and_validity_bits_for_used_group(g);
  }

} // namespace helpers
// }}}

// Bitmap overhead for 16-byte granules is 8 KB per MB (a bit under 1%).
// Bytemap overhead for 16-byte granules is 64 KB per MB (6.25%).

////////////////////////////////////////////////////////////////////

// TODO use stat_tracker again?

// {{{ Space management
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

void display_linemap_for_frame15_id(frame15_id fid);

struct space_allocator_t {
  space_allocator_t() : curr_frame15(0) {}

private:
  std::vector<frame21*>   frame21s;
  std::vector<frame15_id> frame15s;

  size_t curr_frame15;

  std::vector<free_linegroup*> singles;
  std::vector<free_linegroup*> biggers;

public:
  size_t get_curr_frame_idx() { return curr_frame15; }
  void reset_allocator_cache() {
    // fprintf(gclog, "resetting available line cache...\n");
    curr_frame15 = 0;
    singles.clear();
    biggers.clear();
  }

  void reset_scan(int64_t lines_reclaimed) {
    reset_marked_histogram();
  }

  void display_heap_linemaps() {
    for (auto fid : frame15s) { display_linemap_for_frame15_id(fid); }
  }

  void grow_heap_by(ssize_t maxbytes) {
    // Round up; a request for 10K should be one frame15, not zero.
    auto frame15s_left = (maxbytes + ((1 << 15) - 1)) >> 15;

    auto mb = foster::humanize_s(double(maxbytes), "B");
    auto fb = foster::humanize_s(double(frame15s_left * (1 << 15)), "B");
    fprintf(gclog, "byte_limit: maxbytes = %s, maxframe15s = %ld, framebytes=%s, maxlines=%ld\n",
          mb.c_str(), frame15s_left, fb.c_str(), frame15s_left * IMMIX_LINES_PER_FRAME15);

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
  }

  template<bool small>
  free_linegroup* grab_free_linegroup(size_t num_lines, size_t max_lines_wanted) {
    int big_limit = 0;

    while (true) {
      if (small) {
        if (!singles.empty()) {
          auto g = singles.back(); singles.pop_back();
          if (GCLOG_DETAIL > 2) { fprintf(gclog, "marking single allocated line (size %zd) at %p\n", distance(g, g->bound), g); }
          // Invariant(FREEMETACLEAR): metadata for free linegroups has already been cleared.
          //    (cleared pre-collection, and by definition left unmodified)
          if (linegroup_size_in_lines(g) != 1) {
            fprintf(gclog, "OOPS singleton linegroup %p had non-1 size\n", g);
          }
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
        if (size < num_lines) continue;
        
          if (size > IMMIX_LINES_PER_FRAME15) {
            fprintf(gclog, "OOPS bigger linegroup %p was oversized of size %d\n", g, size);
          }

        if (size >= num_lines) {
          biggers[i] = nullptr;
          // fprintf(gclog, "grab_free_linegroup marking slots used from %p to %p stored at %p\n", g, g->bound, &g->bound);
          // Invariant(FREEMETACLEAR): metadata for free linegroups has already been cleared.
          return g;
        }
      }

      if (curr_frame15 == frame15s.size()) {
        curr_frame15 = 0;
        fprintf(gclog, "curr_frame iterator hit limit, gotta do a collection...\n");
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
    uint8_t* line_status = linemap_for_frame15_id(fid);
    auto f15 = frame15_for_frame15_id(fid);

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

      // Validity bits must persist after collections.
      // Mark bits could be cleared either before or after collection;
      // we clear before, so no need to clear here too.

      if (i == i0 + 1) {
        singles.push_back(g);
      } else {
        //fprintf(gclog, "bigger: i0 =  %d; i = %d; size = %d; g=%p; g->bound=%p;; frame=%u\n", i0, i, distance(g, g->bound), g, g->bound, frame15_id_of(g));
        biggers.push_back(g);
      }
    }

    //fprintf(gclog, "LSFA: ");
    //display_linemap_for_frame15_id(fid);

    int num_marked_lines = IMMIX_LINES_PER_FRAME15 - num_available_lines;
    auto finfo = frame15_info_for(f15);
    finfo->num_holes_at_last_full_collection = num_holes_found;
    gcglobals.marked_histogram[num_holes_found] += num_marked_lines;
    gcglobals.marked_histogram_frames[num_holes_found] += 1;
    gcglobals.residency_histogram[num_holes_found] += gcglobals.lazy_mapped_frame_liveness[fid];

    gcglobals.lazy_mapped_frame_liveness[fid] = 0;
  }

public:
  double  full_heap_line_count() { return double(frame15s.size() * IMMIX_LINES_PER_FRAME15); }
};

space_allocator_t global_space_allocator;
// }}}

// {{{ Linemap display helpers
uint8_t count_marked_lines_for_frame15(frame15* f15, uint8_t* linemap_for_frame);

void display_linemap_for_frame15_id(frame15_id fid) {
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
  fprintf(gclog, "\n");
}

void display_used_linegroup_linemap(used_linegroup* g, uint8_t* linemap) {
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
  }
}
// }}}

// {{{ metadata helpers
void used_linegroup::clear_line_and_object_mark_and_validity_bits() {
  uint8_t* linemap = linemap_for_frame15_id(associated_frame15_id());

  gc_assert(startline() != endline(), "used linegroup had same start and end line...?");

  // Note: must clear only our bits, since those of other groups may not yet have been inspected.
  for (int i = startline(); i < endline(); ++i) {
    //fprintf(gclog, "clearing linemap entry %d for (%u), linemap addr: %p\n", i, associated_frame15_id(), &linemap[i]);  fflush(gclog);
    do_unmark_line(i, linemap);
  }
  gc_assert(startline() >= 0, "invalid startline when clearing bits");
  gc_assert(endline() <= IMMIX_LINES_PER_FRAME15, "invalid endline when clearing bits");
  gc_assert(startline() < endline(), "invalid: startline after endline when clearing bits");
  clear_object_mark_and_validity_bits_for_used_group(*this);
}

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

// }}}

// {{{ Factored-out functionality: cell scanning, space tracking.
// This struct contains per-frame state and code shared between
// regular and line-based immix frames.
namespace immix_common {
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
      // We only need to filter non-markable constants;
      // type safety ensures we won't see un-allocated pointer values.
      if (!non_markable_addr_toosmall_or_taggedInt(* (void**)slot)) {
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
  // Precondition: root points to an unmarked, unforwarded, markable object.
  void immix_trace(unchecked_ptr* root, heap_cell* obj) {
    //       |------------|       obj: |------------|
    // root: |    body    |---\        |  size/meta |
    //       |------------|   |        |------------|
    //                        \- tidy->|            |
    //                        |       ...          ...
    //                        \-*root->|            |
    //                                 |------------|
    scan_cell(obj);
  }

  // Returns true if we should immediately retry GC (e.g. to switch to full-heap non-sticky collection).
  void common_gc();
};

class immix_space_tracking {
  std::vector<used_linegroup> used_lines;
  ssize_t lines_tracked;

public:
  immix_space_tracking() : lines_tracked(0) {}
  ~immix_space_tracking() {}

  void add_and_install_free_group(free_linegroup* fg, bump_allocator& bumper) {
    used_linegroup ug = { .base = fg, .count = linegroup_size_in_lines(fg) };
    note_used_group(ug);

    bumper.base  = realigned_for_allocation(fg);
    bumper.bound = fg->bound;
    bumper.group = used_lines.size() - 1;
  }
  void note_used_group(used_linegroup g) {
    // fprintf(gclog, "noting used group of size %d\n", g.count);
    used_lines.push_back(g); lines_tracked += g.count; }

  // Precondition: n > 0.
  void trim_ith_group_by(int i, int n_lines) {
    used_lines[i].count -= n_lines; lines_tracked -= n_lines;
    // fprintf(gclog, "count[%d] after -= %d is now %d\n", i, n_lines, used_lines[i].count);
  }

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

void process_worklists();

void collect_all_potential_roots() {
  // Caller-saved registers will be on the stack already, but we may need to
  // inspect/collect callee-saved registers. We collect the union of SysV and
  // Microsoft's calling convention saved registers, except for RBP and RSP.
  void* registers[7] = { 0 };
  __asm__ (
        "movq %%rbx,   (%0)\n\t"
        "movq %%r12,  8(%0)\n\t"
        "movq %%r13, 16(%0)\n\t"
        "movq %%r14, 24(%0)\n\t"
        "movq %%r15, 32(%0)\n\t"
        "movq %%rdi, 40(%0)\n\t"
        "movq %%rsi, 48(%0)\n\t"
    : // no output
    : "r" (registers) // store in any register
    // nothing clobbered
  );
  for (int i = 0; i < 7; ++i) {
    helpers::consider_conservative_root((unchecked_ptr*) &registers[i]);
  }

  collect_roots_from_stack(__builtin_frame_address(0));

  // TODO: should keep a list of dirty coros and scan them before tracing.
  foster_bare_coro** coro_slot = __foster_get_current_coro_slot();
  foster_bare_coro*  coro = *coro_slot;
  if (coro) {
    if (GCLOG_DETAIL > 1) {
      fprintf(gclog, "==========visiting current coro: %p\n", coro); fflush(gclog);
    }
    helpers::consider_conservative_root((unchecked_ptr*)coro_slot);
    if (GCLOG_DETAIL > 1) {
      fprintf(gclog, "==========visited current coro: %p\n", coro); fflush(gclog);
    }
  }
}

void immix_common::common_gc() {
#if DEBUG_VERIFY_MARK_BITS
    g_marked_this_cycle.clear();
#endif

    auto num_marked_at_start   = gcglobals.num_objects_marked_total;
    auto bytes_marked_at_start = gcglobals.alloc_bytes_marked_total;

    gcglobals.num_gcs_triggered += 1;
    if (PRINT_STDOUT_ON_GC) { fprintf(stdout, "                        start GC #%d\n", gcglobals.num_gcs_triggered); fflush(stdout); }
    if (ENABLE_GCLOG_ENDGC) { fprintf( gclog, "                        start GC #%d\n",
          gcglobals.num_gcs_triggered); fflush(gclog); }

    clocktimer<false> gcstart; gcstart.start();
    clocktimer<false> phase;

    // Make sure no line groups persist between collections.
    global_space_allocator.reset_allocator_cache();

    phase.start();
    collect_all_potential_roots();
    auto rootCollection_us = phase.elapsed_us();

    phase.start();
    gcglobals.condemned_set.prepare_for_tracing();
    auto markResetting_us = phase.elapsed_us();

    phase.start();
    process_worklists();
    auto recursiveMarking_us = phase.elapsed_us();

    if (GCLOG_PRINT_LINE_MARKS) { global_space_allocator.display_heap_linemaps(); }

    phase.start();

    auto bytes_marked = gcglobals.alloc_bytes_marked_total - bytes_marked_at_start;

    gcglobals.condemned_set.lines_live = 0;
    int64_t num_lines_tracked = 0;
    int64_t num_groups_tracked = 0;
    int64_t num_lines_reclaimed = gcglobals.condemned_set.sweep_condemned(
                                                phase,
                                                &num_lines_tracked, &num_groups_tracked);
    double sweep_us = phase.elapsed_us();

    auto line_footprint = gcglobals.condemned_set.lines_live; // Note: only valid for involuntary collections.
    auto line_footprint_in_bytes = line_footprint * IMMIX_BYTES_PER_LINE;

    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "%zd groups tracking %zd lines (avg %.1f lines/group).\n",
        num_groups_tracked, num_lines_tracked, double(num_lines_tracked)/double(num_groups_tracked));
    }

    double byte_level_fragmentation_percentage =
      ((double(line_footprint_in_bytes) / double(bytes_marked)) - 1.0) * 100.0;

    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "Byte level fragmentation percentage: %.1f\n",
          byte_level_fragmentation_percentage);
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
      gcglobals.max_bytes_live_at_whole_heap_gc =
        std::max(gcglobals.max_bytes_live_at_whole_heap_gc, bytes_marked);
    }

    if (ENABLE_GC_TIMING && GCLOG_MUTATOR_UTILIZATION) {
      auto ems = gcstart.elapsed_ms();
      auto now = gcglobals.init_start.elapsed_s();
      fprintf(gclog, "MUTUTIL %f %f\n", // pause duration in ms, pause start time in s
                      ems, now - (ems / 1000.0));
    }
  }

#if ((GCLOG_DETAIL > 1) || ENABLE_GCLOG_ENDGC)
#   if TRACK_NUM_OBJECTS_MARKED
      fprintf(gclog, "\t%zu objects marked in this GC cycle, %zu marked overall\n",
              gcglobals.num_objects_marked_total - num_marked_at_start,
              gcglobals.num_objects_marked_total);
#   endif

      if (ENABLE_GC_TIMING) {
        double delta_us = gcstart.elapsed_us();
        double other_us = delta_us - (rootCollection_us + recursiveMarking_us + sweep_us + markResetting_us);
        fprintf(gclog, "\ttook %zd us which was %.2f%% stack root collection, %.2f%% (%.1f us) from remsets & mark resetting, %.2f%% marking, %.2f%% sweeping (%.1f us), %.2f%% other (%.1f us)\n",
                          int64_t(delta_us),
                          (rootCollection_us * 100.0)/delta_us,
                          (markResetting_us * 100.0)/delta_us, markResetting_us,
                          (recursiveMarking_us * 100.0)/delta_us,
                          (sweep_us * 100.0)/delta_us, sweep_us,
                          (other_us * 100.0)/delta_us, other_us
                          );

        //double collection_us = recursiveMarking_us + sweep_us;
        //g_sweeping_total_us += sweep_us;
        double lines_per_us = double(num_lines_reclaimed) / delta_us;
        double ns_per_line = (delta_us * 1000.0) / double(num_lines_reclaimed);
        fprintf(gclog, "    lines/us: %.2f;  ns/line: %.2f\n", lines_per_us, ns_per_line);
        
        //fprintf(gclog, "Sweeping reclaimed %zd lines in %f us.     (total RC sweeping time: %.2f us)\n", num_lines_reclaimed, sweeping_us, g_rc_sweeping_total_us);

      }

    fprintf(gclog, "\t/endgc %d\n\n", gcglobals.num_gcs_triggered);
    fflush(gclog);
#endif

  if (PRINT_STDOUT_ON_GC) { fprintf(stdout, "                              endgc\n"); fflush(stdout); }

  if (ENABLE_GC_TIMING) {
    double delta_us = gcstart.elapsed_us();
    if (FOSTER_GC_TIME_HISTOGRAMS) {
      hdr_record_value(gcglobals.hist_gc_pause_micros, int64_t(delta_us));
    }
    gcglobals.gc_time_us += delta_us;
  }

  global_space_allocator.reset_scan(num_lines_reclaimed);

}
// }}}

// Invariant: IMMIX_LINES_PER_FRAME15 <= 256
// Invariant: marked lines have value 1, unmarked are 0.
uint8_t count_marked_lines_for_frame15(frame15* f15, uint8_t* linemap_for_frame) {
  uint8_t count = 0; // Note: Clang compiles this to straight-line code using vector ops.
  for (int i = 0; i < IMMIX_LINES_PER_FRAME15; ++i) { count += linemap_for_frame[i]; }
  return count;
}



class immix_space {
public:
  immix_space() {
    approx_lines_allocated_since_last_collection = 0;
    if (GCLOG_DETAIL > 2) { fprintf(gclog, "new immix_space %p\n", this); }
  }

  void dump_stats(FILE* json) {
    return;
  }

  void prepare_for_tracing() {  
    clear_line_and_object_mark_and_validity_bits();

    // Note: the object map is used before tracing starts, to identify
    // valid references from conservative roots. We clear the object map
    // here, and tracing re-establishes validity for live objects.

    // In a generational collector, we'd also discard the remembered set here.
  }

  void clear_line_and_object_mark_and_validity_bits() {
    laa.reset_large_array_marks();

    tracking.iter_used_lines_void([this](used_linegroup g) {
        /*
        fprintf(gclog, "GCPREP: clearing linegroup at line %d of (%u)(+%d)\n",
            line_offset_within_f15(g.base),
            frame15_id_of(g.base),
            g.count);
            */
      helpers::clear_line_and_object_mark_and_validity_bits_for_used_group(g);
    });
  }

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

  void force_gc_for_debugging_purposes() {
    if (GCLOG_DETAIL > 2) { fprintf(gclog, "force_gc_for_debugging_purposes triggering immix gc\n"); }
    immix_common::common_gc();
  }

  // {{{ Prechecked allocation functions
  template <int N>
  tidy* allocate_cell_prechecked_N(const typemap* map) {
    return helpers::allocate_cell_prechecked(&small_bumper, map, N);
  }

  tidy* allocate_cell_prechecked(const typemap* map) {
    return helpers::allocate_cell_prechecked(&small_bumper, map, map->cell_size);
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
    free_linegroup* g = global_space_allocator.grab_free_linegroup<small>(lines_needed, 128);
    if (!g) {
      // fprintf(gclog, "grab_free_linegroup(for %zd bytes = %d lines) returned null\n", cell_size, lines_needed);
      return false;
    }

    approx_lines_allocated_since_last_collection += linegroup_size_in_lines(g);
    // fprintf(gclog, "try_prep_allocable_block installing free group of size %d\n", linegroup_size_in_lines(g));
    tracking.add_and_install_free_group(g, *bumper);

    if (ENABLE_GCLOG_PREP) {
      fprintf(gclog, "after gc %d: Prepared allocatable block: %d lines at %p  (%d in %u) for space %p; curr frame idx %zd\n",
          gcglobals.num_gcs_triggered,
          linegroup_size_in_lines(g), g,
          line_offset_within_f15(g),
          frame15_id_of(g), this,
          global_space_allocator.get_curr_frame_idx());
      //display_linemap_for_frame15_id(frame15_id_of(g));
    }

    if (MEMSET_FREED_MEMORY) {
      auto dist = distance(g, g->bound);
      memset(offset(g, 16), 0xef, dist - 16);
    }
    return true;
  }

  int unmarked_line_from(uint8_t* linemap, int start) {
      for (int i = start; i < (IMMIX_LINES_PER_FRAME15 - 1); ++i) {
        if (linemap[i] == 0) return i;
      }
      return -1;
  }

  int first_marked_line_after(uint8_t* linemap, int start) {
      for (int i = start + 1; i < IMMIX_LINES_PER_FRAME15; ++i) {
        if (linemap[i] != 0) return i;
      }
      return IMMIX_LINES_PER_FRAME15;
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

  void* allocate_cell_16(typemap* typeinfo) { return allocate_cell_N<16>(typeinfo); }
  void* allocate_cell_32(typemap* typeinfo) { return allocate_cell_N<32>(typeinfo); }
  void* allocate_cell_48(typemap* typeinfo) { return allocate_cell_N<48>(typeinfo); }

  void* allocate_cell_slowpath(typemap* typeinfo) __attribute__((noinline))
  {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.

    if (GCLOG_DETAIL > 2) { fprintf(gclog, "allocate_cell_slowpath for size-%zd cell triggering immix gc\n", cell_size); }

    immix_common::common_gc();

    if (!try_establish_alloc_precondition<true>(&small_bumper, cell_size)) {
      helpers::oops_we_died_from_heap_starvation("allocate_cell_slowpath"); return NULL;
    }

    //fprintf(gclog, "gc collection freed space for cell, now have %lld\n", curr->free_size());
    //fflush(gclog);

    return allocate_cell_prechecked(typeinfo);
  }

  virtual void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) {
    int64_t slot_size = elt_typeinfo->cell_size; // note the name change!
    int64_t req_bytes = array_size_for(n, slot_size);

    //fprintf(gclog, "immix space allocating array, %d elts * %d b = %d bytes\n", n, slot_size, req_bytes);

    if (false && FOSTER_GC_ALLOC_HISTOGRAMS) {
      hdr_record_value(gcglobals.hist_gc_alloc_array, req_bytes);
    }

    if (req_bytes <= IMMIX_BYTES_PER_LINE) {
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
      return helpers::allocate_array_prechecked(bumper, elt_typeinfo, n, req_bytes, init);
    } else {
      if (GCLOG_DETAIL > 2) { fprintf(gclog, "allocate_array_into_bumper needing %zd bytes triggering immix gc\n", req_bytes); }
      fprintf(gclog, "bumper size before GC: %zd\n", bumper->size());
      immix_common::common_gc();

      fprintf(gclog, "bumper size after GC: %zd\n", bumper->size());
      if (try_establish_alloc_precondition<small>(bumper, req_bytes)) {
        fprintf(gclog, "gc collection freed space for array...\n");
        fflush(gclog);
        return helpers::allocate_array_prechecked(bumper, elt_typeinfo, n, req_bytes, init);
      } else {
        helpers::oops_we_died_from_heap_starvation("allocate_array_into_bumper"); return NULL; }
    }
  }

  // }}}

  bool is_empty() { return laa.empty() && tracking.num_lines_tracked() == 0; }

  uint64_t approx_size_in_bytes() {
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
    }
    return rv * IMMIX_BYTES_PER_LINE;
  }

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

    clocktimer<false> insp_ct; insp_ct.start();
    tracking.iter_used_lines_taking_ownership([&](used_linegroup g) {
      int reclaimed = this->inspect_lines_postgc(g);
      num_lines_reclaimed += reclaimed;
    });
    auto inspectFrame15Time_us = insp_ct.elapsed_us();

    auto deltaPostMarkingCleanup_us = phase.elapsed_us();


    //size_t frame15s_total = tracking.logical_frame15s();
    size_t lines_tracked = tracking.num_lines_tracked();
    size_t lines_allocated = this->approx_lines_allocated_since_last_collection;

    if (GCLOG_DETAIL > 0) {
      fprintf(gclog, "Reclaimed (%zd) lines.\n", num_lines_reclaimed);
    }

#if ((GCLOG_DETAIL > 1) && ENABLE_GCLOG_ENDGC)
      { auto s = foster::humanize_s(nursery_ratio * double(lines_tracked * IMMIX_BYTES_PER_LINE), "B");
      fprintf(gclog, "Allocated into %zd lines ('nursery' was %.1f%% = %s of %zd total)\n", lines_allocated, 100.0 * nursery_ratio, s.c_str(), lines_tracked);
      }
      fprintf(gclog, "    global yield rate: %f\n", 100.0 * yield_rate);
      fprintf(gclog, "     local yield rate: %f\n", 100.0 * local_yield);

      fprintf(gclog, "Reclaimed %.2f%% (%zd) of %zd lines.\n", yield_percentage, num_lines_reclaimed, lines_tracked);

#endif

    approx_lines_allocated_since_last_collection = 0;
    return num_lines_reclaimed;
  }

  void describe_frame15s_count(const char* start, size_t f15s) {
    auto h = foster::humanize_s(double(f15s) * (1 << 15), "B");
    fprintf(gclog, "%s: %6zd f15s == %s\n", start, f15s, h.c_str());
  }

  // Returns the number of reclaimed lines from the line group.
  int inspect_lines_postgc(used_linegroup& g) {
    // Iterate through the lines, collecting groups of used lines.
    // Free line groups need not be explicitly constructed; they will
    // be reconstructed on demand by the global allocator.
    used_linegroup ug = { .base = g.base, .count = 0 };
    bool was_free = false;
    int num_marked_lines = 0;
    uint8_t* linemap = linemap_for_frame15_id(frame15_id_of(g.base));

    if (GCLOG_PRINT_USED_GROUPS) {
      display_used_linegroup_linemap(&g, linemap);
    }

    free_linegroup* fg = nullptr; // TODO remove?

    if (g.count > IMMIX_LINES_PER_FRAME15) {
      fprintf(gclog, "OOPS: watch *%p\n", &g.count);
    }
    for (int i = 0; i < g.count; ++i) {
      bool is_marked = line_is_marked(g.startline() + i, linemap);
      if (is_marked) {
        ++num_marked_lines;

        if (was_free) { // start new used group
          fg = nullptr;
          if (ug.count > 0) {
            tracking.note_used_group(ug); // return used group
          }
          ug.base = offset(g.base, i * IMMIX_BYTES_PER_LINE);
          ug.count = 1;
        } else { // continue used group
          ug.count++;
        }
      } else {
        if (!was_free) {
          // start new free group
          fg = (free_linegroup*) offset(g.base, i * IMMIX_BYTES_PER_LINE);
          fg->bound = offset(fg, IMMIX_BYTES_PER_LINE);
        } else {
          // continue free group
          fg->bound = offset(fg->bound, IMMIX_BYTES_PER_LINE);
        }

        if (GCLOG_DETAIL > 2) {
          fprintf(gclog, "gc %d: INFO: clearing contents of line %d of frame %u @ %p; space=%p\n",
              gcglobals.num_gcs_triggered,
            line_offset_within_f15(offset(g.base, i * IMMIX_BYTES_PER_LINE)),
            frame15_id_of(offset(g.base, i * IMMIX_BYTES_PER_LINE)),
            offset(g.base, i * IMMIX_BYTES_PER_LINE), this);
        }
        if (MEMSET_FREED_MEMORY) {
          // Be careful not to overwrite the metadata in `fg` that we just computed!
          memset(offset(g.base, (i * IMMIX_BYTES_PER_LINE) + sizeof(free_linegroup)),
                 0xdf,
                 IMMIX_BYTES_PER_LINE - sizeof(free_linegroup));
        }
        // Nothing to do!
      }
      was_free = !is_marked;
    }
    
    if (ug.count > 0) {
      tracking.note_used_group(ug); // return used group
    }

    gcglobals.condemned_set.lines_live += num_marked_lines;
    auto num_available_lines = g.count - num_marked_lines;

    return num_available_lines;

  }

private:
  // These bumpers point into particular frame15s.
  bump_allocator small_bumper;
  bump_allocator medium_bumper;

  large_array_allocator laa;

  immix_space_tracking tracking;
 
  uint64_t approx_lines_allocated_since_last_collection;
  // immix_space_end
};

void condemned_set::prepare_for_tracing() {
  gcglobals.allocator->prepare_for_tracing();
}

int64_t condemned_set::sweep_condemned(
             clocktimer<false>& phase, int64_t* num_lines_tracked, int64_t* num_groups_tracked) {
  int64_t num_lines_reclaimed = 0;
  
  num_lines_reclaimed += gcglobals.allocator->immix_sweep(phase, num_lines_tracked, num_groups_tracked);

  // Handles (and other unframed allocations) must be unmarked too.
  for (auto c : unframed_and_marked) {
    //fprintf(gclog, "Unmarking unframed object %p\n", c);
    do_unmark_granule(c);
  }
  unframed_and_marked.clear();

  return num_lines_reclaimed;
}

void process_worklists() {
  if (GCLOG_DETAIL > 0) { fprintf(gclog, "Before processing, had %zd conservative roots\n", conservative_roots.size()); }

  for (auto tidyptr : conservative_roots) {
    auto obj = heap_cell::for_tidy(reinterpret_cast<tidy*>(tidyptr));
    #if DEBUG_VERIFY_MARK_BITS
      g_marked_this_cycle.insert(obj);
    #endif
    immix_common::scan_cell(obj);
  }
  conservative_roots.clear();

  if (GCLOG_DETAIL > 0) { fprintf(gclog, "DONE PROCESSING CONSERVATIVE ROOTS.\n"); }
  immix_worklist.drain();
  if (GCLOG_DETAIL > 0) { fprintf(gclog, "After processing, had %zd conservative roots\n", conservative_roots.size()); }
}

void immix_worklist_t::drain() {
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

    tori* body = unchecked_ptr_val(*root);
    // ASSUMPTION: no language-level interior pointers
    heap_cell* obj = heap_cell::for_tidy(reinterpret_cast<tidy*>(body));

    if (GCLOG_DETAIL > 2) {
      fprintf(gclog, "gc %d: root %p contains object %p (body %p) (line %d of frame %u) with header %zx\n",
          gcglobals.num_gcs_triggered,
          root, obj, body,
          line_offset_within_f15(root),
                  frame15_id_of(root)
          , obj->raw_header()
          );
    }

    if (obj->is_forwarded()) {
      // fprintf(gclog, "worklist.process: root=%p, body = %p, obj = %p, header=%zx\n", root, body, obj, obj->raw_header()); fflush(gclog);
      *root = make_unchecked_ptr((tori*) obj->get_forwarded_body());
    } else if (obj_is_marked(obj)) {
#if DEBUG_VERIFY_MARK_BITS
      if (g_marked_this_cycle.count(obj) == 0) {
        fprintf(gclog, "WARN: mark bits not properly cleared for obj %p (body %p granule %zd)\n", obj, body, global_granule_for(obj->body_addr()));
        fprintf(stderr, "WARN: mark bits not properly cleared for obj %p (body %p granule %zd)\n", obj, body, global_granule_for(obj->body_addr())); fflush(stderr);
        g_marked_this_cycle.insert(obj);
      }
#endif
      // Skip marked objects.
      //fprintf(gclog, "gc %d: skipping marked object cell %p\n", gcglobals.num_gcs_triggered, obj);
    } else {
#if DEBUG_VERIFY_MARK_BITS
      g_marked_this_cycle.insert(obj);
#endif
      immix_common::immix_trace(root, obj);
    }
  }
  initialize();
}

// Refresher: on x86, stack frames look like this,
// provided we've told LLVM to disable frame pointer elimination:
// 0x0
//      ........
//    |-----------|
//    |local vars | <- top of stack
//    |saved regs |
//    |   etc     |
//    |-----------|
// +--| prev ebp  | <-- %ebp
// |  |-----------|
// |  | ret addr  | (PUSHed by call insn)
// |  |-----------|
// |  | fn params |
// v  | ......... |
//
// 0x7f..ff (kernel starts at 0x80....)
//
// Each frame pointer stores the address of the previous
// frame pointer.
struct frameinfo { frameinfo* frameptr; void* retaddr; };

// {{{ Walks the call stack and inserts roots into immix_worklist.
void collect_roots_from_stack(void* start_frame) {
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
  // If we were willing to accept a dependency on libgcc,
  // we could use the _Unwind_Backtrace function.
  frameinfo* frame = (frameinfo*) start_frame;
  int i = 0;
  while (true) {
    frameinfo* base = frame;
    frameinfo* next = frame->frameptr;

    // Iterate over all (aligned) potential root slots in the frame.
    void* lower = std::min(base, next);
    void* upper = std::max(base, next);

    // The bottom-most frame of a coroutine stack will have an invalid
    // frame pointer; when we see it, we can bail out.
    const size_t oversized_frame = 1 << 18;
    if (!base || !next || distance(lower, upper) >= oversized_frame) { break; }

    while (lower <= upper) {
      //fprintf(gclog, "considering potential root %p in frame %d\n", lower, i);
      helpers::consider_conservative_root((unchecked_ptr*) lower);
      lower = offset(lower, sizeof(void*));
    }

    ++i;
    frame = next;
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

extern "C" void* opaquely_ptr(void*);

void initialize(void* stack_highest_addr) {
  gcglobals.init_start.start();
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  pages_boot();

  void* malloced = malloc(1);
  if (non_markable_addr_toosmall(malloced)) {
    fprintf(stderr, "ERROR: Foster runtime appears to have been misconfigured;"
                    " malloc() returned an address (%p) that the runtime will not mark.", malloced);
    exit(2);
  }
  free(malloced);


  gcglobals.lazy_mapped_markable_handles        = (void**) allocate_lazily_zero_mapped<heap_handle<immix_space> >(1 << 20);
  // First entry reserved for free list.
  (*gcglobals.lazy_mapped_markable_handles) = offset(gcglobals.lazy_mapped_markable_handles, sizeof(heap_handle<immix_space>));

  gcglobals.lazy_mapped_frame15info             = allocate_lazily_zero_mapped<frame15info>(     size_t(1) << (address_space_prefix_size_log() - 15));

  gcglobals.lazy_mapped_granule_marks           = allocate_lazily_zero_mapped<uint8_t>(lazy_mapped_granule_marks_size()); // byte marks
  gcglobals.lazy_mapped_granule_validity        = allocate_lazily_zero_mapped<uint8_t>(lazy_mapped_granule_marks_size());
  gcglobals.lazy_mapped_frame_liveness          = allocate_lazily_zero_mapped<uint16_t>(     size_t(1) << (address_space_prefix_size_log() - 15));
  gcglobals.lazy_mapped_line_marks              = allocate_lazily_zero_mapped<uint8_t>(      size_t(1) << (address_space_prefix_size_log() - IMMIX_LINE_SIZE_LOG));
  gcglobals.lazy_mapped_line_pins               = allocate_lazily_zero_mapped<uint8_t>(      size_t(1) << (address_space_prefix_size_log() - IMMIX_LINE_SIZE_LOG));
  

  global_space_allocator.grow_heap_by(gSEMISPACE_SIZE());
  gcglobals.allocator = new immix_space();

  gcglobals.had_problems = false;
  gcglobals.logall = false;

  gcglobals.gc_time_us = 0.0;
  gcglobals.num_gcs_triggered = 0;
  gcglobals.num_big_stackwalks = 0;
  gcglobals.num_allocations = 0;
  gcglobals.num_alloc_bytes = 0;
  gcglobals.write_barrier_phase0_hits = 0;
  gcglobals.write_barrier_phase0b_hits = 0;
  gcglobals.write_barrier_phase1_hits = 0;
  gcglobals.write_barrier_phase1g_hits = 0;
  gcglobals.num_objects_marked_total = 0;
  gcglobals.alloc_bytes_marked_total = 0;
  gcglobals.max_bytes_live_at_whole_heap_gc = 0;
  gcglobals.num_closure_calls = 0;

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
  fprintf(json, ",");
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

int nrecorded = 0;
FILE* print_timing_stats() {
  auto total_elapsed = gcglobals.init_start.elapsed_s();
  auto gc_elapsed = gcglobals.gc_time_us / 1e6;
  auto mut_elapsed = total_elapsed - gc_elapsed;

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
    if (ENABLE_GC_TIMING) {
      fprintf(gclog, "hist_gc_pause_micros:\n");
      foster_hdr_percentiles_print(gcglobals.hist_gc_pause_micros, gclog, 4);
    }

    fprintf(gclog, "gc_stackscan_roots:\n");
    foster_hdr_percentiles_print(gcglobals.hist_gc_stackscan_roots, gclog, 4);
  }

  fflush(gclog);

  dump_alloc_site_stats(gclog);

  fprintf(gclog, "'Num_Big_Stackwalks': %d\n", gcglobals.num_big_stackwalks);
  fprintf(gclog, "'Num_GCs_Triggered': %d\n", gcglobals.num_gcs_triggered);
  if (TRACK_NUM_ALLOCATIONS) {
    auto s = foster::humanize_s(double(gcglobals.num_allocations), "");
    fprintf(gclog, "'Num_Allocations': %s\n", s.c_str());
  }
  if (TRACK_NUM_ALLOC_BYTES) {
    auto s = foster::humanize_s(double(gcglobals.num_alloc_bytes), "B");
    fprintf(gclog, "'Num_Alloc_Bytes': %s\n", s.c_str());
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
  {
    auto s = foster::humanize_s(gcglobals.num_closure_calls, "");
    fprintf(gclog, "'Num_Closure_Calls': %s\n", s.c_str());
  }

  fprintf(gclog, "'FosterlowerConfig': %s\n", (const char*)&__foster_fosterlower_config);
  fprintf(gclog, "'FosterGCConfig': {'FifoSize': %d}\n", USE_FIFO_SIZE);

  fprintf(gclog, "sizeof immix_space: %lu\n", sizeof(immix_space));
  fprintf(gclog, "sizeof bump_allocator: %lu\n", sizeof(bump_allocator));
  fprintf(gclog, "sizeof large_array_allocator: %lu\n", sizeof(large_array_allocator));
  fprintf(gclog, "sizeof immix_space_tracking: %lu\n", sizeof(immix_space_tracking));

  fprintf(gclog, "# recorded allocs: %d\n", nrecorded);

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

  if (!gcglobals.typemap_memory.contains((void*) map)) {
    return nullptr;
  }

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

void record_memalloc_cell(void* cell, typemap* typeinfo, const char* srcloc, const char* typedesc) {
  nrecorded++;
  if (gcglobals.num_gcs_triggered < 10) {
    fprintf(gclog, "recorded memalloc cell %p with typeinfo %p and and srcloc %s and typedesc %s\n", cell, typeinfo, srcloc, typedesc);
  }
  gcglobals.alloc_site_counters[std::make_pair(typedesc, typeinfo)]++;
  gcglobals.alloc_site_locs[cell] = std::make_pair(srcloc, typedesc);
}
// }}}

// Extern symbol for gdb, not direct use by generated code.
void fflush_gclog() { fflush(gclog); }

__attribute__((noinline)) // this attribute will be removed once the barrier optimizer runs.
void foster_read_pseudobarrier(void* base, void** slot) {
  heap_cell* obj = heap_cell::for_tidy(reinterpret_cast<tidy*>(base));
  fprintf(gclog, "gcread() of slot %p in cell %p (base %p) with mark status = %d\n", slot, obj, base, obj_is_marked(obj));
}

__attribute__((noinline)) // this attribute will be removed once the barrier optimizer runs.
void foster_write_barrier_with_obj_generic(void* val, void* obj, void** slot) {
  *slot = val;

  if (TRACK_WRITE_BARRIER_COUNTS > 3) { ++gcglobals.write_barrier_phase0_hits; }
  if (non_markable_addr_toosmall_or_taggedInt(val)) { return; }
  if (TRACK_WRITE_BARRIER_COUNTS > 3) { ++gcglobals.write_barrier_phase0b_hits; }
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

