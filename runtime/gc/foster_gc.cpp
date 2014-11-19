// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "foster_globals.h"
#include "stat_tracker.h"

#include "base/time.h" // for TimeTicks, TimeDelta
#include "base/metrics/histogram.h"
#include "base/metrics/statistics_recorder.h"
#ifdef FOSTER_MULTITHREADED
#include "base/threading/platform_thread.h"
#endif

#include <sys/resource.h> // for getrlimit, RLIMIT_STACK
#include "execinfo.h" // for backtrace

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)

// These are defined as compile-time constants so that the compiler
// can do effective dead-code elimination. If we were JIT compiling
// the GC we could (re-)specialize these config vars at runtime...
#define ENABLE_GCLOG 0
#define FOSTER_GC_ALLOC_HISTOGRAMS    0
#define GC_ASSERTIONS 0
#define TRACK_NUM_ALLOCATIONS         1
#define TRACK_BYTES_KEPT_ENTRIES      0
#define TRACK_BYTES_ALLOCATED_ENTRIES 0
#define GC_BEFORE_EVERY_MEMALLOC_CELL 0
#define DEBUG_INITIALIZE_ALLOCATIONS  0
// This included file may un/re-define these parameters, providing
// a way of easily overriding-without-overwriting the defaults.
#include "gc/foster_gc_reconfig-inl.h"

const int kFosterGCMaxDepth = 1024;
const int inline gSEMISPACE_SIZE() { return __foster_globals.semispace_size; }

const bool wantWeirdCrashToHappen = false;

/////////////////////////////////////////////////////////////////

#include "foster_gc_utils.h"

#include <sstream>
#include <list>
#include <vector>
#include <map>

namespace foster {
namespace runtime {
namespace gc {

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

struct allocator_range {
  memory_range range;
  bool         stable;
};
// }}}

// {{{ Global data used by the GC
FILE* gclog = NULL;

class copying_gc;
copying_gc* allocator = NULL;

std::vector<allocator_range> allocator_ranges;

// TODO de-globalize these
base::TimeTicks gc_time;
base::TimeTicks runtime_start;
base::TimeTicks    init_start;

typedef void* ret_addr;
typedef void* frameptr;
typedef std::map<frameptr, const stackmap::PointCluster*> ClusterMap;
ClusterMap clusterForAddress;
// }}}

// {{{ Internal utility functions
void gc_assert(bool cond, const char* msg) {
  if (GC_ASSERTIONS) {
    foster_assert(cond, msg);
  }
}

bool is_marked_as_stable(tidy* body) {
  for (int i = 0, j = allocator_ranges.size(); i < j; ++i) {
    if (allocator_ranges[i].range.contains((void*) body)) {
      return allocator_ranges[i].stable;
    }
  }
  return false;
}

inline bool
isCoroBelongingToOtherThread(const typemap* map, heap_cell* cell) {
  #ifdef FOSTER_MULTITHREADED
  if (map->isCoro) {
    foster_generic_coro* coro = (foster_generic_coro*) cell->body_addr();
    if (coro_status(coro) == FOSTER_CORO_RUNNING) {
      // Don't scan a coroutine if it's being run by another thread!
      if (coro_owner_thread(coro) != PlatformThread::CurrentId()) {
        return true;
      }
    }
  }
  #endif

  return false;
}
// }}}

////////////////////////////////////////////////////////////////////

// {{{
void inspect_typemap(const typemap* ti);

void scanCoroStack(foster_generic_coro* coro, gc_visitor_fn visitor);
// }}}

// {{{ copying_gc
class copying_gc {
  class semispace {
  public:
      semispace(int64_t size, copying_gc* parent) : parent(parent) {
        range.base  = malloc(size);
        range.bound = offset(range.base, size);
        reset_bump();
        memset(range.base, 0x66, size);

        genericClosureMarker = NULL;
      }

      ~semispace() {
        free(range.base);
      }

  private:
      memory_range range;
      void* bump;
      copying_gc* parent;

      char* genericClosureMarker;

  public:
      void realign_bump() {
         bump = offset(
                roundUpToNearestMultipleWeak(offset(bump, HEAP_CELL_HEADER_SIZE),
                                             FOSTER_GC_DEFAULT_ALIGNMENT)
                                                         ,HEAP_CELL_HEADER_SIZE);
      }
      void reset_bump() {
        // We want to position the bump pointer far enough into the buffer
        // so that after accounting for the heap cell header, the body pointer
        // resulting from allocation will be properly aligned.
        bump = range.base;
        realign_bump();
        fprintf(gclog, "after reset, bump = %p, low bits: %x\n", bump,
                                                    int(intptr_t(bump) & 0xf));
      }

      bool contains(void* ptr) const { return range.contains(ptr); }

      void clear() {
        fprintf(gclog, "clearing mem from %p to %p, bump = %p\n", range.base, range.bound, bump);
        fflush(gclog);
        memset(range.base, 0xFE, range.size());
      }

      int64_t used_size() const { return distance(range.base, bump); }
      int64_t free_size() const {
        //fprintf(gclog, "this=%p, bump = %p, low bits: %x\n", this, bump, intptr_t(bump) & 0xf);
        //fflush(gclog);
        return distance(bump, range.bound);
      }

      bool can_allocate_bytes(int64_t num_bytes) {
        return free_size() > num_bytes;
      }

      void allocate_cell_prechecked_histogram(int N) {
        if (N > 128) {
          HISTOGRAM_CUSTOM_COUNTS("gc-alloc-large", N, 129, 33000000, 50);
        } else {
          HISTOGRAM_ENUMERATION("gc-alloc-small", N, 128);
        }
      }

      // {{{ Prechecked allocation functions
      template <int N>
      tidy* allocate_cell_prechecked_N(typemap* typeinfo) {
        heap_cell* allot = (heap_cell*) bump;
        //fprintf(gclog, "this=%p, memsetting %d bytes at %p (ti=%p)\n", this, int(typeinfo->cell_size), bump, typeinfo); fflush(gclog);
        if (DEBUG_INITIALIZE_ALLOCATIONS) { memset(bump, 0xAA, N); }
        if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(N); }
        if (TRACK_NUM_ALLOCATIONS) { ++parent->num_allocations; }
        if (FOSTER_GC_ALLOC_HISTOGRAMS) { HISTOGRAM_ENUMERATION("gc-alloc-small", N, 128); }
        incr_by(bump, N);
        allot->set_meta(typeinfo);
        //fprintf(gclog, "alloc'd %d, bump = %p, low bits: %x\n", int(typeinfo->cell_size), bump, intptr_t(bump) & 0xF);
        return allot->body_addr();
      }

      tidy* allocate_cell_prechecked(typemap* typeinfo) {
        heap_cell* allot = (heap_cell*) bump;
        //fprintf(gclog, "this=%p, memsetting %d bytes at %p (ti=%p)\n", this, int(typeinfo->cell_size), bump, typeinfo); fflush(gclog);
        if (DEBUG_INITIALIZE_ALLOCATIONS) { memset(bump, 0xAA, typeinfo->cell_size); }
        if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(typeinfo->cell_size); }
        if (TRACK_NUM_ALLOCATIONS) { ++parent->num_allocations; }
        if (!wantWeirdCrashToHappen && FOSTER_GC_ALLOC_HISTOGRAMS) {
          allocate_cell_prechecked_histogram((int) typeinfo->cell_size);
        }
        incr_by(bump, typeinfo->cell_size);
        allot->set_meta(typeinfo);
        //fprintf(gclog, "alloc'd %d, bump = %p, low bits: %x\n", int(typeinfo->cell_size), bump, intptr_t(bump) & 0xF);
        return allot->body_addr();
      }

      tidy* allocate_array_prechecked(typemap* arr_elt_typeinfo,
                                      int64_t  num_elts,
                                      int64_t  total_bytes,
                                      bool     init) {
        heap_array* allot = (heap_array*) bump;
        if (init) memset(bump, 0x00, total_bytes);
        incr_by(bump, total_bytes);
        //fprintf(gclog, "alloc'a %d, bump = %p, low bits: %x\n", int(total_bytes), bump, intptr_t(bump) & 0xF);
        allot->set_meta(arr_elt_typeinfo);
        allot->set_num_elts(num_elts);
        if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(total_bytes); }
        if (TRACK_NUM_ALLOCATIONS) { ++parent->num_allocations; }
        return allot->body_addr();
      }
      // }}}

      // {{{ metadata helpers
      inline void get_cell_metadata(heap_cell* cell,
                                    const void*    & meta,
                                    heap_array*    & arr ,
                                    const typemap* & map,
                                    int64_t        & cell_size) {
        meta = cell->get_meta();
        gc_assert(meta != NULL, "cannot copy cell lacking metadata");

        if (isMetadataPointer(meta)) {
          map = (const typemap*) meta;
          if (ENABLE_GCLOG) { inspect_typemap(map); }

          if (map->isArray) {
            arr = heap_array::from_heap_cell(cell);
          }
        }

        get_cell_size(meta, arr, map, cell_size);
      }

      inline void get_cell_size(const void*      meta,
                                heap_array*      arr ,
                                const typemap*   map,
                                int64_t        & cell_size) {
        if (map) {
          if (arr) {
            cell_size = array_size_for(arr->num_elts(), map->cell_size);
            if (ENABLE_GCLOG) {
              fprintf(gclog, "Collecting array of total size %lld (rounded up from %lld + %lld = %lld), cell size %lld, len %lld...\n",
                                  cell_size,
                                  int64_t(sizeof(heap_array)),
                                                       arr->num_elts() * map->cell_size,
                                  sizeof(heap_array) + arr->num_elts() * map->cell_size,
                                  map->cell_size,
                                  arr->num_elts());
            }
          } else {
            // probably an actual pointer
            cell_size = map->cell_size;
          }
        } else {
          cell_size = int64_t(meta);
        }
      }
      // }}}

      // Invariant: cell is owned by the other semispace.
      // Returns body of newly allocated cell.
      tidy* ss_copy(heap_cell* cell, int remaining_depth) {
        tidy*       result = NULL;
        const void* meta = NULL;
        heap_array* arr = NULL;
        const typemap* map = NULL;
        int64_t cell_size;

        //fprintf(gclog, "cell meta for %p is %p\n", cell, cell->get_meta());

        if (cell->is_forwarded()) {
          goto return_result;
        }

        get_cell_metadata(cell, meta, arr, map, cell_size);

        // {{{ assertions etc
        gc_assert(cell_size >= 16, "cell size must be at least 16!");
        if (ENABLE_GCLOG) {
          fprintf(gclog, "copying cell %p, cell size %llu\n", cell, cell_size); fflush(gclog);
        }

        if (GC_ASSERTIONS) {
          // This should be an invariant, because we only copy data
          // into the semispace which already existed in the other semispace.
          if (!can_allocate_bytes(cell_size)) {
            printf("not enough space to copy!\n");
            printf("have %llu = 0x%llx\n", free_size(), (unsigned long long) free_size());
            printf("need %llu = 0x%llx\n", cell_size,   (unsigned long long) cell_size);
            exit(254);
          }
        }

        if (map) {
         if (isCoroBelongingToOtherThread(map, cell)) {
            // Don't copy or scan a coroutine if
            // it belongs to a different thread!
            return cell->body_addr();
          }
        }
        // }}}

        {
          heap_cell* new_addr = (heap_cell*) bump;
          incr_by(bump, cell_size);
          memcpy(new_addr, cell, cell_size);
          cell->set_forwarded_body(new_addr->body_addr());

          // Copy depth-first, but not so much that we blow the stack...
          if (remaining_depth > 0) {
            if (map) {
              if (arr) arr = heap_array::from_heap_cell(new_addr);
              scan_with_map_and_arr(new_addr, map, arr, remaining_depth - 1);
            }
          } else {
            parent->worklist.add(new_addr);
          }
        }

        return_result:
          result = cell->get_forwarded_body();
          if (ENABLE_GCLOG) {
            fprintf(gclog, "; replacing %p with %p\n", cell->body_addr(), result);
          }
          return result;
      } // end ss_copy


      // Invariant: map is not null
      void scan_with_map_and_arr(heap_cell* cell, const typemap* map,
                                 heap_array* arr, int depth) {
        //fprintf(gclog, "copying %lld cell %p, map np %d, name %s\n",
        //  cell_size, cell, map->numEntries, map->name); fflush(gclog);

        if (arr) {
          // TODO for byte arrays and such, we can skip this loop...
          int64_t numcells = arr->num_elts();
          for (int64_t cellnum = 0; cellnum < numcells; ++cellnum) {
            //fprintf(gclog, "num cells in array: %lld, curr: %lld\n", numcells, cellnum);
            scan_with_map(arr->elt_body(cellnum, map->cell_size), map, depth);
          }
        } else {
            scan_with_map(from_tidy(cell->body_addr()), map, depth);
        }

        if (map->isCoro) {
          foster_generic_coro* coro = (foster_generic_coro*) cell->body_addr();
          scanCoroStack(coro, copying_gc_root_visitor);
        }
      }


      // Invariant: map is not null
      void scan_with_map(intr* body, const typemap* map, int depth) {
        for (int i = 0; i < map->numOffsets; ++i) {
          parent->copy_or_update((unchecked_ptr*) offset(body, map->offsets[i]),
                                 depth);
        }
      }

      inline void scan_cell(heap_cell* cell, int depth) {
        const void* meta = NULL;
        heap_array* arr = NULL;
        const typemap* map = NULL;
        int64_t cell_size;
        get_cell_metadata(cell, meta, arr, map, cell_size);
        if (map) scan_with_map_and_arr(cell, map, arr, depth);
      }

  private:
      intr* from_tidy(tidy* t) { return (intr*) t; }
  };

  void record_bytes_allocated(int64_t num_bytes) {
    int64_t idx = num_bytes / FOSTER_GC_DEFAULT_ALIGNMENT;
    if (idx >= bytes_req_per_alloc.size() - 1) {
      bytes_req_per_alloc.back()++;
    } else {
      bytes_req_per_alloc[idx]++;
    }
  }

  // {{{ Copying GC data members

  // An efficiently-encoded int->int map...
  // A value of v at index k in [index 0..TRACK_BYTES_ALLOCATED_ENTRIES)
  // means v allocations of size (k * FOSTER_GC_DEFAULT_ALIGNMENT).
  // All larger allocations go in the last array entry.
  std::vector<int64_t>  bytes_req_per_alloc;

  stat_tracker<int64_t> bytes_kept_per_gc;

  std::map<std::pair<const char*, typemap*>, int64_t> alloc_site_counters;

  int64_t num_allocations;
  int64_t num_collections;
  bool saw_bad_pointer;

  semispace* curr;
  semispace* next;

  struct worklist {
      void       initialize()      { ptrs.clear(); idx = 0; }
      void       process(semispace* next);
      bool       empty()           { return idx >= ptrs.size(); }
      void       advance()         { ++idx; }
      heap_cell* peek_front()      { return ptrs[idx]; }
      void       add(heap_cell* c) { ptrs.push_back(c); }
    private:
      size_t                  idx;
      std::vector<heap_cell*> ptrs;
  };
  worklist worklist;

  // }}}

  void gc();

  // precondition: all active cells from curr have been copied to next
  void flip() {
    // re-align the next bump pointer so it'll be ready for us.
    next->realign_bump();
    // curr is the old semispace, so we reset its bump ptr
    curr->reset_bump();
    std::swap(curr, next);
  }

public:
  copying_gc(int64_t size) {
    // {{{
    curr = new semispace(size, this);

    // Allocate some temporary memory to force curr and next
    // to have visually distinct address ranges.
    std::vector<semispace*> stretches;
    for (int i = (4 * 1000 * 1000) / size; i >= 0; --i) {
      stretches.push_back(new semispace(size, this));
    }
    next = new semispace(size, this);
    for (int i = 0; i < stretches.size(); --i) {
      delete stretches[i]; stretches[i] = NULL;
    }

    num_allocations = 0;
    num_collections = 0;
    saw_bad_pointer = false;
    bytes_kept_per_gc.resize(TRACK_BYTES_KEPT_ENTRIES);
    bytes_req_per_alloc.resize(TRACK_BYTES_ALLOCATED_ENTRIES + 1);
    // }}}
  }

  ~copying_gc() {
    dump_stats(NULL);
  }

  void dump_stats(FILE* json) {
    // {{{
    FILE* stats = json ? json : gclog;

    double approx_bytes = double(num_collections * gSEMISPACE_SIZE());
    fprintf(stats, "'num_collections' : %" PRId64 ",\n", num_collections);
    if (TRACK_NUM_ALLOCATIONS) {
    fprintf(stats, "'num_allocations' : %.3g,\n", double(num_allocations));
    fprintf(stats, "'avg_alloc_size' : %d,\n", (num_allocations == 0)
                                                  ? 0
                                                  : int(approx_bytes / double(num_allocations)));
    }
    fprintf(stats, "'alloc_num_bytes_gt' : %.3g,\n", approx_bytes);
    fprintf(stats, "'semispace_size_kb' : %d,\n", gSEMISPACE_SIZE() / 1024);

    if (TRACK_BYTES_KEPT_ENTRIES) {
    int64_t mn = bytes_kept_per_gc.compute_min(),
            mx = bytes_kept_per_gc.compute_max(),
            aa = bytes_kept_per_gc.compute_avg_arith();
    fprintf(stats, "'min_bytes_kept' : %8" PRId64 ",\n", mn);
    fprintf(stats, "'max_bytes_kept' : %8" PRId64 ",\n", mx);
    fprintf(stats, "'avg_bytes_kept' : %8" PRId64 ",\n", aa);
    fprintf(stats, "'min_bytes_kept_percent' : %.2g%%,\n", double(mn * 100.0)/double(gSEMISPACE_SIZE()));
    fprintf(stats, "'max_bytes_kept_percent' : %.2g%%,\n", double(mx * 100.0)/double(gSEMISPACE_SIZE()));
    fprintf(stats, "'avg_bytes_kept_percent' : %.2g%%,\n", double(aa * 100.0)/double(gSEMISPACE_SIZE()));
    }
    if (TRACK_BYTES_ALLOCATED_ENTRIES) {
      for (int i = 0; i < bytes_req_per_alloc.size() - 1; ++i) {
        int sz = i * FOSTER_GC_DEFAULT_ALIGNMENT;
        fprintf(stats, "allocs_of_size_%4d: %12" PRId64 ",\n", sz, bytes_req_per_alloc[i]);
      }
      fprintf(stats,  "allocs_of_size_more: %12" PRId64 ",\n", bytes_req_per_alloc.back());
    }

    if (!this->alloc_site_counters.empty()) {
      fprintf(stats, "'allocation_sites' : [\n");
      std::map<std::pair<const char*, typemap*>, int64_t>::iterator it;
      for (it  = this->alloc_site_counters.begin();
            it != this->alloc_site_counters.end(); ++it) {
        fprintf(stats, "{ 'typemap' : %p , 'allocations' : %12" PRId64 ",\n", it->first.second, it->second);
        fprintf(stats, "  'from' : \"%s\" },\n", it->first.first);
      }
      fprintf(stats, "],\n");
    }
    // }}}

  }

  bool had_problems() { return saw_bad_pointer; }

  void force_gc_for_debugging_purposes() { this->gc(); }

  void record_memalloc_cell(typemap* typeinfo, const char* srclines) {
    this->alloc_site_counters[std::make_pair(srclines, typeinfo)]++;
  }

  // Jones/Hosking/Moss refer to this function as "process(fld)".
  void copy_or_update(unchecked_ptr* root, int depth) {
    //       |------------|            |------------|
    // root: |    body    |---\        |  size/meta |
    //       |------------|   |        |------------|
    //                        \------> |            |
    //                                ...          ...
    //                                 |            |
    //                                 |------------|
    unchecked_ptr body_ = *root;
    if (is_null(body_)) return;
    tidy* body = untag(body_);

    heap_cell* obj = heap_cell::for_body(body);
    if (curr->contains(body)) {
      *root = make_unchecked_ptr(next->ss_copy(obj, depth));

      gc_assert(!is_null(*root),        "copying gc should not null out slots");
      gc_assert(body  != untag(*root) , "copying gc should return new pointers");
    } else if (is_marked_as_stable(body)) {
      next->scan_cell(obj, depth);
    } else {
      // {{{ Should-never-happen error handling...
      if (next->contains(obj)) {
        fprintf(gclog, "foster_gc error: tried to collect"
                       " cell in next-semispace: %p\n", obj);
        fflush(gclog);
        fprintf(gclog, "\t\twith meta %p\n", obj->get_meta());
        fflush(gclog);
        exit(254);
        //return false;
      } else {
        fprintf(gclog, "foster_gc error: tried to collect"
                       " unknown cell: %p\n", obj);
        fflush(gclog);
        saw_bad_pointer = true;
      }
      // }}}
    }
  }

  // {{{ Allocation, in various flavors & specializations.
  void* allocate_cell(typemap* typeinfo) {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.

    if (wantWeirdCrashToHappen && FOSTER_GC_ALLOC_HISTOGRAMS) {
        // odd -- having this code here seems to cause llvm to miscompile
        // this function (it removes the bounds check from can_allocate_bytes)
        // at high optimzation levels, but only if we do inlining in foster-me,
        // and if we don't do it in allocate_cell_prechecked
        // ... wtf is going on???
        curr->allocate_cell_prechecked_histogram(17);
    }

    if (curr->can_allocate_bytes(cell_size)) {
      return curr->allocate_cell_prechecked(typeinfo);
    } else {
      return allocate_cell_slowpath(typeinfo);
    }
  }

  template <int N>
  void* allocate_cell_N(typemap* typeinfo) {
    if (curr->can_allocate_bytes(N)) {
      return curr->allocate_cell_prechecked_N<N>(typeinfo);
    } else {
      return allocate_cell_slowpath(typeinfo);
    }
  }

  void* allocate_cell_slowpath(typemap* typeinfo) {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.
    gc();
    if (curr->can_allocate_bytes(cell_size)) {
      fprintf(gclog, "gc collection freed space for cell, now have %lld\n", curr->free_size());
      fflush(gclog);
      return curr->allocate_cell_prechecked(typeinfo);
    } else {
      fprintf(gclog, "working set exceeded heap size! aborting...\n"); fflush(gclog);
      exit(255); // TODO be more careful if we're allocating from a coro...
      return NULL;
    }
  }

  static inline int64_t array_size_for(int64_t n, int64_t slot_size) {
    return roundUpToNearestMultipleWeak(sizeof(heap_array) + n * slot_size,
                                        FOSTER_GC_DEFAULT_ALIGNMENT);
  }

  void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) {
    int64_t slot_size = elt_typeinfo->cell_size; // note the name change!
    int64_t req_bytes = array_size_for(n, slot_size);

    if (false && FOSTER_GC_ALLOC_HISTOGRAMS) {
      HISTOGRAM_CUSTOM_COUNTS("gc-alloc-array", (int) req_bytes, 1, 33000000, 128);
    }

    if (curr->can_allocate_bytes(req_bytes)) {
      return curr->allocate_array_prechecked(elt_typeinfo, n, req_bytes, init);
    } else {
      gc();
      if (curr->can_allocate_bytes(req_bytes)) {
        fprintf(gclog, "gc collection freed space for array, now have %lld\n", curr->free_size());
        fflush(gclog);
        return curr->allocate_array_prechecked(elt_typeinfo, n, req_bytes, init);
      } else {
        fprintf(gclog, "working set exceeded heap size! aborting...\n"); fflush(gclog);
        exit(255); // TODO be more careful if we're allocating from a coro...
        return NULL;
      }
    }
  }
  // }}}
}; // copying_gc
// }}}

// This function statically references the global allocator.
// Eventually we'll want a generational GC with thread-specific
// allocators and (perhaps) type-specific allocators.
void copying_gc_root_visitor(unchecked_ptr* root, const typemap* slotname) {
  gc_assert(root != NULL, "someone passed a NULL root addr!");
  if (ENABLE_GCLOG) {
    fprintf(gclog, "\t\tSTACK SLOT %p contains %p, slot name = %s\n", root,
                      unchecked_ptr_val(*root),
                      (slotname ? ((const char*) slotname) : "<unknown slot>"));
  }
  allocator->copy_or_update(root, kFosterGCMaxDepth);
}

extern "C" foster_generic_coro** __foster_get_current_coro_slot();

void copying_gc::gc() {
  //fprintf(stdout, "gc();\n");
  //fprintf(stderr, "gc();\n");
  base::TimeTicks begin = base::TimeTicks::HighResNow();
  ++this->num_collections;
  if (ENABLE_GCLOG) {
    fprintf(gclog, ">>>>>>> visiting gc roots on current stack\n"); fflush(gclog);
  }

  worklist.initialize();

  visitGCRootsWithStackMaps(__builtin_frame_address(0),
                            copying_gc_root_visitor);

  foster_generic_coro** coro_slot = __foster_get_current_coro_slot();
  foster_generic_coro*  coro = *coro_slot;
  if (coro) {
    if (ENABLE_GCLOG) {
      fprintf(gclog, "==========visiting current ccoro: %p\n", coro); fflush(gclog);
    }
    copying_gc_root_visitor((unchecked_ptr*)coro_slot, NULL);
    if (ENABLE_GCLOG) {
      fprintf(gclog, "==========visited current ccoro: %p\n", coro); fflush(gclog);
    }
  }

  worklist.process(next);

  if (TRACK_BYTES_KEPT_ENTRIES) {
    bytes_kept_per_gc.record_sample(next->used_size());
  }

  flip();
  next->clear(); // for debugging purposes

  if (ENABLE_GCLOG) {
    fprintf(gclog, "\t/gc\n\n");
    fflush(gclog);
  }

  gc_time += (base::TimeTicks::HighResNow() - begin);
}

void copying_gc::worklist::process(copying_gc::semispace* next) {
  while (!empty()) {
    heap_cell* cell = peek_front();
    advance();
    next->scan_cell(cell, kFosterGCMaxDepth);
  }
}

void register_stackmaps(ClusterMap&);

size_t get_default_stack_size() {
  struct rlimit rlim;
  getrlimit(RLIMIT_STACK, &rlim);
  //gc_assert(rlim.rlim_cur != RLIM_INFINITY);
  // TODO: account for stack space already being used?
  return (size_t) rlim.rlim_cur;
}

// {{{ get_static_data_range
#if OS_LINUX
// http://stackoverflow.com/questions/4308996/finding-the-address-range-of-the-data-segment
extern "C" char etext, end;
void get_static_data_range(memory_range& r) {
  r.base  = &etext;
  r.bound = &end;
}
#elif OS_MACOSX
// http://stackoverflow.com/questions/1765969/unable-to-locate-definition-of-etext-edata-end
#include <mach-o/getsect.h>
void get_static_data_range(memory_range& r) {
  r.base  = (void*) get_etext();
  r.bound = (void*) get_end();
}
#else
#error TODO: Use Win32 to find boundaries of data segment range.
#endif
// }}}

// {{{ GC startup & shutdown
void initialize(void* stack_highest_addr) {
  init_start = base::TimeTicks::HighResNow();
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  base::StatisticsRecorder::Initialize();
  allocator = new copying_gc(gSEMISPACE_SIZE());

  // ASSUMPTION: stack segments grow down, and are linear...
  size_t stack_size = get_default_stack_size();
  allocator_range ar;
  ar.range.bound = stack_highest_addr;
  ar.range.base  = (void*) (((char*) ar.range.bound) - stack_size);
  ar.stable = true;
  allocator_ranges.push_back(ar);

  allocator_range datarange;
  get_static_data_range(datarange.range);
  datarange.stable = true;
  allocator_ranges.push_back(datarange);

  register_stackmaps(clusterForAddress);

  gc_time = base::TimeTicks();
  runtime_start = base::TimeTicks::HighResNow();
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

// TODO: track bytes allocated, bytes clollected, max heap size,
//       max slop (alloc - reserved), peak mem use; compute % GC time.

int cleanup() {
  base::TimeTicks fin = base::TimeTicks::HighResNow();
  base::TimeDelta total_elapsed = fin - init_start;
  base::TimeDelta  init_elapsed = runtime_start - init_start;
  base::TimeDelta    gc_elapsed = gc_time - base::TimeTicks();
  base::TimeDelta   mut_elapsed = total_elapsed - gc_elapsed - init_elapsed;
  FILE* json = __foster_globals.dump_json_stats_path.empty()
                ? NULL
                : fopen(__foster_globals.dump_json_stats_path.c_str(), "w");
  if (json) fprintf(json, "{\n");
  gclog_time("Elapsed_runtime", total_elapsed, json);
  gclog_time("Initlzn_runtime",  init_elapsed, json);
  gclog_time("     GC_runtime",    gc_elapsed, json);
  gclog_time("Mutator_runtime",   mut_elapsed, json);
  if (FOSTER_GC_ALLOC_HISTOGRAMS) {
    fprintf(gclog, "stats recorder active? %d\n", base::StatisticsRecorder::IsActive());
    std::string output;
    base::StatisticsRecorder::WriteGraph("", &output);
    fprintf(gclog, "%s\n", output.c_str());
  }
  bool had_problems = allocator->had_problems();
  if (json) allocator->dump_stats(json);
  delete allocator;
  fclose(gclog); gclog = NULL;
  if (json) fprintf(json, "}\n");
  if (json) fclose(json);
  return had_problems ? 99 : 0;
}
// }}}

#include "foster_gc_backtrace_x86-inl.h"

// {{{ ``mapM visitor (callStackFromAddr start_frame)``
// Note that ``visitor`` is ``copying_gc_root_visitor`` which just forwards
// to the copy_or_update() method of the global ``allocator`` pointer.
void visitGCRootsWithStackMaps(void* start_frame,
                               gc_visitor_fn visitor) {
  enum { MAX_NUM_RET_ADDRS = 1024 };
  // Garbage collection requires 16+ KB of stack space due to these arrays.
  ret_addr  retaddrs[MAX_NUM_RET_ADDRS];
  frameinfo frames[MAX_NUM_RET_ADDRS];

  // Collect frame pointers and return addresses
  // for the current call stack.
  int nFrames = foster_backtrace((frameinfo*) start_frame, frames, MAX_NUM_RET_ADDRS);

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

    const stackmap::PointCluster* pc = clusterForAddress[safePointAddr];
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

      visitor((unchecked_ptr*) rootaddr, (const typemap*) m);
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
void* coro_topmost_frame_pointer(foster_generic_coro* coro) {
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

const char* coro_status_name(foster_generic_coro* c) {
  switch (coro_status(c)) {
  case FOSTER_CORO_INVALID: return "invalid";
  case FOSTER_CORO_SUSPENDED: return "suspended";
  case FOSTER_CORO_DORMANT: return "dormant";
  case FOSTER_CORO_RUNNING: return "running";
  case FOSTER_CORO_DEAD: return "dead";
  default: return "unknown";
  }
}

void coro_print(foster_generic_coro* coro) {
  if (!coro) return;
  fprintf(gclog, "coro %p: ", coro); fflush(stdout);
  fprintf(gclog, "sibling %p, invoker %p, status %s, fn %p\n",
      foster::runtime::coro_sibling(coro),
      foster::runtime::coro_invoker(coro),
      coro_status_name(coro),
      foster::runtime::coro_fn(coro));
}

void coro_dump(foster_generic_coro* coro) {
  if (!coro) {
    fprintf(gclog, "cannot dump NULL coro ptr!\n");
  } else if (ENABLE_GCLOG) {
    coro_print(coro);
    fprintf(gclog, " "); coro_print(foster::runtime::coro_sibling(coro));
  }
}

// Declared in libfoster_coro.cpp
extern "C"
void foster_coro_ensure_self_reference(foster_generic_coro* coro);

void scanCoroStack(foster_generic_coro* coro,
                   gc_visitor_fn visitor) {
  coro_dump(coro);
  if (!coro) return;
  if (foster::runtime::coro_status(coro) == FOSTER_CORO_INVALID
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

  // Another point worth mentioning is that two generic_coros
  // may point to the same stack but have different statuses:
  // an fcoro may say "RUNNING" while a ccoro may say "SUSPENDED",
  // because we don't bother updating the status for the current coro
  // when we invoke away from it. But since fcoros are the only ones
  // referenced directly by the program, it's all OK.

  // Note! We scan stacks from ccoros (yielded to),
  // not fcoros (invokable). A suspended stack will have
  // pointers into the stack from both types of coro, but
  // the ccoro pointer will point higher up the stack!

  // TODO mark stack so it won't be swept away

  // extract frame pointer from ctx, and visit its stack.
  void* frameptr = coro_topmost_frame_pointer(coro);
  gc_assert(frameptr != NULL, "(c)coro frame ptr shouldn't be NULL!");

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanning coro (%p, fn=%p, %s) stack from %p\n",
        coro, foster::runtime::coro_fn(coro), coro_status_name(coro), frameptr);
  }

  visitGCRootsWithStackMaps(frameptr, visitor);

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanned ccoro stack from %p\n", frameptr);
    fflush(gclog);
  }
}

//////////////////////////////////////////////////////////////}}}

//  {{{ Debugging utilities
void inspect_typemap(const typemap* ti) {
  fprintf(gclog, "typemap: %p\n", ti); fflush(gclog);
  if (!ti) return;
  fprintf(gclog, "\tsize:       %lld\n", ti->cell_size);   fflush(gclog);
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
}
// }}}

// {{{ Pointer classification utilities
bool isMetadataPointer(const void* meta) {
  if (uint64_t(meta) < uint64_t(1<<16)) return false;
  if (GC_ASSERTIONS) {
    const typemap* map = (const typemap*) meta;
    bool is_corrupted = (
          ((map->isCoro  != 0) && (map->isCoro  != 1))
       || ((map->isArray != 0) && (map->isArray != 1))
       || (map->numOffsets < 0)
       || (map->cell_size  < 0));
    if (is_corrupted) {
      inspect_typemap(map);
      printf("meta: %p\n", meta);
      gc_assert(!is_corrupted, "isMetadataPointer() found corrupted meta");
    }
  }
  return true;
}
// }}}

/////////////////////////////////////////////////////////////////

extern "C" {

// {{{ Allocation interface used by generated code
void* memalloc_cell(typemap* typeinfo) {
  if (GC_BEFORE_EVERY_MEMALLOC_CELL) {
    allocator->force_gc_for_debugging_purposes();
  }
  return allocator->allocate_cell(typeinfo);
}

void* memalloc_cell_16(typemap* typeinfo) {
  if (GC_BEFORE_EVERY_MEMALLOC_CELL) {
    allocator->force_gc_for_debugging_purposes();
  }
  return allocator->allocate_cell_N<16>(typeinfo);
}

void* memalloc_array(typemap* typeinfo, int64_t n, int8_t init) {
  return allocator->allocate_array(typeinfo, n, (bool) init);
}

void record_memalloc_cell(typemap* typeinfo, const char* srclines) {
  allocator->record_memalloc_cell(typeinfo, srclines);
}
// }}}

// Extern symbol for gdb, not direct use by generated code.
void fflush_gclog() { fflush(gclog); }

} // extern "C"

void force_gc_for_debugging_purposes() {
  allocator->force_gc_for_debugging_purposes();
}

} // namespace foster::runtime::gc

uint8_t ctor_id_of(void* constructed) {
  gc::heap_cell* cell = gc::heap_cell::for_body((gc::tidy*) constructed);
  gc::typemap* map = (gc::typemap*) cell->get_meta();
  int8_t ctorId = map->ctorId;
  if (ctorId < 0) {
    fprintf(gc::gclog, "foster_ctor_id_of inspected bogus ctor id %d\n", ctorId);
    gc::inspect_typemap(map);
  }
  return ctorId;
}

} // namespace foster::runtime
} // namespace foster

