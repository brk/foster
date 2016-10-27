// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "foster_globals.h"
#include "stat_tracker.h"

#include "base/time/time.h" // for TimeTicks, TimeDelta
#include "base/metrics/histogram.h"
#include "base/metrics/statistics_recorder.h"

#include <sys/resource.h> // for getrlimit, RLIMIT_STACK
#include "execinfo.h" // for backtrace

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)

// These are defined as compile-time constants so that the compiler
// can do effective dead-code elimination. If we were JIT compiling
// the GC we could (re-)specialize these config vars at runtime...
#define ENABLE_GCLOG 0
#define FOSTER_GC_TRACK_BITMAPS       0
#define FOSTER_GC_ALLOC_HISTOGRAMS    0
#define FOSTER_GC_TIME_HISTOGRAMS     0
#define FOSTER_GC_EFFIC_HISTOGRAMS    0
#define FOSTER_GC_PRINT_WHEN_RUN      0
#define GC_ASSERTIONS 0
#define TRACK_NUM_ALLOCATIONS         0
#define TRACK_BYTES_KEPT_ENTRIES      0
#define TRACK_BYTES_ALLOCATED_ENTRIES 0
#define TRACK_BYTES_ALLOCATED_PINHOOK 0
#define GC_BEFORE_EVERY_MEMALLOC_CELL 0
#define DEBUG_INITIALIZE_ALLOCATIONS  0
#define MEMSET_FREED_MEMORY           1
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

extern "C" {
  void foster_pin_hook_memalloc_cell(uint64_t nbytes);
  void foster_pin_hook_memalloc_array(uint64_t nbytes);
}

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

  virtual bool owns(tori* body) = 0;
  virtual tidy* tidy_for(tori* t) = 0;

  virtual void dump_stats(FILE* json) = 0;

  virtual void force_gc_for_debugging_purposes() = 0;

  virtual void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) = 0;
  virtual void* allocate_cell(typemap* typeinfo) = 0;

  virtual void* allocate_cell_16(typemap* typeinfo) = 0;
  virtual void* allocate_cell_32(typemap* typeinfo) = 0;
};

// {{{ Global data used by the GC
FILE* gclog = NULL;

class copying_gc;

template<typename Allocator>
struct GCGlobals {
  Allocator* allocator = NULL;
  Allocator* default_allocator = NULL;

  std::vector<allocator_range> allocator_ranges;

  ClusterMap clusterForAddress;

  bool had_problems;

  std::map<std::pair<const char*, typemap*>, int64_t> alloc_site_counters;

  base::TimeTicks gc_time;
  base::TimeTicks runtime_start;
  base::TimeTicks    init_start;
};

GCGlobals<copying_gc> gcglobals;
// }}}

// {{{ Internal utility functions
void gc_assert(bool cond, const char* msg);

template <typename T>
inline T num_granules(T size_in_bytes) { return size_in_bytes / T(16); }

bool is_marked_as_stable(tori* body) {
  for (const allocator_range& ar : gcglobals.allocator_ranges) {
    if (ar.range.contains(static_cast<void*>(body))) {
      return ar.stable;
    }
  }
  return false;
}
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

  uint8_t get_bit(int n) {
    int byte_offset = n / 8;
    int bit_offset  = n % 8;
    uint8_t val = bytes[byte_offset];
    uint8_t bit = (val >> bit_offset) & 1;
    return bit;
  }

  void set_bit(int n) {
    int byte_offset = n / 8;
    int bit_offset  = n % 8;
    uint8_t val = bytes[byte_offset];
    bytes[byte_offset] = val | (1 << bit_offset);
  }

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
void visitGCRoots(void* start_frame, copying_gc* visitor);
void coro_visitGCRoots(foster_generic_coro* coro, copying_gc* visitor);
const typemap* tryGetTypemap(heap_cell* cell);
// }}}

class heapstats {
public:
  heapstats() {
    num_allocations = 0;
    num_collections = 0;
    bytes_kept_per_gc.resize(TRACK_BYTES_KEPT_ENTRIES);
    bytes_req_per_alloc.resize(TRACK_BYTES_ALLOCATED_ENTRIES + 1);
  }

  // An efficiently-encoded int->int map...
  // A value of v at index k in [index 0..TRACK_BYTES_ALLOCATED_ENTRIES)
  // means v allocations of size (k * FOSTER_GC_DEFAULT_ALIGNMENT).
  // All larger allocations go in the last array entry.
  std::vector<int64_t>  bytes_req_per_alloc;

  stat_tracker<int64_t> bytes_kept_per_gc;

  int64_t num_allocations;
  int64_t num_collections;
};

// {{{ copying_gc
class copying_gc : public heap {
  // {{{ semispace
  class semispace {
  public:
      semispace(int64_t size, copying_gc* parent) : parent(parent),
                              obj_start(size / 16), obj_limit(size / 16) {
        range.base  = malloc(size);
        range.bound = offset(range.base, size);
        memset(range.base, 0x66, size);

        reset_bump();
      }

      ~semispace() {
        free(range.base);
      }

  private:
      memory_range range;
      void* bump;
      copying_gc* parent;
      bitmap obj_start;
      bitmap obj_limit;

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
        obj_start.clear();
        obj_limit.clear();
        fprintf(gclog, "after reset, bump = %p, low bits: %x, size = %lld\n", bump,
                                                    int(intptr_t(bump) & 0xf),
                                                    get_size());
      }

      bool contains(void* ptr) const { return range.contains(ptr); }

      void clear() {
        if (MEMSET_FREED_MEMORY) {
          fprintf(gclog, "clearing mem from %p to %p, bump = %p\n", range.base, range.bound, bump); fflush(gclog);
          memset(range.base, 0xFE, range.size());
        }
      }

      int64_t used_size() const { return distance(range.base, bump); }
      int64_t free_size() const { return distance(bump, range.bound); }
      int64_t  get_size() const { return distance(range.base, range.bound); }

      bool can_allocate_bytes(int64_t num_bytes) {
        return free_size() > num_bytes;
      }

      void allocate_cell_prechecked_histogram(int N) {
        if (N > 128) {
          LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-alloc-large", N, 129, 33000000, 50);
        } else {
          LOCAL_HISTOGRAM_ENUMERATION("gc-alloc-small", N, 128);
        }
      }

      // {{{ Prechecked allocation functions
      template <int N>
      tidy* allocate_cell_prechecked_N(const typemap* map) {
        heap_cell* allot = static_cast<heap_cell*>(bump);
        //fprintf(gclog, "this=%p, memsetting %d bytes at %p (ti=%p)\n", this, int(typeinfo->cell_size), bump, typeinfo); fflush(gclog);
        if (DEBUG_INITIALIZE_ALLOCATIONS) { memset(bump, 0xAA, N); }
        if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(N); }
        if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_cell(N); }
        if (TRACK_NUM_ALLOCATIONS) { ++parent->hpstats.num_allocations; }
        if (FOSTER_GC_ALLOC_HISTOGRAMS) { LOCAL_HISTOGRAM_ENUMERATION("gc-alloc-small", N, 128); }
        incr_by(bump, N);
        allot->set_meta(map);

        // Record the start and end of this object, for interior pointers, heap parsing, etc.
        if (FOSTER_GC_TRACK_BITMAPS) {
          int granule = granule_for(tori_of_tidy(allot->body_addr()));
          obj_start.set_bit(granule);
          obj_limit.set_bit(granule + num_granules(N));
        }
        // With --backend-optimize on a GC-heavy workload (10M allocs, 317MB allocated):
        //   Without memset free: 426ms = 293gc + 133mut
        //   Without bit setting: 460ms = 322gc + 134mut
        //   With one bit  set:   491ms = 318gc + 173mut
        //   With two bits set:   520ms = 310gc + 210mut
        // So: 6.7% degraded throughput for 1 bit set, 13% for two.
        // 10M allocs getting 30ms slower: 3 nanoseconds per bit set.
        // 32 * 10 * (1000/426) is just beyond 750 MB/s.
        // 32 * 10 * (1000/612) is just shy of 512 MB/s.
        //
        // Adding support for interior pointers based on granule bitmaps:
        //                        612ms = 430gc + 182mut [[30% degraded]]
        // Without the tidy_for(tori*) logic: 588ms = 411gc + 177mut
        //   & also minus bitsetting when evacuating: back to 491ms.

        //if (gNumAllocsToPrint --> 0)
        //  fprintf(gclog, "alloc'd _N=%d; %d, bump = %p, low bits: %x, granule = %d\n", N, int(map->cell_size), bump, intptr_t(bump) & 0xF, granule);
        return allot->body_addr();
      }

      tidy* allocate_cell_prechecked(const typemap* map) {
        heap_cell* allot = static_cast<heap_cell*>(bump);
        //fprintf(gclog, "this=%p, memsetting %d bytes at %p (ti=%p)\n", this, int(typeinfo->cell_size), bump, typeinfo); fflush(gclog);
        if (DEBUG_INITIALIZE_ALLOCATIONS) { memset(bump, 0xAA, map->cell_size); }
        if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(map->cell_size); }
        if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_cell(map->cell_size); }
        if (TRACK_NUM_ALLOCATIONS) { ++parent->hpstats.num_allocations; }
        if (!wantWeirdCrashToHappen && FOSTER_GC_ALLOC_HISTOGRAMS) {
          allocate_cell_prechecked_histogram((int) map->cell_size);
        }
        incr_by(bump, map->cell_size);
        allot->set_meta(map);
        if (FOSTER_GC_TRACK_BITMAPS) {
          size_t granule = granule_for(tori_of_tidy(allot->body_addr()));
          obj_start.set_bit(granule);
          obj_limit.set_bit(granule + num_granules(map->cell_size));
        }
        //if (gNumAllocsToPrint --> 0)
        //  fprintf(gclog, "alloc'd %d, bump = %p, low bits: %x, granule = %d\n", int(map->cell_size), bump, intptr_t(bump) & 0xF, granule);
        return allot->body_addr();
      }

      tidy* allocate_array_prechecked(const typemap* arr_elt_map,
                                      int64_t  num_elts,
                                      int64_t  total_bytes,
                                      bool     init) {
        heap_array* allot = static_cast<heap_array*>(bump);
        if (init) memset(bump, 0x00, total_bytes);
        incr_by(bump, total_bytes);
        //fprintf(gclog, "alloc'a %d, bump = %p, low bits: %x\n", int(total_bytes), bump, intptr_t(bump) & 0xF);
        allot->set_meta(arr_elt_map);
        allot->set_num_elts(num_elts);
        if (TRACK_BYTES_ALLOCATED_ENTRIES) { parent->record_bytes_allocated(total_bytes); }
        if (TRACK_BYTES_ALLOCATED_PINHOOK) { foster_pin_hook_memalloc_array(total_bytes); }
        if (TRACK_NUM_ALLOCATIONS) { ++parent->hpstats.num_allocations; }

        if (FOSTER_GC_TRACK_BITMAPS) {
          size_t granule = granule_for(tori_of_tidy(allot->body_addr()));
          obj_start.set_bit(granule);
          obj_limit.set_bit(granule + num_granules(total_bytes));
        }
        return allot->body_addr();
      }
      // }}}

      // {{{ metadata helpers
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
          cell_size = cell->cell_size();
        } else if (!arr) {
          cell_size = map->cell_size; // probably an actual pointer
        } else {
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
        }
        // }}}
      }
      // }}}

      // Invariant: cell is owned by the other semispace.
      // Returns body of newly allocated cell.
      tidy* ss_copy(heap_cell* cell, int remaining_depth) {
        tidy*       result = NULL;
        heap_array*    arr = NULL;
        const typemap* map = NULL;
        int64_t cell_size;

        if (cell->is_forwarded()) { goto return_result; }

        get_cell_metadata(cell, arr, map, cell_size);

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

        if (false /*map && isCoroBelongingToOtherThread(*map, cell)*/) {
          // Don't copy or scan a coroutine if it belongs to another thread!
          return cell->body_addr();
        }
        // }}}

        {
          heap_cell* new_addr = static_cast<heap_cell*>(bump);
          incr_by(bump, cell_size);
          memcpy(new_addr, cell, cell_size);
          cell->set_forwarded_body(new_addr->body_addr());

          if (FOSTER_GC_TRACK_BITMAPS) {
            obj_start.set_bit(granule_for(tori_of_tidy(new_addr->body_addr())));
            obj_limit.set_bit(granule_for((tori*) offset(new_addr->body_addr(), cell_size)));
          }

          // We now have a cell in the new semispace, but any pointer fields
          // it had are still pointing back to the old semispace.
          // We'll scan it to update those fields in place.

          // Copy depth-first, but not so much that we blow the stack...
          if (remaining_depth > 0) {
            if (map) { // No map means no pointers to scan!
              if (arr) arr = heap_array::from_heap_cell(new_addr);
              scan_with_map_and_arr(new_addr, *map, arr, remaining_depth - 1);
            }
          } else {
            fprintf(gclog, "adding to parent worklist, current length %d\n", parent->worklist.size());
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


      void scan_with_map_and_arr(heap_cell* cell, const typemap& map,
                                 heap_array* arr, int depth) {
        //fprintf(gclog, "copying %lld cell %p, map np %d, name %s\n", cell_size, cell, map.numEntries, map.name); fflush(gclog);
        if (arr) {
          // TODO for byte arrays and such, we can skip this loop...
          int64_t numcells = arr->num_elts();
          for (int64_t cellnum = 0; cellnum < numcells; ++cellnum) {
            //fprintf(gclog, "num cells in array: %lld, curr: %lld\n", numcells, cellnum);
            scan_with_map(arr->elt_body(cellnum, map.cell_size), map, depth);
          }
        } else {
            scan_with_map(from_tidy(cell->body_addr()), map, depth);
        }

        if (map.isCoro) {
          foster_generic_coro* coro = reinterpret_cast<foster_generic_coro*>(cell->body_addr());
          coro_visitGCRoots(coro, parent);
        }
      }


      void scan_with_map(intr* body, const typemap& map, int depth) {
        for (int i = 0; i < map.numOffsets; ++i) {
          parent->copy_or_update((unchecked_ptr*) offset(body, map.offsets[i]),
                                 depth);
        }
      }

      inline void scan_cell(heap_cell* cell, int depth) {
        heap_array* arr = NULL;
        const typemap* map = NULL;
        int64_t cell_size;
        get_cell_metadata(cell, arr, map, cell_size);
        // Without metadata for the cell, there's not much we can do...
        if (map) scan_with_map_and_arr(cell, *map, arr, depth);
      }

      inline tidy* tidy_for_granule(size_t g) {
        return (tidy*) offset(range.base, g * 16);
      }

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

  private:
      intr* from_tidy(tidy* t) { return (intr*) t; }
  };
  // }}} semispace

  // {{{ Copying GC data members

  heapstats hpstats;

  semispace* curr;
  semispace* next;

  struct worklist {
      void       initialize()      { ptrs.clear(); idx = 0; }
      void       process(semispace* next);
      bool       empty()           { return idx >= ptrs.size(); }
      void       advance()         { ++idx; }
      heap_cell* peek_front()      { return ptrs[idx]; }
      void       add(heap_cell* c) { ptrs.push_back(c); }
      size_t     size()            { return ptrs.size(); }
    private:
      size_t                  idx;
      std::vector<heap_cell*> ptrs;
  };
  worklist worklist;

  // }}}

  void gc(bool should_print);

  // precondition: all active cells from curr have been copied to next
  void flip() {
    // re-align the next bump pointer so it'll be ready for us.
    next->realign_bump();
    // curr is the old semispace, so we reset its bump ptr
    curr->reset_bump();
    std::swap(curr, next);
  }

  void record_bytes_allocated(int64_t num_bytes) {
    int64_t idx = num_bytes / FOSTER_GC_DEFAULT_ALIGNMENT;
    if (idx >= hpstats.bytes_req_per_alloc.size() - 1) {
      hpstats.bytes_req_per_alloc.back()++;
    } else {
      hpstats.bytes_req_per_alloc[idx]++;
    }
  }

public:
  copying_gc(int64_t size) : heap() {
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
    // }}}
  }

  virtual ~copying_gc() {
    dump_stats(NULL);
  }

  // Precondition: curr owns t.
  virtual tidy* tidy_for(tori* t) { return curr->tidy_for(t); }

  void visit_root(unchecked_ptr* root, const char* slotname) {
    gc_assert(root != NULL, "someone passed a NULL root addr!");
    if (ENABLE_GCLOG) {
      fprintf(gclog, "\t\tSTACK SLOT %p contains %p, slot name = %s\n", root,
                        unchecked_ptr_val(*root),
                        (slotname ? slotname : "<unknown slot>"));
    }
    this->copy_or_update(root, kFosterGCMaxDepth);
  }

  // Jones/Hosking/Moss refer to this function as "process(fld)".
  void copy_or_update(unchecked_ptr* root, int depth) {
    //       |------------|       obj: |------------|
    // root: |    body    |---\        |  size/meta |
    //       |------------|   |        |------------|
    //                        \------> |            |
    //                                ...          ...
    //                                 |            |
    //                                 |------------|
    tidy* tidyn;
    tori* body = untag(*root);
    if (!body) return;

    if (curr->contains(body)) {
      tidy* tidy = curr->tidy_for(body);
      heap_cell* obj = heap_cell::for_tidy(tidy);

      tidyn = next->ss_copy(obj, depth);
      *root = make_unchecked_ptr((tori*) offset(tidyn, distance(tidy, body) ));

      gc_assert(NULL != untag(*root), "copying gc should not null out slots");
      gc_assert(body != untag(*root), "copying gc should return new pointers");
    } else if (is_marked_as_stable(body)) {
      // TODO handling interior pointers to stable storage?
      // Where's the obj bitmap, and how repr? Or just forbid non-tidy ptrs?
      heap_cell* obj = heap_cell::for_tidy(reinterpret_cast<tidy*>(body));
      next->scan_cell(obj, depth);
    } else {
      // {{{ Should-never-happen error handling...
      if (next->contains(body)) {
        fprintf(gclog, "foster_gc error: tried to collect"
                       " cell in next-semispace: %p\n", body);
        fflush(gclog);
        //fprintf(gclog, "\t\twith meta %p\n", obj->get_meta());
        //fflush(gclog);
        exit(254);
        //return false;
      } else {
        fprintf(gclog, "foster_gc error: tried to collect"
                       " unknown cell: %p\n", body);
        fflush(gclog);
        gcglobals.had_problems = true;
      }
      // }}}
    }
  }

  virtual bool owns(tori* body) {
    return curr->contains(body) || next->contains(body);
  }

  // {{{ Allocation, in various flavors & specializations.
  virtual void* allocate_cell(typemap* typeinfo) {
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

  void* try_allocate_cell(typemap* typeinfo) {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.

    if (curr->can_allocate_bytes(cell_size)) {
      return curr->allocate_cell_prechecked(typeinfo);
    } else {
      return NULL;
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

  virtual void* allocate_cell_16(typemap* typeinfo) { return allocate_cell_N<16>(typeinfo); }
  virtual void* allocate_cell_32(typemap* typeinfo) { return allocate_cell_N<32>(typeinfo); }

  void* allocate_cell_slowpath(typemap* typeinfo) __attribute__((noinline))
  {
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.
    gc(FOSTER_GC_PRINT_WHEN_RUN);
    if (curr->can_allocate_bytes(cell_size)) {
      fprintf(gclog, "gc collection freed space for cell, now have %lld\n", curr->free_size());
      fflush(gclog);

      if (FOSTER_GC_EFFIC_HISTOGRAMS) {
         double reclaimed = double(curr->free_size()) / double(curr->get_size());
         int percent = int(reclaimed * 100.0);
         LOCAL_HISTOGRAM_PERCENTAGE("gc-reclaimed-pct", percent);
      }

      return curr->allocate_cell_prechecked(typeinfo);
    } else { oops_we_died_from_heap_starvation(); return NULL; }
  }

  static inline int64_t array_size_for(int64_t n, int64_t slot_size) {
    return roundUpToNearestMultipleWeak(sizeof(heap_array) + n * slot_size,
                                        FOSTER_GC_DEFAULT_ALIGNMENT);
  }

  virtual void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) {
    int64_t slot_size = elt_typeinfo->cell_size; // note the name change!
    int64_t req_bytes = array_size_for(n, slot_size);

    if (false && FOSTER_GC_ALLOC_HISTOGRAMS) {
      LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-alloc-array", (int) req_bytes, 1, 33000000, 128);
    }

    if (curr->can_allocate_bytes(req_bytes)) {
      return curr->allocate_array_prechecked(elt_typeinfo, n, req_bytes, init);
    } else {
      gc(FOSTER_GC_PRINT_WHEN_RUN);
      if (curr->can_allocate_bytes(req_bytes)) {
        fprintf(gclog, "gc collection freed space for array, now have %lld\n", curr->free_size());
        fflush(gclog);
        return curr->allocate_array_prechecked(elt_typeinfo, n, req_bytes, init);
      } else { oops_we_died_from_heap_starvation(); return NULL; }
    }
  }

  void oops_we_died_from_heap_starvation() {
    print_heap_starvation_info(gclog);
    print_heap_starvation_info(stderr);
    exit(255); // TODO be more careful if we're allocating from a coro...
  }

  void print_heap_starvation_info(FILE* f) {
    fprintf(f, "working set exceeded heap size of %lld bytes! aborting...\n", curr->get_size()); fflush(f);
    fprintf(f, "    try running with a larger heap size using a flag like\n");
    fprintf(f, "      --foster-runtime '{\"gc_semispace_size_kb\":64000}'\n");
  }
  // }}}

  // {{{
  virtual void force_gc_for_debugging_purposes() { this->gc(false); }

  virtual void dump_stats(FILE* json) {
    FILE* stats = json ? json : gclog;

    double approx_bytes = double((hpstats.num_collections * curr->get_size()) + curr->used_size());
    fprintf(stats, "'num_collections' : %" PRId64 ",\n", hpstats.num_collections);
    if (TRACK_NUM_ALLOCATIONS) {
    fprintf(stats, "'num_allocations' : %.3g,\n", double(hpstats.num_allocations));
    fprintf(stats, "'avg_alloc_size' : %d,\n", (hpstats.num_allocations == 0)
                                                  ? 0
                                                  : int(approx_bytes / double(hpstats.num_allocations)));
    }
    fprintf(stats, "'alloc_num_bytes_gt' : %.3g,\n", approx_bytes);
    fprintf(stats, "'semispace_size_kb' : %lld,\n", curr->get_size() / 1024);

    if (TRACK_BYTES_KEPT_ENTRIES) {
    int64_t mn = hpstats.bytes_kept_per_gc.compute_min(),
            mx = hpstats.bytes_kept_per_gc.compute_max(),
            aa = hpstats.bytes_kept_per_gc.compute_avg_arith();
    fprintf(stats, "'min_bytes_kept' : %8" PRId64 ",\n", mn);
    fprintf(stats, "'max_bytes_kept' : %8" PRId64 ",\n", mx);
    fprintf(stats, "'avg_bytes_kept' : %8" PRId64 ",\n", aa);
    fprintf(stats, "'min_bytes_kept_percent' : %.2g%%,\n", double(mn * 100.0)/double(curr->get_size()));
    fprintf(stats, "'max_bytes_kept_percent' : %.2g%%,\n", double(mx * 100.0)/double(curr->get_size()));
    fprintf(stats, "'avg_bytes_kept_percent' : %.2g%%,\n", double(aa * 100.0)/double(curr->get_size()));
    }
    if (TRACK_BYTES_ALLOCATED_ENTRIES) {
      for (int i = 0; i < hpstats.bytes_req_per_alloc.size() - 1; ++i) {
        int sz = i * FOSTER_GC_DEFAULT_ALIGNMENT;
        fprintf(stats, "allocs_of_size_%4d: %12" PRId64 ",\n", sz, hpstats.bytes_req_per_alloc[i]);
      }
      fprintf(stats,  "allocs_of_size_more: %12" PRId64 ",\n", hpstats.bytes_req_per_alloc.back());
    }

    if (!gcglobals.alloc_site_counters.empty()) {
      fprintf(stats, "'allocation_sites' : [\n");
      for (auto it : gcglobals.alloc_site_counters) {
        typemap* map = it.first.second;
        int64_t bytes_allocated = map->cell_size * it.second;
        fprintf(stats, "{ 'typemap' : %p , 'allocations' : %12" PRId64 ", 'alloc_size':%" PRId64
                        ", 'bytes_allocated': %10" PRId64 ", 'alloc_percent':%f,",
                        map, it.second, map->cell_size, bytes_allocated, (double(bytes_allocated) * 100.0) / approx_bytes);
        fprintf(stats, "  'from' : \"%s\" },\n", it.first.first);
      }
      fprintf(stats, "],\n");
    }
  }
  // }}}

}; // copying_gc
// }}}

extern "C" foster_generic_coro** __foster_get_current_coro_slot();

// {{{ Primary GC driver loops for root visiting and worklist processing.
// Adds stack + coroutine roots to the worklist, processes the worklist,
// then flips semispaces.
void copying_gc::gc(bool should_print) {
  if (should_print) {
    fprintf(stdout, "♻\n");
    fprintf(stderr, "♻\n");
  }
  base::TimeTicks begin = base::TimeTicks::Now();
  ++hpstats.num_collections;
  if (ENABLE_GCLOG) {
    fprintf(gclog, ">>>>>>> visiting gc roots on current stack\n"); fflush(gclog);
  }

  worklist.initialize();

  visitGCRoots(__builtin_frame_address(0), this);

  foster_generic_coro** coro_slot = __foster_get_current_coro_slot();
  foster_generic_coro*  coro = *coro_slot;
  if (coro) {
    if (ENABLE_GCLOG) {
      fprintf(gclog, "==========visiting current ccoro: %p\n", coro); fflush(gclog);
    }
    this->visit_root((unchecked_ptr*)coro_slot, NULL);
    if (ENABLE_GCLOG) {
      fprintf(gclog, "==========visited current ccoro: %p\n", coro); fflush(gclog);
    }
  }

  worklist.process(next);

  if (TRACK_BYTES_KEPT_ENTRIES) {
    hpstats.bytes_kept_per_gc.record_sample(next->used_size());
  }

  flip();
  next->clear(); // for debugging purposes

  if (ENABLE_GCLOG) {
    fprintf(gclog, "\t/gc\n\n");
    fflush(gclog);
  }

  auto delta = base::TimeTicks::Now() - begin;
  if (FOSTER_GC_TIME_HISTOGRAMS) {
    LOCAL_HISTOGRAM_CUSTOM_COUNTS("gc-pause-micros", delta.InMicroseconds(),  0, 60000000, 256);
  }
  gcglobals.gc_time += delta;
}

void copying_gc::worklist::process(copying_gc::semispace* next) {
  while (!empty()) {
    heap_cell* cell = peek_front();
    advance();
    next->scan_cell(cell, kFosterGCMaxDepth);
  }
}
// }}}

#include "foster_gc_backtrace_x86-inl.h"

// {{{ Walks the call stack, calling visitor->visit_root() along the way.
void visitGCRoots(void* start_frame, copying_gc* visitor) {
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

// A thin wrapper around visitGCRoots.
void coro_visitGCRoots(foster_generic_coro* coro, copying_gc* visitor) {
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

  // extract frame pointer from ctx, and visit its stack.
  void* frameptr = coro_topmost_frame_pointer(coro);
  gc_assert(frameptr != NULL, "(c)coro frame ptr shouldn't be NULL!");

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanning coro (%p, fn=%p, %s) stack from %p\n",
        coro, foster::runtime::coro_fn(coro), coro_status_name(coro), frameptr);
  }

  visitGCRoots(frameptr, visitor);

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanned ccoro stack from %p\n", frameptr);
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

size_t get_default_stack_size() {
  struct rlimit rlim;
  getrlimit(RLIMIT_STACK, &rlim);
  return (size_t) (rlim.rlim_cur != RLIM_INFINITY) ? rlim.rlim_cur : 0x080000;
}

void register_allocator_ranges(void* stack_highest_addr) {
  // ASSUMPTION: stack segments grow down, and are linear...
  size_t stack_size = get_default_stack_size();
  allocator_range ar;
  ar.range.bound = stack_highest_addr;
  ar.range.base  = (void*) (((char*) ar.range.bound) - stack_size);
  ar.stable = true;
  gcglobals.allocator_ranges.push_back(ar);

  allocator_range datarange;
  get_static_data_range(datarange.range);
  datarange.stable = true;
  gcglobals.allocator_ranges.push_back(datarange);
}

void initialize(void* stack_highest_addr) {
  gcglobals.init_start = base::TimeTicks::Now();
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");
  if (!base::TimeTicks::IsHighResolution()) {
    fprintf(gclog, "(warning: using low-resolution timer)\n");
  }

  base::StatisticsRecorder::Initialize();
  gcglobals.allocator = new copying_gc(gSEMISPACE_SIZE());
  gcglobals.default_allocator = gcglobals.allocator;

  gcglobals.had_problems = false;

  register_allocator_ranges(stack_highest_addr);

  register_stackmaps(gcglobals.clusterForAddress);

  gcglobals.gc_time = base::TimeTicks();
  gcglobals.runtime_start = base::TimeTicks::Now();
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

FILE* print_timing_stats() {
  base::TimeTicks fin = base::TimeTicks::Now();
  base::TimeDelta total_elapsed = fin - gcglobals.init_start;
  base::TimeDelta  init_elapsed = gcglobals.runtime_start - gcglobals.init_start;
  base::TimeDelta    gc_elapsed = gcglobals.gc_time - base::TimeTicks();
  base::TimeDelta   mut_elapsed = total_elapsed - gc_elapsed - init_elapsed;
  FILE* json = __foster_globals.dump_json_stats_path.empty()
                ? NULL
                : fopen(__foster_globals.dump_json_stats_path.c_str(), "w");
  if (json) fprintf(json, "{\n");
  if (!json &&
      (FOSTER_GC_ALLOC_HISTOGRAMS || FOSTER_GC_TIME_HISTOGRAMS || FOSTER_GC_EFFIC_HISTOGRAMS)) {
    fprintf(gclog, "stats recorder active? %d\n", base::StatisticsRecorder::IsActive());
    std::string output;
    base::StatisticsRecorder::WriteGraph("", &output);
    fprintf(gclog, "%s\n", output.c_str());
  }
  gclog_time("Elapsed_runtime", total_elapsed, json);
  gclog_time("Initlzn_runtime",  init_elapsed, json);
  gclog_time("     GC_runtime",    gc_elapsed, json);
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

extern "C" void inspect_ptr_for_debugging_purposes(void* bodyvoid) {
  unsigned align = (!(intptr_t(bodyvoid) & 0x0f)) ? 16
                 : (!(intptr_t(bodyvoid) & 0x07)) ? 8
                 : (!(intptr_t(bodyvoid) & 0x03)) ? 4 : 0
                 ;
  fprintf(stdout, "inspect_ptr_for_debugging_purposes: %p  (alignment %d)\n", bodyvoid, align);
  unchecked_ptr bodyu = make_unchecked_ptr(static_cast<tori*>(bodyvoid));
  tori* body = untag(bodyu);
  if (! body) {
    fprintf(stdout, "body is (maybe tagged) null\n");
  } else {
    if (gc::gcglobals.allocator->owns(body)) {
      fprintf(stdout, "\t...this pointer is owned by the main allocator");
    } else if (is_marked_as_stable(body)) {
      fprintf(stdout, "\t...this pointer is marked as stable");
    } else {
      fprintf(stdout, "\t...this pointer is not owned by the main allocator, nor marked as stable!");
      goto done;
    }

    gc::heap_cell* cell = gc::heap_cell::for_tidy(gc::gcglobals.allocator->tidy_for(body));
    if (cell->is_forwarded()) {
      fprintf(stdout, "cell is forwarded to %p\n", cell->get_forwarded_body());
    } else {
      if (const gc::typemap* ti = tryGetTypemap(cell)) {
        //gc::inspect_typemap(stdout, ti);
        int iters = ti->numOffsets > 128 ? 0 : ti->numOffsets;
        for (int i = 0; i < iters; ++i) {
          fprintf(stdout, "\t@%d : %p\n", ti->offsets[i], gc::offset(bodyvoid, ti->offsets[i]));
          fflush(stdout);
        }
      } else {
        fprintf(stdout, "\tcell has no typemap, size is %lld\n", cell->cell_size());
      }
    }
  }

done:
  fprintf(stdout, "done inspecting ptr: %p\n", body);
  fflush(stdout);
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

#if 0
void* try_memalloc_cell(typemap* typeinfo) {
  return gcglobals.allocator->try_allocate_cell(typeinfo);
}
#endif

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

void* memalloc_array(typemap* typeinfo, int64_t n, int8_t init) {
  return gcglobals.allocator->allocate_array(typeinfo, n, (bool) init);
}

void record_memalloc_cell(typemap* typeinfo, const char* srclines) {
  gcglobals.alloc_site_counters[std::make_pair(srclines, typeinfo)]++;
}
// }}}

// Extern symbol for gdb, not direct use by generated code.
void fflush_gclog() { fflush(gclog); }

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

