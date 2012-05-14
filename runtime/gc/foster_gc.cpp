// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cstddef> // for offsetof
#include <numeric>
#include <algorithm>

#include "libfoster.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"

#include "base/time.h"
#include "base/threading/platform_thread.h"

#include "execinfo.h"

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)
#define ENABLE_GCLOG 0
#define GC_BEFORE_EVERY_MEMALLOC_CELL 0
#define TRACK_BYTES_KEPT_ENTRIES 0

const int KB = 1024;
const int SEMISPACE_SIZE = 1024 * KB;

/////////////////////////////////////////////////////////////////

void register_stackmaps();

#include "foster_gc_utils.h"

#include <sstream>
#include <list>
#include <vector>
#include <map>

namespace foster {
namespace runtime {
namespace gc {

FILE* gclog = NULL;

template<typename T>
struct stat_tracker {
  int  idx;
  int  idx_max;
  std::vector<T> samples;
  stat_tracker() : idx(0), idx_max(0) {}

  void resize(size_t sz) { samples.resize(sz); }

  void record_sample(T v) {
    samples[idx] = v;
    if (idx > idx_max) { idx_max = idx; }
    idx = (idx + 1) % int(samples.size());
  }

  T compute_min() const {
    return *std::min_element(samples.begin(), samples.end());
  }

  T compute_max() const {
    return *std::max_element(samples.begin(), samples.end());
  }

  T compute_avg_arith() const {
    return std::accumulate(samples.begin(), samples.end(), T(0)) /
                                                              T(samples.size());
  }
};

////////////////////////////////////////////////////////////////////

void inspect_typemap(typemap* ti);

void scanCoroStack(foster_generic_coro* coro, gc_visitor_fn visitor);

inline bool
isCoroBelongingToOtherThread(const typemap* map, heap_cell* cell) {
  #ifdef FOSTER_MULTITHREADED
  if (map->isCoro) {
    foster_generic_coro* coro = (foster_generic_coro*) cell->body_addr();
    if (coro->status == FOSTER_CORO_RUNNING) {
      // Don't scan a coroutine if it's being run by another thread!
      if (coro->owner_thread != PlatformThread::CurrentId()) {
        return true;
      }
    }
  }
  #endif

  return false;
}

class copying_gc {
  class semispace {
  public:
      semispace(int64_t size, copying_gc* parent) : parent(parent) {
        start = (char*) malloc(size);
        end   = start + size;
        reset_bump();
        memset(start, 0x66, size);

        genericClosureMarker = NULL;
      }

      ~semispace() {
        free(start);
      }
  private:
      char* start;
      char* end;
      char* bump;
      copying_gc* parent;

      char* genericClosureMarker;

  public:
      void realign_bump() {
         bump = roundUpToNearestMultipleWeak(bump + HEAP_CELL_HEADER_SIZE,
                                             FOSTER_GC_DEFAULT_ALIGNMENT)
                                                  - HEAP_CELL_HEADER_SIZE;
      }
      void reset_bump() {
        // We want to position the bump pointer far enough into the buffer
        // so that after accounting for the heap cell header, the body pointer
        // resulting from allocation will be properly aligned.
        bump = start;
        realign_bump();
        fprintf(gclog, "after reset, bump = %p, low bits: %x\n", bump,
                                                    int(intptr_t(bump) & 0xf));
      }

      bool contains(void* ptr) {
        return (ptr >= start) && (ptr < end);
      }

      void clear() {
        fprintf(gclog, "clearing mem from %p to %p, bump = %p\n", start, end, bump);
        fflush(gclog);
        memset(start, 0xFE, end - start);
      }

      int64_t used_size() const { return bump - start; }
      int64_t free_size() const {
        //fprintf(gclog, "this=%p, bump = %p, low bits: %x\n", this, bump, intptr_t(bump) & 0xf);
        //fflush(gclog);
        return end - bump;
      }

      bool can_allocate_bytes(int64_t num_bytes) {
        return free_size() > num_bytes;
      }

      void* allocate_cell_prechecked(typemap* typeinfo) {
        heap_cell* allot = (heap_cell*) bump;
        //fprintf(gclog, "this=%p, memsetting %d bytes at %p (ti=%p)\n", this, int(typeinfo->cell_size), bump, typeinfo); fflush(gclog);
        memset(bump, 0xAA, typeinfo->cell_size);
        bump += typeinfo->cell_size;
        allot->set_meta(typeinfo);
        //fprintf(gclog, "alloc'd %d, bump = %p, low bits: %x\n", int(typeinfo->cell_size), bump, intptr_t(bump) & 0xF);
        return allot->body_addr();
      }

      void* allocate_array_prechecked(typemap* arr_elt_typeinfo,
                                      int64_t  num_elts,
                                      int64_t  total_bytes,
                                      bool     init) {
        heap_array* allot = (heap_array*) bump;
        if (init) memset(bump, 0x00, total_bytes);
        bump += total_bytes;
        //fprintf(gclog, "alloc'a %d, bump = %p, low bits: %x\n", int(total_bytes), bump, intptr_t(bump) & 0xF);
        allot->set_meta(arr_elt_typeinfo);
        allot->set_num_elts(num_elts);
        return allot->body_addr();
      }

      void complain_to_lack_of_metadata(heap_cell* cell);

      // returns body of newly allocated cell
      void* ss_copy(heap_cell* cell) {
        if (!this->parent->owns(cell)) return cell->body_addr();
        void* result = NULL;
        const void* meta = NULL;
        heap_array* arr = NULL;

        if (cell->is_forwarded()) {
          result = cell->get_forwarded_body();
          goto return_result;
        }

        meta = cell->get_meta();
        foster_assert(meta != NULL, "cannot copy cell lacking metadata");
        if (ENABLE_GCLOG) {
          if (isMetadataPointer(meta)) {
            inspect_typemap((typemap*)meta);
          }
        }

        int64_t cell_size;

        if (!isMetadataPointer(meta)) {
          cell_size = int64_t(meta);
        } else {
          const typemap* map = (const typemap*) meta;
          if (isCoroBelongingToOtherThread(map, cell)) {
            // Don't copy or scan a coroutine if
            // it belongs to a different thread!
            return cell->body_addr();
          }

          if (map->isArray) {
            arr = heap_array::from_heap_cell(cell);
            cell_size = array_size_for(arr->num_elts(), map->cell_size);
            if (ENABLE_GCLOG) {
              fprintf(gclog, "Collecting array of total size %lld, cell size %lld, len %lld...\n",
                                  cell_size, map->cell_size, arr->num_elts());
            }
          } else {
            // probably an actual pointer
            cell_size = map->cell_size;
          }
        }
        foster_assert(cell_size >= 16, "cell size must be at least 16!");
        if (ENABLE_GCLOG) {
          fprintf(gclog, "copying cell %p, cell size %llu\n", cell, cell_size); fflush(gclog);
        }

        if (can_allocate_bytes(cell_size)) {
          memcpy(bump, cell, cell_size);
          heap_cell* new_addr = (heap_cell*) bump;
          bump += cell_size;
          cell->set_forwarded_body(new_addr->body_addr());
          if (isMetadataPointer(meta)) {
            const typemap* map = (const typemap*) meta;

            //fprintf(gclog, "copying %lld cell %p, map np %d, name %s\n",
            //  cell_size, cell, map->numEntries, map->name); fflush(gclog);

            int64_t from_old_body_to_new_body = (char*)new_addr - (char*)cell;
            // for each cell in the array (if applicable)
            int64_t numcells = arr ? arr->num_elts() : 1;
            // TODO for byte arrays and such, we can skip this loop...
            for (int64_t cellnum = 0; cellnum < numcells; ++cellnum) {
              // for each pointer field in the cell
              //fprintf(gclog, "num cells in array (if any): %lld, curr: %lld\n",
              //                  numcells, cellnum);
              void* old_body = arr ? arr->elt_body(cellnum, map->cell_size)
                                   : cell->body_addr();
              void* new_body = offset(old_body, from_old_body_to_new_body);
              for (int i = 0; i < map->numOffsets; ++i) {
                int32_t off_bytes = map->offsets[i];
                void** oldslot = (void**) offset(old_body, off_bytes);

                //fprintf(gclog, "body is %p, offset is %d, typeinfo is %p, addr_of_ptr_slot is %p, ptr_slot_val is %p\n",
                //    body, e.offset, e.typeinfo, oldslot, *oldslot);
                // recursively copy the field from cell, yielding subfwdaddr
                // set the copied cell field to subfwdaddr
                if (*oldslot != NULL) {
                  void** newslot = (void**) offset(new_body, off_bytes);
                  //fprintf(gclog, "recursively copying of cell %p slot %p with type map %p to %p\n",
                  //  cell, oldslot, map, newslot); fflush(gclog);
                  *newslot = ss_copy(heap_cell::for_body(*oldslot));

                  foster_assert(*newslot != NULL,     "copying gc should not null out slots");
                  foster_assert(*newslot != *oldslot, "copying gc should return new pointers");
                  //fprintf(gclog, "recursively copied  of cell %p slot %p with type map %p to %p\n",
                  //  cell, oldslot, map, newslot); fflush(gclog);
                }
              }
            }

            if (map->isCoro) {
              foster_generic_coro* coro = (foster_generic_coro*) cell->get_forwarded_body();
              scanCoroStack(coro, copying_gc_root_visitor);
            }
          }

          result = cell->get_forwarded_body();
          goto return_result;
        } else {
          printf("not enough space to copy!\n");
          printf("have %llu = 0x%llx\n", free_size(), (unsigned long long) free_size());
          printf("need %llu = 0x%llx\n", cell_size,   (unsigned long long) cell_size);
          //exit(255);
          return NULL;
        }
        return_result:
          if (ENABLE_GCLOG) {
            fprintf(gclog, "; replacing %p with %p\n", cell->body_addr(), result);
          }
          return result;
      }
  };

  stat_tracker<int64_t> bytes_kept_per_alloc;
  int64_t num_allocations;
  int64_t num_collections;
  bool saw_bad_pointer;

  semispace* curr;
  semispace* next;

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
    bytes_kept_per_alloc.resize(TRACK_BYTES_KEPT_ENTRIES);
  }

  ~copying_gc() {
      double approx_bytes = double(num_collections * SEMISPACE_SIZE);
      fprintf(gclog, "num collections: %" PRId64 "\n", num_collections);
      fprintf(gclog, "num allocations: %.3g\n", double(num_allocations));
      fprintf(gclog, "alloc # bytes >: %.3g\n", approx_bytes);
      fprintf(gclog, "avg. alloc size: %d\n", int(approx_bytes / double(num_allocations)));

      if (TRACK_BYTES_KEPT_ENTRIES) {
      int64_t mn = bytes_kept_per_alloc.compute_min(),
              mx = bytes_kept_per_alloc.compute_max(),
              aa = bytes_kept_per_alloc.compute_avg_arith();
      fprintf(gclog, "min bytes kept: %8" PRId64 " (%.2g%%)\n", mn, double(mn * 100.0)/double(SEMISPACE_SIZE));
      fprintf(gclog, "max bytes kept: %8" PRId64 " (%.2g%%)\n", mx, double(mx * 100.0)/double(SEMISPACE_SIZE));
      fprintf(gclog, "avg bytes kept: %8" PRId64 " (%.2g%%)\n", aa, double(aa * 100.0)/double(SEMISPACE_SIZE));
      }
  }

  bool had_problems() { return saw_bad_pointer; }

  void force_gc_for_debugging_purposes() { this->gc(); }

  bool owns(heap_cell* cell) {
    if (curr->contains(cell)) return true;
    saw_bad_pointer = true;
    if (next->contains(cell)) {
      fprintf(gclog, "foster_gc error: tried to collect"
                     " cell in next-semispace: %p\n", cell);
      fflush(gclog);
      fprintf(gclog, "\t\twith meta %p\n", cell->get_meta());
      fflush(gclog);
      exit(254);
      //return false;
    }
    fprintf(gclog, "foster_gc error: copying_gc cannot collect"
                     " cell that it did not allocate: %p\n", cell);
    //fprintf(gclog, "\t\twith meta %p\n",  cell->get_meta());
    return false;
  }

  void copy_or_update(void* body, void** root) {
    //       |------------|            |------------|
    // root: |    body    |---\        |  size/meta |
    //       |------------|   |        |------------|
    //                        \------> |            |
    //                                ...          ...
    //                                 |            |
    //                                 |------------|
    *root = next->ss_copy(heap_cell::for_body(body));
  }

  void* allocate_cell(typemap* typeinfo) {
    ++num_allocations;
    int64_t cell_size = typeinfo->cell_size; // includes space for cell header.

    if (curr->can_allocate_bytes(cell_size)) {
      return curr->allocate_cell_prechecked(typeinfo);
    } else {
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
  }

  static inline int64_t array_size_for(int64_t n, int64_t slot_size) {
    return roundUpToNearestMultipleWeak(sizeof(heap_array) + n * slot_size,
                                        FOSTER_GC_DEFAULT_ALIGNMENT);
  }

  void* allocate_array(typemap* elt_typeinfo, int64_t n, bool init) {
    ++num_allocations;
    int64_t slot_size = elt_typeinfo->cell_size; // note the name change!
    int64_t req_bytes = array_size_for(n, slot_size);

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
};

copying_gc* allocator = NULL;

// This function statically references the global allocator.
// Eventually we'll want a generational GC with thread-specific
// allocators and (perhaps) type-specific allocators.
void copying_gc_root_visitor(void **root, const void *slotname) {
  foster_assert(root != NULL, "someone passed a NULL root addr!");
  void* body = *root;
  if (ENABLE_GCLOG) {
    fprintf(gclog, "\t\tSTACK SLOT %p contains %p, slot name = %s\n", root, body,
                      (slotname ? ((const char*) slotname) : "<unknown slot>"));
  }
  if (body) {
    allocator->copy_or_update(body, root);
  }
}

base::TimeTicks gc_time;
base::TimeTicks runtime_start;
base::TimeTicks    init_start;

void copying_gc::gc() {
  base::TimeTicks begin = base::TimeTicks::HighResNow();
  ++this->num_collections;
  if (ENABLE_GCLOG) {
    fprintf(gclog, ">>>>>>> visiting gc roots on current stack\n"); fflush(gclog);
  }

  visitGCRootsWithStackMaps(__builtin_frame_address(0),
                            copying_gc_root_visitor);

  if (current_coro) {
    if (ENABLE_GCLOG) {
      fprintf(gclog, "==========visiting current ccoro: %p\n", current_coro); fflush(gclog);
    }
    copying_gc_root_visitor((void**)&current_coro, NULL);
    if (ENABLE_GCLOG) {
      fprintf(gclog, "==========visited current ccoro: %p\n", current_coro); fflush(gclog);
    }
  }

  if (TRACK_BYTES_KEPT_ENTRIES) {
    bytes_kept_per_alloc.record_sample(next->used_size());
  }

  flip();
  next->clear(); // for debugging purposes

  if (ENABLE_GCLOG) {
    fprintf(gclog, "\t/gc\n\n");
    fflush(gclog);
  }

  gc_time += (base::TimeTicks::HighResNow() - begin);
}

typedef std::map<void*, const stackmap::PointCluster*> ClusterMap;
ClusterMap clusterForAddress;

void register_stackmaps(ClusterMap& clusterForAddress);

void initialize() {
  init_start = base::TimeTicks::HighResNow();
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  allocator = new copying_gc(SEMISPACE_SIZE);

  register_stackmaps(clusterForAddress);

  gc_time = base::TimeTicks();
  runtime_start = base::TimeTicks::HighResNow();
}

void gclog_time(const char* msg, base::TimeDelta d) {
  fprintf(gclog, "%s: %2ld.%03ld s\n", msg,
          long(d.InSeconds()),
          long(d.InMilliseconds() - (d.InSeconds() * 1000)));
}

// TODO: track bytes allocated, bytes clollected, max heap size,
//       max slop (alloc - reserved), peak mem use; compute % GC time.

int cleanup() {
  base::TimeTicks fin = base::TimeTicks::HighResNow();
  base::TimeDelta total_elapsed = fin - init_start;
  base::TimeDelta  init_elapsed = runtime_start - init_start;
  base::TimeDelta    gc_elapsed = gc_time - base::TimeTicks();
  gclog_time("Elapsed runtime", total_elapsed);
  gclog_time("Initlzn runtime",  init_elapsed);
  gclog_time("     GC runtime",    gc_elapsed);
  gclog_time("Mutator runtime", total_elapsed - gc_elapsed - init_elapsed);
  bool had_problems = allocator->had_problems();
  delete allocator;
  fclose(gclog); gclog = NULL;
  return had_problems ? 99 : 0;
}

extern "C" void* memalloc_cell(typemap* typeinfo) {
  if (GC_BEFORE_EVERY_MEMALLOC_CELL) {
    allocator->force_gc_for_debugging_purposes();
  }
  return allocator->allocate_cell(typeinfo);
}

extern "C" void* memalloc_array(typemap* typeinfo, int64_t n, int8_t init) {
  return allocator->allocate_array(typeinfo, n, (bool) init);
}

void force_gc_for_debugging_purposes() {
  allocator->force_gc_for_debugging_purposes();
}

// Extern symbol for gdb, not foster programs.
extern "C" void fflush_gclog() { fflush(gclog); }

#include "foster_gc_backtrace_x86-inl.h"

void visitGCRootsWithStackMaps(void* start_frame,
                               gc_visitor_fn visitor) {
  enum { MAX_NUM_RET_ADDRS = 1024 };
  void* retaddrs[MAX_NUM_RET_ADDRS];
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
    void* safePointAddr = frames[i].retaddr;
    void* frameptr = (void*) frames[i].frameptr;

    const stackmap::PointCluster* pc = clusterForAddress[safePointAddr];
    if (!pc) {
      if (ENABLE_GCLOG) {
        fprintf(gclog, "no point cluster for address %p with frame ptr%p\n", safePointAddr, frameptr);
      }
      continue;
    }

    if (ENABLE_GCLOG) {
      fprintf(gclog, "\nframe %d: retaddr %p, frame ptr %p: live count w/meta %d, w/o %d\n",
        i, safePointAddr, frameptr,
        pc->liveCountWithMetadata, pc->liveCountWithoutMetadata);
    }

    int32_t frameSize = pc->frameSize;
    for (int a = 0; a < pc->liveCountWithMetadata; ++a) {
      int32_t     off  = pc->offsetWithMetadata(a)->offset;
      const void* meta = pc->offsetWithMetadata(a)->metadata;
      void* rootaddr = offset(frameptr, off);

      visitor((void**) rootaddr, meta);
    }

    foster_assert(pc->liveCountWithoutMetadata == 0,
                  "TODO: scan pointer w/o metadata");
  }
}

/////////////////////////////////////////////////////////////////
////////////////////// coro functions ///////////////////////////
/////////////////////////////////////////////////////////////////

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
  foster_assert(coro->status == FOSTER_CORO_SUSPENDED
             || coro->status == FOSTER_CORO_DORMANT,
           "can only get topmost frame pointer from "
           "suspended or dormant coro!");
  void** sp = coro->ctx.sp;
  #if __amd64
  const int NUM_SAVED = 6;
  #else // CORO_WIN_TIB : += 3
  const int NUM_SAVED = 4;
  #endif

  return &sp[NUM_SAVED - 1];
}

const char* coro_status(int status) {
  switch (status) {
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
      coro->sibling, coro->invoker, coro_status(coro->status), coro->fn);
}

void coro_dump(foster_generic_coro* coro) {
  if (!coro) {
    fprintf(gclog, "cannot dump NULL coro ptr!\n");
  } else if (ENABLE_GCLOG) {
    coro_print(coro);
    fprintf(gclog, " "); coro_print(coro->sibling);
  }
}

// Declared in libfoster_coro.cpp
extern "C"
void foster_coro_ensure_self_reference(foster_generic_coro* coro);

void scanCoroStack(foster_generic_coro* coro,
                   gc_visitor_fn visitor) {
  coro_dump(coro);
  if (!coro) return;
  if (coro->status == FOSTER_CORO_INVALID
   || coro->status == FOSTER_CORO_DEAD
   || coro->status == FOSTER_CORO_RUNNING) {
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
  foster_assert(frameptr != NULL, "(c)coro frame ptr shouldn't be NULL!");

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanning coro (%p, fn=%p, %s) stack from %p\n",
        coro, coro->fn, coro_status(coro->status), frameptr);
  }

  visitGCRootsWithStackMaps(frameptr, visitor);

  if (ENABLE_GCLOG) {
    fprintf(gclog, "========= scanned ccoro stack from %p\n", frameptr);
    fflush(gclog);
  }
}

/////////////////////////////////////////////////////////////////

void copying_gc::semispace::complain_to_lack_of_metadata(heap_cell* cell) {
  void* body = cell->body_addr();
  const int ptrsize = sizeof(void*);
  void** bp4 = (void**) offset(body, ptrsize);
  const void* meta2 = *(const void**) offset(body, -ptrsize);
  inspect_typemap((typemap*) meta2);
  fprintf(gclog, "called copy with null metadata\n"); fflush(gclog);
  fprintf(gclog, "body   is %p -> %p\n", body, *(void**)body); fflush(gclog);
  fprintf(gclog, "body+%d is %p -> %p\n", ptrsize, offset(body, ptrsize), *bp4); fflush(gclog);
  fprintf(gclog, "body-%d is %p -> %p\n", ptrsize, offset(body,-ptrsize), *(void**)offset(body,-ptrsize));
  fflush(gclog);
  void** envptr = (void**)*bp4;
  fprintf(gclog, "envptr: %p -> %p\n", envptr, *envptr); fflush(gclog);
  typemap* envtm = (typemap*) *envptr;
  fprintf(gclog, "env tm name is %s, # ptrs = %d\n", envtm->name, envtm->numOffsets); fflush(gclog);
}

void inspect_typemap(typemap* ti) {
  fprintf(gclog, "typemap: %p\n", ti); fflush(gclog);
  if (!ti) return;
  fprintf(gclog, "\tsize:       %lld\n", ti->cell_size);   fflush(gclog);
  foster_assert(ti->cell_size > 0, "invalid typemap in inspect_typemap");
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

bool isMetadataPointer(const void* meta) {
 return uint64_t(meta) > uint64_t(1<<16);
}

} // namespace foster::runtime::gc

uint8_t ctor_id_of(void* constructed) {
  gc::heap_cell* cell = gc::heap_cell::for_body(constructed);
  gc::typemap* map = (gc::typemap*) cell->get_meta();
  int8_t ctorId = map->ctorId;
  if (ctorId < 0) {
    fprintf(gc::gclog, "foster_ctor_id_of inspected bogus ctor id %d\n", ctorId);
    gc::inspect_typemap(map);
  }
  return ctorId;
}

} // namespace foster::runtime
}

