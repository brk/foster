// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cstddef> // for offsetof

#include "libfoster.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"

#include "base/time.h"
#include "base/threading/platform_thread.h"

#include "execinfo.h"

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)

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

////////////////////////////////////////////////////////////////////

void inspect_typemap(typemap* ti);

void scanCoroStack(foster_generic_coro* coro, gc_visitor_fn visitor);

inline bool
isCoroBelongingToOtherThread(const typemap* map, void* body) {
  #ifdef FOSTER_MULTITHREADED
  if (map->isCoro) {
    foster_generic_coro* coro = (foster_generic_coro*) body;
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
      void reset_bump() {
        // We want to position the bump pointer far enough into the buffer
        // so that after accounting for the heap cell header, the body pointer
        // resulting from allocation will be properly aligned.
        bump = roundUpToNearestMultipleWeak(
                          start + HEAP_CELL_HEADER_SIZE,
                          FOSTER_GC_DEFAULT_ALIGNMENT)
                                          - HEAP_CELL_HEADER_SIZE;
      }

      bool contains(void* ptr) {
        return (ptr >= start) && (ptr < end);
      }

      void clear() {
        fprintf(gclog, "clearing mem from %p to %p\n", start, end);
        fflush(gclog);
        memset(start, 255, end - start);
      }

      int64_t free_size() { return end - bump; }

      bool can_allocate_bytes(int64_t num_bytes) {
        return free_size() > num_bytes;
      }

      void* allocate_cell_prechecked(typemap* typeinfo) {
        heap_cell* allot = (heap_cell*) bump;
        memset(bump, 0xAA, typeinfo->cell_size);
        bump += typeinfo->cell_size;
        allot->set_meta(typeinfo);
        return allot->body_addr();
      }

      void* allocate_array_prechecked(typemap* elt_typeinfo,
                                      int64_t  num_elts,
                                      int64_t  total_bytes) {
        heap_cell* allot = (heap_cell*) bump;
        bump += total_bytes;
        allot->set_meta(elt_typeinfo);
        // allot = [meta|size|e1...]
        void* body_addr = allot->body_addr();
        int64_t* size = (int64_t*) body_addr;
                *size = num_elts;
        return body_addr;
      }

      void complain_to_lack_of_metadata(void* body, heap_cell* cell);

      // returns body of newly allocated cell
      void* ss_copy(void* body, const void* meta) {
        if (!this->parent->owns(body)) return body;

        heap_cell* cell = heap_cell::for_body(body);
        meta = meta ? meta : cell->get_meta();

        if (!meta) {
          complain_to_lack_of_metadata(body, cell);
          return NULL;
        }

        //fprintf(gclog, "copying cell %p, meta %p\n", cell, meta); fflush(gclog);
        if (cell->is_forwarded()) {
          void* fwd = cell->get_forwarded_body();
          //fprintf(gclog, "cell %p(->%p) considered forwarded to [[%p]] for body %p(->%p)\n",
          //  cell, *(void**)cell,
          //  fwd, body, *(void**)body); fflush(gclog);
          return fwd;
        }

        int64_t cell_size;
        if (!isMetadataPointer(meta)) {
          cell_size = int64_t(meta);
        } else {
          const typemap* map = (const typemap*) meta;
          if (isCoroBelongingToOtherThread(map, body)) {
            // Don't copy or scan a coroutine if
            // it belongs to a different thread!
            return body;
          }

          // probably an actual pointer
          cell_size = map->cell_size;
        }
        foster_assert(cell_size >= 16, "cell size must be at least 16!");
        //fprintf(gclog, "copying cell %p, cell size %llu\n", cell, cell_size); fflush(gclog);

        if (can_allocate_bytes(cell_size)) {
          memcpy(bump, cell, cell_size);
          heap_cell* new_addr = (heap_cell*) bump;
          bump += cell_size;
          cell->set_forwarded_body(new_addr->body_addr());
          if (isMetadataPointer(meta)) {
            const typemap* map = (const typemap*) meta;

            //fprintf(gclog, "copying %lld cell %p, map np %d, name %s\n",
            //  cell_size, cell, map->numEntries, map->name); fflush(gclog);

            // for each pointer field in the cell
            for (int i = 0; i < map->numEntries; ++i) {
              const typemap::entry& e = map->entries[i];
              void** oldslot = (void**) offset(body, e.offset);

              //fprintf(gclog, "body is %p, offset is %d, typeinfo is %p, addr_of_ptr_slot is %p, ptr_slot_val is %p\n",
              //    body, e.offset, e.typeinfo, oldslot, *oldslot);
              // recursively copy the field from cell, yielding subfwdaddr
              // set the copied cell field to subfwdaddr
              if (*oldslot != NULL) {
                void** newslot = (void**) offset(new_addr->body_addr(), e.offset);
                //fprintf(gclog, "recursively copying of cell %p slot %p with ti %p to %p\n",
                 // cell, oldslot, e.typeinfo, newslot); fflush(gclog);
                *newslot = ss_copy(*oldslot, e.typeinfo);
                //fprintf(gclog, "recursively copied  of cell %p slot %p with ti %p to %p\n",
                 // cell, oldslot, e.typeinfo, newslot); fflush(gclog);
              }
            }

            if (map->isCoro) {
              foster_generic_coro* coro = (foster_generic_coro*) cell->get_forwarded_body();
              scanCoroStack(coro, copying_gc_root_visitor);
            }
          }

          return cell->get_forwarded_body();
        } else {
          printf("not enough space to copy!\n");
          printf("have %llu = 0x%llx\n", free_size(), (unsigned long long) free_size());
          printf("need %llu = 0x%llx\n", cell_size,   (unsigned long long) cell_size);
          //exit(255);
          return NULL;
        }
      }
  };

  semispace* curr;
  semispace* next;

  int num_allocations;
  int num_collections;
  bool saw_bad_pointer;

  void gc();

  // precondition: all active cells from curr have been copied to next
  void flip() {
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
  }

  ~copying_gc() {
      fprintf(gclog, "num allocations: %d, num collections: %d\n",
                      num_allocations, num_collections);
  }

  bool had_problems() { return saw_bad_pointer; }

  void force_gc_for_debugging_purposes() { this->gc(); }

  bool owns(void* ptr) {
    if (curr->contains(ptr)) return true;
    saw_bad_pointer = true;
    if (next->contains(ptr)) {
      fprintf(gclog, "foster_gc error: tried to collect"
                     " pointer in next-semispace: %p\n", ptr);
      return false;
    }
    fprintf(gclog, "foster_gc error: copying_gc cannot collect"
                     " pointer that it did not allocate: %p\n", ptr);
    return false;
  }

  void copy_or_update(void* body, void** root, const void* meta) {
    //       |------------|            |------------|
    // root: |    body    |---\        |    _size   |
    //       |------------|   |        |------------|
    //                        \------> |            |
    //                                 |            |
    //                                 |            |
    //                                 |------------|
    void* newaddr = next->ss_copy(body, meta);
    //fprintf(gclog, "copying_gc_root_visitor(%p -> %p): copied  body\n", root, body); fflush(gclog);
    if (meta) {
      typemap* map = (typemap*) meta;
      fprintf(gclog, "\tname: %s", map->name);
    }
    if (newaddr) {
      fprintf(gclog, "; replacing %p with %p\n", body, newaddr);
      *root = newaddr;
    }
  }

  void* allocate_cell(typemap* typeinfo) {
    ++num_allocations;
    int64_t cell_size = typeinfo->cell_size;

    if (curr->can_allocate_bytes(cell_size)) {
      return curr->allocate_cell_prechecked(typeinfo);
    } else {
      gc();
      if (curr->can_allocate_bytes(cell_size)) {
        fprintf(gclog, "gc collection freed space, now have %lld\n", curr->free_size());
            return curr->allocate_cell_prechecked(typeinfo);
      } else {
        fprintf(gclog, "working set exceeded heap size! aborting...\n"); fflush(gclog);
        exit(255); // TODO be more careful if we're allocating from a coro...
        return NULL;
      }
    }
  }

  void* allocate_array(typemap* elt_typeinfo, int64_t n) {
    ++num_allocations;
    int64_t cell_size = elt_typeinfo->cell_size;
    int64_t req_bytes = 8 + 8 + n * cell_size; // typeinfo, elt count, elts.

    if (curr->can_allocate_bytes(req_bytes)) {
      return curr->allocate_array_prechecked(elt_typeinfo, n, req_bytes);
    } else {
      gc();
      if (curr->can_allocate_bytes(req_bytes)) {
        fprintf(gclog, "gc collection freed space, now have %lld\n", curr->free_size());
            return curr->allocate_array_prechecked(elt_typeinfo, n, req_bytes);
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
void copying_gc_root_visitor(void **root, const void *meta) {
  foster_assert(root != NULL, "someone passed a NULL root addr!");
  void* body = *root;
  fprintf(gclog, "copying_gc_root_visitor(root %p -> body %p, meta %p)\n", root, body, meta); fflush(gclog);
  if (isMetadataPointer(meta)) {
    inspect_typemap((typemap*)meta);
  }

  if (body) {
    allocator->copy_or_update(body, root, meta);
  }
}

base::TimeTicks gc_time;
base::TimeTicks runtime_start;
base::TimeTicks    init_start;

void copying_gc::gc() {
  base::TimeTicks begin = base::TimeTicks::HighResNow();
  ++this->num_collections;
  fprintf(gclog, "visiting gc roots on current stack\n"); fflush(gclog);
  visitGCRootsWithStackMaps(__builtin_frame_address(0),
                            copying_gc_root_visitor);

  if (current_coro) {
    fprintf(gclog, "==========visiting current ccoro: %p\n", current_coro); fflush(gclog);
    copying_gc_root_visitor((void**)&current_coro, NULL);
    fprintf(gclog, "==========visited current ccoro: %p\n", current_coro); fflush(gclog);
  }

  flip();
  next->clear(); // for debugging purposes
  fprintf(gclog, "\t/gc\n\n");
  fflush(gclog);

  gc_time += (base::TimeTicks::HighResNow() - begin);
}

typedef std::map<void*, const stackmap::PointCluster*> ClusterMap;
ClusterMap clusterForAddress;

void register_stackmaps(ClusterMap& clusterForAddress);

void initialize() {
  init_start = base::TimeTicks::HighResNow();
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  const int KB = 1024;
  allocator = new copying_gc(1024 * KB);

  register_stackmaps(clusterForAddress);

  gc_time = base::TimeTicks();
  runtime_start = base::TimeTicks::HighResNow();
}

void gclog_time(const char* msg, base::TimeDelta d) {
  fprintf(gclog, "%s: %2ld.%03ld s\n", msg,
          long(d.InSeconds()),
          long(d.InMilliseconds() - (d.InSeconds() * 1000)));
}

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
  //allocator->force_gc_for_debugging_purposes();
  return allocator->allocate_cell(typeinfo);
}

extern "C" void* memalloc_array(typemap* typeinfo, int64_t n) {
  return allocator->allocate_array(typeinfo, n);
}

void force_gc_for_debugging_purposes() {
  allocator->force_gc_for_debugging_purposes();
}

#include "foster_gc_backtrace_x86-inl.h"

void visitGCRootsWithStackMaps(void* start_frame,
                               gc_visitor_fn visitor) {
  enum { MAX_NUM_RET_ADDRS = 1024 };
  static void* retaddrs[MAX_NUM_RET_ADDRS];
  static frameinfo frames[MAX_NUM_RET_ADDRS];

  // Collect frame pointers and return addresses
  // for the current call stack.
  int nFrames = foster_backtrace((frameinfo*) start_frame, frames, MAX_NUM_RET_ADDRS);
  const bool SANITY_CHECK_CUSTOM_BACKTRACE = false;
  if (SANITY_CHECK_CUSTOM_BACKTRACE) {
    // backtrace() fails when called from a coroutine's stack...
    int numRetAddrs = backtrace((void**)&retaddrs, MAX_NUM_RET_ADDRS);
    if (true) {
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
      fprintf(gclog, "no point cluster for address %p with frame ptr%p\n", safePointAddr, frameptr);
      continue;
    }

    fprintf(gclog, "retaddr %p, frame ptr %p: live count w/meta %d, w/o %d\n",
      safePointAddr, frameptr,
      pc->liveCountWithMetadata, pc->liveCountWithoutMetadata);

    int32_t frameSize = pc->frameSize;
    for (int a = 0; a < pc->liveCountWithMetadata; ++a) {
      int32_t     off  = pc->offsetWithMetadata(a)->offset;
      const void* meta = pc->offsetWithMetadata(a)->metadata;
      void* rootaddr = offset(frameptr, off);

      visitor((void**) rootaddr, meta);
    }
    // TODO also scan pointers without metadata
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
  } else {
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

  fprintf(gclog, "========= scanning coro (%p, fn=%p, %s) stack from %p\n",
      coro, coro->fn, coro_status(coro->status), frameptr);

  visitGCRootsWithStackMaps(frameptr, visitor);

  fprintf(gclog, "scanned ccoro stack from %p\n", frameptr);
  fflush(gclog);
}

/////////////////////////////////////////////////////////////////

void copying_gc::semispace::complain_to_lack_of_metadata(
                             void* body, heap_cell* cell) {
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
  fprintf(gclog, "env tm name is %s, # ptrs = %d\n", envtm->name, envtm->numEntries); fflush(gclog);
}

void inspect_typemap(typemap* ti) {
  fprintf(gclog, "typemap: %p\n", ti); fflush(gclog);
  if (!ti) return;

  fprintf(gclog, "\tsize: %lld\n", ti->cell_size);
  fprintf(gclog, "\tname: %s\n", ti->name);
  fprintf(gclog, "\tisCoro: %d\n", ti->isCoro);
  fprintf(gclog, "\tnumE: %d\n", ti->numEntries);
  fflush(gclog);
  int iters = ti->numEntries > 128 ? 0 : ti->numEntries;
  for (int i = 0; i < iters; ++i) {
    fprintf(gclog, "\t\t@%d: %p\n", ti->entries[i].offset,
                                 ti->entries[i].typeinfo);
    fflush(gclog);
  }
}

bool isMetadataPointer(const void* meta) {
 return uint64_t(meta) > uint64_t(1<<16);
}

} } } // namespace foster::runtime::gc

