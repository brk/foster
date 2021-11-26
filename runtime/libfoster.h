// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef LIBFOSTER_H
#define LIBFOSTER_H

#include <stdint.h>

// This file exists to provide symbols to link
// libfoster_main.cpp::main() to libfoster

struct coro_context;
extern "C" {
void foster_coro_destroy(coro_context* ctx);

struct foster_bytes {
   int64_t cap; // array portion has space for this many elements
   int8_t bytes[0];
};
}

namespace foster {
namespace runtime {

void initialize(int argc, char** argv, void*);
int  cleanup();

uint8_t ctor_id_of(void* body);

namespace gc {
struct typemap;
}

} // namespace foster::runtime
} // namespace foster

//////////////////////////////////////////////////////////////////

extern "C" {

// Interface to foster's memory allocator; see gc/foster_gc_allocate.cpp
void* memalloc_cell(foster::runtime::gc::typemap* typeinfo);
void* memalloc_array(foster::runtime::gc::typemap* typeinfo, int64_t n, int8_t init);
void foster__assert(bool, const char*);

void* foster_emit_string_of_cstring(const char*, int32_t); // defined by the Foster compiler
}

#ifndef PRId64
#define PRId64 "lld"
#endif

#ifndef PRIX64
#define PRIX64 "llX"
#endif

#endif
