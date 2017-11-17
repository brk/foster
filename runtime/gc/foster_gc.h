// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

namespace foster {
namespace runtime {
namespace gc {

struct tidy;
struct meta;
struct intr; // interior/internal; like tidy, but not preceded by metadata.
struct tori; // tidy or interior; consult mark bitmap (if in semispace)

void initialize(void* stack_base);
int  cleanup();
void force_gc_for_debugging_purposes();

bool is_marked_as_stable(tori* body);

} } } // namespace foster::runtime::gc
