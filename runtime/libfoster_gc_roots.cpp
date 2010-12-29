// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster_gc_roots.h"

// (eventually, per-thread variable)
// coro_invoke(c) sets this to c.
// coro_yield() resets this to current_coro->invoker.
foster_generic_coro* current_coro;
