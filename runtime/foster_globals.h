// Copyright (c) 2013 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GLOBALS_H
#define FOSTER_GLOBALS_H

#include "base/threading/simple_thread.h"

#ifdef OS_MACOSX
#include <objc/runtime.h>
#include <objc/objc-runtime.h>
#else
typedef void* id;
#endif

#include "cpuid.h"

#include <vector>
#include <string>

struct FosterGlobals {
  std::vector<const char*> args;

  int                    semispace_size;

  // One timer thread for the whole runtime, not per-vCPU.
  base::SimpleThread*    scheduling_timer_thread;
  id                     scheduling_timer_thread_autorelease_pool;

  cpuid_info             x86_cpuid_info;
};

extern FosterGlobals __foster_globals;

namespace base { class DictionaryValue; }

namespace foster {
namespace runtime {
  void parse_runtime_options(int argc, char** argv);
  std::string dump_global_config_options();
  void extract_global_config_options(const base::DictionaryValue&);
}
}

#endif
