// Copyright (c) 2013 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GLOBALS_H
#define FOSTER_GLOBALS_H

#ifdef OS_MACOSX
#include <objc/runtime.h>
#include <objc/objc-runtime.h>
#else
typedef void* id;
#endif

#include <vector>
#include <string>
#include <thread>
#include <atomic>

////////////////////////////////////////////////////////////////

struct FosterGlobals {
  std::vector<const char*> args;
  std::string              dump_json_stats_path;

  ssize_t                  semispace_size;

  // One timer thread for the whole runtime, not per-vCPU.
  std::atomic<bool>      scheduling_timer_thread_ending;
  std::thread*           scheduling_timer_thread;
  id                     scheduling_timer_thread_autorelease_pool;

  bool                   disable_sticky;
  double                 sticky_base_threshold;
  double                 compaction_threshold;
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
