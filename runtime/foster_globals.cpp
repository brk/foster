#include "foster_globals.h"

#include <cstring>
#include <iostream>
#include <sstream>
#include <cstdlib>

namespace foster {
namespace runtime {

  bool str_prefix_eq(const char* target, const char* other) {
    return strncmp(target, other, strlen(target)) == 0;
  }

  bool streq(const char* target, const char* other) {
    return strncmp(target, other, (std::max)(strlen(target), strlen(other)) + 1) == 0;
  }

  bool is_foster_runtime_flag(const char* arg) {
    return str_prefix_eq("--foster-", arg);
  }

  double parse_double(const char* s, double d) {
    char* end = nullptr;
    double rv = strtod(s, &end);
    if (end == s) return d; else return rv;
  }

  // Trawl through argv, looking for any JSON flags destined for the runtime itself.
  // The remainder of the flags will be installed in the global .args.
  // Note that we must be given command-line args like -foster-runtime-X ARG,
  //                                               not -foster-runtime-X=ARG!
  void parse_runtime_options(int argc, char** argv) {
    __foster_globals.semispace_size = 1024 * 1024;

    for (int i = 0; i < argc; ++i) {
      const char* arg = argv[i];
      if (!is_foster_runtime_flag(arg)) {
        __foster_globals.args.push_back(arg);
      } else {
        if (i == argc - 1) continue; // no more to look at!
        if (streq("--foster-heap-KB", arg)) {
          __foster_globals.semispace_size = ssize_t(parse_double(argv[i + 1], 1024.0) * 1024.0);
        } else if (streq("--foster-heap-MB", arg)) {
          __foster_globals.semispace_size = ssize_t(parse_double(argv[i + 1], 1.0) * 1024.0 * 1024.0);
        } else if (streq("--foster-heap-GB", arg)) {
          __foster_globals.semispace_size = ssize_t(parse_double(argv[i + 1], 0.001) * 1024.0 * 1024.0 * 1024.0);
        } else if (streq("--foster-json-stats", arg)) {
          __foster_globals.dump_json_stats_path = argv[i + 1];
        }
      }
    }
  }

} // end namespace foster::runtime
} // end namespace foster

