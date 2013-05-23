#include "foster_globals.h"

#include "base/values.h"

#include "base/json/json_reader.h"

#include <iostream>
#include <sstream>

namespace foster {
namespace runtime {

  bool streq(const char* target, const char* other) {
    return strncmp(target, other, strlen(target)) == 0;
  }

  bool is_foster_runtime_flag(const char* arg) {
    // normalize to a single leading dash
    const char* arg_cont = (arg && arg[0] == '-' && arg[1] == '-') ? &arg[1] : arg;
    return streq("-foster-runtime", arg_cont);
  }

  // Trawl through argv, looking for any JSON flags destined for the runtime itself.
  // The remainder of the flags will be installed in the global .args.
  void parse_runtime_options(int argc, char** argv) {
    base::JSONReader reader;
    base::DictionaryValue dv;
    bool merged = false;

    for (int i = 0; i < argc; ++i) {
      const char* arg = argv[i];
      if (!is_foster_runtime_flag(arg)) {
        __foster_globals.args.push_back(arg);
      } else {
        if (i == argc - 1) continue; // no more to look at!
        if (Value* v = reader.ReadToValue(argv[i + 1])) {
          DictionaryValue* dvp = NULL;
          v->GetAsDictionary(&dvp);
          if (dvp) {
            dv.MergeDictionary(dvp); merged = true;
          } else {
            fprintf(stderr, "Parsed option JSON was not dict: %s\n", argv[i + 1]);
          }
          delete v;
        } else {
          fprintf(stderr, "Parsing option JSON failed: %s\n", reader.GetErrorMessage().c_str());
        }
      }
    }

    extract_global_config_options(dv);
  }

  // Heads up: keys with '.' in them will not work unless the non-expanding get/set
  // variants for DictionaryValue are used, // because JSON parsing doesn't perform
  // path expansion.
  const char kGCSemispaceSizeKb[] = "gc_semispace_size_kb";

  void extract_global_config_options(const base::DictionaryValue& dv) {
    int ss_kb = 1024;
    bool ok = dv.GetInteger(kGCSemispaceSizeKb, &ss_kb);
    __foster_globals.semispace_size = ss_kb * 1024;
  }

  std::string dump_global_config_options() {
    base::DictionaryValue dv;
    dv.SetInteger(kGCSemispaceSizeKb, __foster_globals.semispace_size / 1024);
    std::stringstream ss;
    ss << dv;
    return ss.str();
  }

} // end namespace foster::runtime
} // end namespace foster

