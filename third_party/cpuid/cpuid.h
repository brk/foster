#ifndef CPUID_H
#define CPUID_H

#define CPUID_VERSION_STRING "2010-06-14"

// Based on revision 036 (August 2009) of Intel's Application Note 485,
// Intel (r) Processor Identification and the CPUID Instruction.
// http://www.intel.com/Assets/PDF/appnote/241618.pdf

#include <cstring>
#include <string>
#include <vector>
#include <map>
#include <stdint.h>

typedef unsigned int uint;

struct cpuid_info;

bool cpuid_introspect(cpuid_info&);

int cpuid_small_cache_size(cpuid_info&);
int cpuid_large_cache_size(cpuid_info&);

/////////////////////////////////////////////////////////////////////

struct tag_processor_features {
  int threads; // total, or per core?

  struct tag_monitor_features {
    int min_line_size;
    int max_line_size;
  } monitor_features;
};

struct tag_processor_cache_descriptor {
  int entries_or_linesize; // 0 if no relevant cache; linesize for non-TLB caches
  int set_assoc_ways; // 0 for fully associative
  bool sectored;
  int size; // page size for TLB caches, total size for non-TLB caches
};

struct tag_processor_cache_descriptors {
  tag_processor_cache_descriptor TLBi, TLBd, L1i, L1d, L2, L3;
};


inline const char* cache_type_str(int type) {
  switch (type) {
    case 0: return "-";
    case 1: return "d"; // data
    case 2: return "i"; // instruction
    case 3: return ""; // unified
  }
  return "?";
}

struct tag_processor_cache_parameter_set {
  int reserved_APICS;
  int sharing_threads;
  bool fully_associative;
  bool self_initializing_cache_level;
  int cache_level;
  int cache_type;
  int ways;
  int physical_line_partitions;
  int system_coherency_line_size;
  int sets;
  bool inclusive;
  // the description for EDX[1] and EDX[0] is virtually identical!
  bool inclusive_behavior;

  int size_in_bytes;
};


struct cpuid_info {
  cpuid_info() {
    memset(brand_string, 0, sizeof(brand_string));
    memset(vendor_id,    0, sizeof(vendor_id));
    rdtsc_serialized_overhead_cycles = -1;
    rdtsc_unserialized_overhead_cycles = -1;
  }

  int max_basic_eax;
  uint max_ext_eax;
  int max_linear_address_size;
  int max_physical_address_size;
  double rdtsc_serialized_overhead_cycles;
  double rdtsc_unserialized_overhead_cycles;

  typedef std::vector<tag_processor_cache_parameter_set> cache_parameters;
  cache_parameters processor_cache_parameters;

  tag_processor_features           processor_features;
  tag_processor_cache_descriptors  processor_cache_descriptors;

  typedef std::map<std::string, bool> feature_flags;
  feature_flags features;

  char brand_string[48];
  char vendor_id[13];
};

#endif
