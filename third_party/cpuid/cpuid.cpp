// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "cpuid.h"

///////////////////////////////////////////////////////////////

int cache_type_tag(char c) {
  switch (c) {
    case 'd': return 1; // data
    case 'i': return 2; // instruction
    case 'u': return 3; // unified
  }
  return 0; // default
}

int cpuid_small_cache_size(cpuid_info& info) {
  int min_size = 1<<30;
  int instr_cache = cache_type_tag('i');

  cpuid_info::cache_parameters::iterator it;
  for (it = info.processor_cache_parameters.begin();
      it != info.processor_cache_parameters.end();
      ++it) {
    if (it->cache_type == instr_cache) continue;
    if (it->size_in_bytes < min_size) {
      min_size = it->size_in_bytes;
    }
  }

  return min_size;
}

int cpuid_large_cache_size(cpuid_info& info) {
  int max_size = -1;

  cpuid_info::cache_parameters::iterator it;
  for (it = info.processor_cache_parameters.begin();
      it != info.processor_cache_parameters.end();
      ++it) {
    if (it->size_in_bytes > max_size) {
      max_size = it->size_in_bytes;
    }
  }

  return max_size;
}

// low bit is bit 0, high bit on IA-32 is bit 31
#define BIT(n) (1U << (n))

// mask of bits from 0 to n, inclusive
// e.g. LO_MASK(3) == 0b1111
#define LO_MASK(n) (BIT((n)+1U) - 1U)

// value of bits from hi to lo, inclusive
#define MASK_RANGE_IN(v, hi, lo) ((v >> (lo)) & LO_MASK((hi) - (lo)))

#define MASK_RANGE_EX(v, hi, lo) (MASK_RANGE_IN(v, hi, lo+1U))

#define BIT_IS_SET(v, bit) ((v & BIT(bit)) != 0)

#define ARRAY_SIZE(a) (sizeof((a))/sizeof((a)[0]))

#define MERGE_HI_LO(a, b) ((((uint64)a) << 32) | ((uint64)b))

#define D(expr) (#expr) << " = " << (expr)

// http://www.ibiblio.org/gferg/ldp/GCC-Inline-Assembly-HOWTO.html

// http://www.intel.com/Assets/PDF/appnote/241618.pdf page 13 and 14

// global register locatiosn and variable aliases
enum REGISTER { EAX, EBX, ECX, EDX };
uint reg[4] = { 0 };
uint& eax = reg[0]; uint& ebx = reg[1]; uint& ecx = reg[2]; uint& edx = reg[3];

struct feature_bit { REGISTER reg; int offset; const char* name; };

feature_bit intel_feature_bits[] = { // EAX = 1
  { EDX,  3, "pse" },
  { EDX,  4, "tsc" },
  { EDX,  5, "msr" },
  { EDX,  8, "cx8" },
  { EDX, 15, "cmov" },
  { EDX, 16, "pat" },
  { EDX, 17, "pse36" },
  { EDX, 19, "clflush" },
  { EDX, 21, "ds" },
  { EDX, 23, "mmx" },
  { EDX, 25, "sse" },
  { EDX, 26, "sse2" },
  { EDX, 27, "ss" },
  { EDX, 28, "htt" },

  { ECX,  0, "sse3" },
  { ECX,  1, "pclmuldq" },
  { ECX,  2, "dtes64" },
  { ECX,  3, "monitor" },
  { ECX,  4, "ds_cpl" },
  { ECX,  5, "vmx" },
  { ECX,  6, "smx" },
  { ECX,  9, "ssse3" },
  { ECX, 13, "cx16" },
  { ECX, 15, "pdcm" },
  { ECX, 19, "sse41" },
  { ECX, 20, "sse42" },
  { ECX, 21, "x2apic" },
  { ECX, 22, "movbe" },
  { ECX, 23, "popcnt" },
  { ECX, 25, "aes" }
};

feature_bit intel_ext_feature_bits[] = { // EAX = 0x80000001
  { EDX, 29, "x86_64" },
  { ECX,  0, "lahf" }
};

feature_bit amd_feature_bits[] = {
  { EDX,  3, "pse" },
  { EDX,  4, "tsc" },
  { EDX,  5, "msr" },
  { EDX,  8, "cx8" },
  { EDX, 15, "cmov" },
  { EDX, 16, "pat" },
  { EDX, 17, "pse36" },
  { EDX, 19, "clflush" },
  { EDX, 23, "mmx" },
  { EDX, 25, "sse" },
  { EDX, 26, "sse2" },
  { EDX, 28, "htt" },

  { ECX,  0, "sse3" },
  { ECX,  3, "monitor" },
  { ECX,  9, "ssse3" },
  { ECX, 13, "cx16" },
  { ECX, 19, "sse41" },
  { ECX, 23, "popcnt" },
  { ECX, 31, "raz" }
};

feature_bit amd_ext_feature_bits[] = { // EAX = 0x80000001
  { ECX, 10, "ibs" },
  { ECX,  8, "3dnowprefetch" },
  { ECX,  7, "misalignsse" },
  { ECX,  6, "sse4a" },
  { ECX,  5, "abm" },
  { ECX,  2, "svm" },

  { EDX, 31, "3dnow" },
  { EDX, 30, "3dnowext" },
  { EDX, 29, "x86_64" },
  { EDX, 27, "rdtscp" },
  { EDX, 22, "mmxext" },
  { EDX, 15, "cmov" },
  { EDX,  8, "cx8" },
  { EDX,  5, "msr" },
  { EDX,  3, "pse" }
};

//////////////////////////////////////////////////////////////////////////////

void init_all_features_to_false(cpuid_info& info) {
  for (unsigned i = 0; i < ARRAY_SIZE(intel_feature_bits); ++i) {
    info.features[intel_feature_bits[i].name] = false;
  }
  for (unsigned i = 0; i < ARRAY_SIZE(intel_ext_feature_bits); ++i) {
    info.features[intel_ext_feature_bits[i].name] = false;
  }
  for (unsigned i = 0; i < ARRAY_SIZE(amd_feature_bits); ++i) {
    info.features[amd_feature_bits[i].name] = false;
  }
  for (unsigned i = 0; i < ARRAY_SIZE(amd_ext_feature_bits); ++i) {
    info.features[amd_ext_feature_bits[i].name] = false;
  }
}

#if 0 // Untested detailed processor type introspection
  struct tag_processor_signature {
    uint full_bit_string;
    uint extended_family;
    uint extended_model;
    uint processor_type;
    uint family_code;
    uint model_number;
    uint stepping_id;
  } processor_signature;


  const char* intel_processor_type_string() {
    switch (processor_signature.processor_type) {
      case 0b00: return "Original OEM Processor";
      case 0b01: return "OverDrive Processor";
      case 0b10: return "Dual Processor";
    }
    return "Unknown processor type";
  }

  const char* intel_extmodel_0_signature_string() {
    switch (processor_signature.family_code) {
      case 0b0011: return "i386";
      case 0b0100: return "i486";
      case 0b0101: return "i486";
      case 0b0110:
        switch (processor_signature.model_number) {
          case 0b0001: return "Pentium Pro";
          case 0b0011: // OverDrive
          case 0b0101: return "Pentium II";
          case 0b0110: return "Celeron";
          case 0b0111:
          case 0b1000:
          case 0b1010:
          case 0b1011: return "Pentium III";
          case 0b1001: return "Pentium M";
          case 0b1101: return "Pentium M (90 nm)";
          case 0b1110: return "Core Duo or Core Solo (65nm)";
          case 0b1111: return "Core 2 Duo or Core 2 Quad (65nm)";
        }
        break;
      case 0b1111:
        switch (processor_signature.model_number) {
          case 0b0000: // model 00h
          case 0b0001: return "Pentium 4 (180 nm)"; // model 01h
          case 0b0010: return "Pentium 4 (130 nm)"; // model 02h
          case 0b0011: // model 03h
          case 0b0100: return "Pentium 4 (90 nm)"; // model 04h
          case 0b0110: return "Pentium 4 (65 nm)"; // model 06h
        }
        break;
    }
    return "Unknown processor signature";
  }

  const char* intel_extmodel_1_signature_string() {
    switch (processor_signature.family_code) {
      case 0b0110:
        switch (processor_signature.model_number) {
          case 0b0110: return "Celeron (65 nm)"; // model 16h
          case 0b0111: return "Core 2 Extreme (45 nm)"; // model 17h
          case 0b1100: return "Atom (45 nm)";
          case 0b1010: return "Core i7 (45 nm)";
          case 0b1101: return "Xeon MP (45 nm)";
        }
        break;
    }
    return "Unknown processor signature";
  }

  const char* intel_processor_signature_string() {
    switch (processor_signature.extended_model) {
    case 0: return intel_extmodel_0_signature_string();
    case 1: return intel_extmodel_1_signature_string();
    }
    return "Unknown processor signature (due to unknown extended model)";
  }

  void intel_fill_processor_signature() {
    cpuid_with_eax(1);
    processor_signature.full_bit_string  = eax;
    processor_signature.stepping_id      = MASK_RANGE_IN(eax,  3, 0);
    processor_signature.model_number     = MASK_RANGE_EX(eax,  7, 3);
    processor_signature.family_code      = MASK_RANGE_EX(eax, 11, 7);
    processor_signature.processor_type   = MASK_RANGE_EX(eax, 13, 11);
    processor_signature.extended_model   = MASK_RANGE_EX(eax, 19, 15);
    processor_signature.extended_family  = MASK_RANGE_EX(eax, 27, 19);
  }

  std::ostream& operator<<(std::ostream& out, const tag_processor_signature& sig) {
    return out << "{" << std::endl
                << "\textended family: " << sig.extended_family << std::endl
                << "\textended model:  " << sig.extended_model << std::endl
                << "\tprocessor type:  " << sig.processor_type << std::endl
                << "\tfamily code:     " << sig.family_code << std::endl
                << "\tmodel_number:    " << sig.model_number << std::endl
                << "\tstepping id:     " << sig.stepping_id << std::endl
                << "}";
  }

#endif

#ifndef __LP64__
// http://linux.derkeiler.com/Newsgroups/comp.os.linux.development.system/2008-01/msg00174.html
inline void cpuid_with_eax(uint in_eax) {
  __asm__ __volatile__(
      "pushl %%ebx\n\t"       // save %ebx for PIC code on OS X
      "cpuid\n\t"
      "movl %%ebx, %%esi\n\t" // save what cpuid put in ebx
      "popl %%ebx\n\t"       // restore ebx
          : "=a"(eax), "=S"(ebx), "=d"(edx), "=c"(ecx) // output
          : "a"(in_eax) // input in_eax to %eax
          );
}

inline void cpuid_with_eax_and_ecx(uint in_eax, uint in_ecx) {
  __asm__ __volatile__(
      "pushl %%ebx\n\t"       // save %ebx for PIC code on OS X
      "cpuid\n\t"
      "movl %%ebx, %%esi\n\t" // save what cpuid put in ebx
      "popl %%ebx\n\t"       // restore ebx
          : "=a"(eax), "=S"(ebx), "=d"(edx), "=c"(ecx) // output
          : "a"(in_eax), "c"(in_ecx) // input in_eax to %eax and in_ecx to %ecx
          );
}

uint64 rdtsc_unserialized() {
  uint64 ticks;
  __asm__ __volatile__("rdtsc": "=A" (ticks));
  return ticks;
}

#else // use 64 bit gas syntax
inline void cpuid_with_eax(uint in_eax) {
  __asm__ __volatile__(
      "pushq %%rbx\n\t"       // save %ebx for PIC code on OS X
      "cpuid\n\t"
      "movq %%rbx, %%rsi\n\t" // save what cpuid put in ebx
      "popq %%rbx\n\t"       // restore ebx
          : "=a"(eax), "=S"(ebx), "=d"(edx), "=c"(ecx) // output
          : "a"(in_eax) // input in_eax to %eax
          );
}

inline void cpuid_with_eax_and_ecx(uint in_eax, uint in_ecx) {
  __asm__ __volatile__(
      "pushq %%rbx\n\t"       // save %ebx for PIC code on OS X
      "cpuid\n\t"
      "movq %%rbx, %%rsi\n\t" // save what cpuid put in ebx
      "popq %%rbx\n\t"       // restore ebx
          : "=a"(eax), "=S"(ebx), "=d"(edx), "=c"(ecx) // output
          : "a"(in_eax), "c"(in_ecx) // input in_eax to %eax and in_ecx to %ecx
          );
}

uint64 rdtsc_unserialized() {
  uint a, d;
  __asm__ __volatile__("rdtsc": "=a"(a), "=d"(d));
  return MERGE_HI_LO(d, a);
}
#endif

uint64 rdtsc_serialized() {
  cpuid_with_eax(0);
  uint64 ticks;
  __asm__ __volatile__("rdtsc": "=A" (ticks));
  return ticks;
}



void intel_fill_processor_features(cpuid_info& info) {
  cpuid_with_eax(1);
  for (unsigned i = 0; i < ARRAY_SIZE(intel_feature_bits); ++i) {
    feature_bit f(intel_feature_bits[i]);
    info.features[f.name] = BIT_IS_SET(reg[f.reg], f.offset);
  }

  info.processor_features.threads = MASK_RANGE_IN(ebx, 23, 16);

  cpuid_with_eax(0x80000001);
  for (unsigned i = 0; i < ARRAY_SIZE(intel_ext_feature_bits); ++i) {
    feature_bit f(intel_ext_feature_bits[i]);
    info.features[f.name] = BIT_IS_SET(reg[f.reg], f.offset);
  }

  if (info.features["monitor"]) {
    cpuid_with_eax(5);
    info.processor_features.monitor_features.min_line_size = MASK_RANGE_IN(eax, 15, 0);
    info.processor_features.monitor_features.max_line_size = MASK_RANGE_IN(ebx, 15, 0);
  } else {
    info.processor_features.monitor_features.min_line_size = 0;
    info.processor_features.monitor_features.max_line_size = 0;
  }
}

void amd_fill_processor_features(cpuid_info& info) {
  cpuid_with_eax(1);
  for (unsigned i = 0; i < ARRAY_SIZE(amd_feature_bits); ++i) {
    feature_bit f(amd_feature_bits[i]);
    info.features[f.name] = BIT_IS_SET(reg[f.reg], f.offset);
  }

  if (info.features["htt"]) {
    info.processor_features.threads = MASK_RANGE_IN(ebx, 23, 16);
  } else {
    info.processor_features.threads = 1;
  }

  cpuid_with_eax(0x80000001);
  for (unsigned i = 0; i < ARRAY_SIZE(amd_ext_feature_bits); ++i) {
    feature_bit f(amd_ext_feature_bits[i]);
    info.features[f.name] = BIT_IS_SET(reg[f.reg], f.offset);
  }

  if (info.features["monitor"]) {
    cpuid_with_eax(5);
    info.processor_features.monitor_features.min_line_size = MASK_RANGE_IN(eax, 15, 0);
    info.processor_features.monitor_features.max_line_size = MASK_RANGE_IN(ebx, 15, 0);
  } else {
    info.processor_features.monitor_features.min_line_size = 0;
    info.processor_features.monitor_features.max_line_size = 0;
  }
}

tag_processor_cache_parameter_set amd_L1_cache_parameters(int reg) {
    tag_processor_cache_parameter_set cache = { 0 };
    cache.size_in_bytes              = 1024 * MASK_RANGE_IN(reg, 31, 24);
    cache.system_coherency_line_size = MASK_RANGE_IN(reg, 7, 0);
    cache.sets                       = MASK_RANGE_IN(reg, 23, 16);
    cache.ways                       = MASK_RANGE_IN(reg, 15, 8);
    cache.cache_level                = 1;
    return cache;
}

int amd_l2_l3_cache_assoc(int bits) {
  switch (bits) {
    case 0x6: return 8;
    case 0x8: return 16;
    case 0xA: return 32;
    case 0xB: return 48;
    case 0xC: return 64;
    case 0xD: return 96;
    case 0xE: return 128;
  }
  return bits;
}

tag_processor_cache_parameter_set amd_L2_cache_parameters(int reg) {
    tag_processor_cache_parameter_set cache = { 0 };
    cache.system_coherency_line_size = MASK_RANGE_IN(reg, 7, 0);
    cache.sets = amd_l2_l3_cache_assoc(MASK_RANGE_IN(reg, 15, 12));
    cache.ways                       = MASK_RANGE_IN(reg, 11, 8);
    cache.cache_type = cache_type_tag('u');
    return cache;
}


void amd_fill_processor_caches(cpuid_info& info) {
  uint max_eax = info.max_ext_eax;
  if (  max_eax >= 0x80000005) {
    cpuid_with_eax(0x80000005);
    tag_processor_cache_parameter_set L1i = amd_L1_cache_parameters(edx);
    L1i.cache_type = cache_type_tag('i');
    info.processor_cache_parameters.push_back(L1i);

    tag_processor_cache_parameter_set L1d = amd_L1_cache_parameters(ecx);
    L1d.cache_type = cache_type_tag('d');
    info.processor_cache_parameters.push_back(L1d);
  }

  if (  max_eax >= 0x80000006) {
    cpuid_with_eax(0x80000006);
    tag_processor_cache_parameter_set L2 = amd_L2_cache_parameters(ecx);
    L2.size_in_bytes = 1024 * MASK_RANGE_IN(ecx, 31, 16);
    L2.cache_level = 2;
    info.processor_cache_parameters.push_back(L2);

    tag_processor_cache_parameter_set L3 = amd_L2_cache_parameters(edx);
    L3.size_in_bytes = 512 * 1024 * MASK_RANGE_IN(edx, 31, 18);
    L3.cache_level = 3;
    info.processor_cache_parameters.push_back(L3);
  }
}

void intel_set_cache_properties(tag_processor_cache_descriptor& cache,
      int size, int ways, int entries_or_linesize, bool sectored = false) {
  cache.size = size;
  cache.set_assoc_ways = ways;
  cache.entries_or_linesize = entries_or_linesize;
  cache.sectored = sectored;
}

void intel_decode_cache_descriptor(cpuid_info& info, unsigned char v) {
  const int KB = 1024;
  const int MB = KB * KB;

  switch (v) {
  case 0x01: return intel_set_cache_properties(info.processor_cache_descriptors.TLBi, 4*KB, 4, 32);
  case 0x02: return intel_set_cache_properties(info.processor_cache_descriptors.TLBi, 4*MB, 0, 2);
  case 0x03: return intel_set_cache_properties(info.processor_cache_descriptors.TLBd, 4*KB, 4, 64);
  case 0x04: return intel_set_cache_properties(info.processor_cache_descriptors.TLBd, 4*MB, 4, 8);
  case 0x05: return intel_set_cache_properties(info.processor_cache_descriptors.TLBd, 4*MB, 4, 32);
  case 0x06: return intel_set_cache_properties(info.processor_cache_descriptors.L1i, 8*KB, 4, 32);
  case 0x08: return intel_set_cache_properties(info.processor_cache_descriptors.L1i, 16*KB, 4, 32);
  case 0x09: return intel_set_cache_properties(info.processor_cache_descriptors.L1i, 32*KB, 4, 64);
  case 0x0A: return intel_set_cache_properties(info.processor_cache_descriptors.L1d, 8*KB, 2, 32);
  case 0x0C: return intel_set_cache_properties(info.processor_cache_descriptors.L1d, 16*KB, 4, 32);
  case 0x0D: return intel_set_cache_properties(info.processor_cache_descriptors.L1d, 16*KB, 4, 64); // also ECC...
  case 0x21: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 256*KB, 8, 64);
  case 0x22: return intel_set_cache_properties(info.processor_cache_descriptors.L3, 512*KB, 4, 64, true);
  case 0x23: return intel_set_cache_properties(info.processor_cache_descriptors.L3, 1*MB, 8, 64, true);
  case 0x25: return intel_set_cache_properties(info.processor_cache_descriptors.L3, 2*MB, 8, 64, true);
  case 0x29: return intel_set_cache_properties(info.processor_cache_descriptors.L3, 4*MB, 8, 64, true);
  case 0x2C: return intel_set_cache_properties(info.processor_cache_descriptors.L1d, 32*KB, 8, 64);
  case 0x30: return intel_set_cache_properties(info.processor_cache_descriptors.L1i, 32*KB, 8, 64);
  case 0x39: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 128*KB, 8, 64, true);
  case 0x3A: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 192*KB, 6, 64, true);
  case 0x3B: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 128*KB, 2, 64, true);
  case 0x3C: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 256*KB, 4, 64, true);
  case 0x3D: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 384*KB, 6, 64, true);
  case 0x3E: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 512*KB, 4, 64, true);
  case 0x40: return; // no L2 (or L3) cache                        _descriptors
  case 0x41: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 128*KB, 4, 32);
  case 0x42: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 256*KB, 4, 32);
  case 0x43: return intel_set_cache_properties(info.processor_cache_descriptors.L2, 512*KB, 4, 32);
    // TODO: http://www.intel.com/Assets/PDF/appnote/241618.pdf page 27
    // TODO: http://www.intel.com/Assets/PDF/appnote/241618.pdf page 28
  }
}

void intel_add_processor_cache_parameters(cpuid_info& info) {
  tag_processor_cache_parameter_set   params;

  params.reserved_APICS                = MASK_RANGE_IN(eax, 31, 26) + 1;
  params.sharing_threads               = MASK_RANGE_IN(eax, 25, 14) + 1;
  params.fully_associative             = BIT_IS_SET(eax, 9);
  params.self_initializing_cache_level = BIT_IS_SET(eax, 8);
  params.cache_level                   = MASK_RANGE_IN(eax, 7, 5);
  params.cache_type                    = MASK_RANGE_IN(eax, 4, 0);
  params.ways                          = MASK_RANGE_IN(ebx, 31, 22) + 1;
  params.physical_line_partitions      = MASK_RANGE_IN(ebx, 21, 12) + 1;
  params.system_coherency_line_size    = MASK_RANGE_IN(ebx, 11, 0) + 1;
  params.sets                          = ecx + 1;
  params.inclusive                     = BIT_IS_SET(edx, 1);
  params.inclusive_behavior            = BIT_IS_SET(edx, 0);

  params.size_in_bytes = params.ways * params.physical_line_partitions
                       * params.system_coherency_line_size * params.sets;

  info.processor_cache_parameters.push_back(params);
}

void intel_fill_processor_caches(cpuid_info& info) {
  info.processor_cache_descriptors.TLBi.entries_or_linesize = 0;
  info.processor_cache_descriptors.TLBd.entries_or_linesize = 0;
  info.processor_cache_descriptors.L1i.entries_or_linesize = 0;
  info.processor_cache_descriptors.L1d.entries_or_linesize = 0;
  info.processor_cache_descriptors.L2.entries_or_linesize = 0;
  info.processor_cache_descriptors.L3.entries_or_linesize = 0;

  cpuid_with_eax(2);

  // TODO: function 4
  uint in_ecx = 0;
  cpuid_with_eax_and_ecx(4, in_ecx);
  do {
    intel_add_processor_cache_parameters(info);
    cpuid_with_eax_and_ecx(4, ++in_ecx);
  } while(MASK_RANGE_IN(eax, 4, 0) != 0);
}

// TODO: test EFLAGS first
// TODO: function 5
// TODO: function 8000_0006
// TODO: function 8000_0008
// TODO: denormals-are-zero

uint cpuid_vendor_id_and_max_basic_eax_input(cpuid_info& info) {
  cpuid_with_eax(0);
  ((uint*)info.vendor_id)[0] = ebx;
  ((uint*)info.vendor_id)[1] = edx;
  ((uint*)info.vendor_id)[2] = ecx;
  return eax;
}

// http://www.intel.com/Assets/PDF/appnote/241618.pdf page 13
uint cpuid_max_acceptable_extended_eax_input() {
  cpuid_with_eax(0x80000000);
  return eax;
}

// http://www.intel.com/Assets/PDF/appnote/241618.pdf page 13
bool intel_was_cpuid_input_acceptable(uint eax) {
  return (eax & BIT(31)) == 0;
}

void fill_brand_string_helper(cpuid_info& info, int offset) {
  ((uint*)info.brand_string)[offset + 0] = eax;
  ((uint*)info.brand_string)[offset + 1] = ebx;
  ((uint*)info.brand_string)[offset + 2] = ecx;
  ((uint*)info.brand_string)[offset + 3] = edx;
}

void cpuid_fill_brand_string(cpuid_info& info) {
  cpuid_with_eax(0x80000002);
  fill_brand_string_helper(info, 0);
  cpuid_with_eax(0x80000003);
  fill_brand_string_helper(info, 4);
  cpuid_with_eax(0x80000004);
  fill_brand_string_helper(info, 8);
}

void estimate_rdtsc_overhead(cpuid_info& info) {
  uint64 a, b;
  a = rdtsc_serialized();
  b = rdtsc_serialized();
  info.rdtsc_serialized_overhead_cycles = double(b - a);

  a = rdtsc_unserialized();
  b = rdtsc_unserialized();
  info.rdtsc_unserialized_overhead_cycles = double(b - a);
}


bool cpuid_introspect(cpuid_info& info) {
  info.vendor_id[12] = '\0';

  info.max_basic_eax = cpuid_vendor_id_and_max_basic_eax_input(info);
  info.max_ext_eax = cpuid_max_acceptable_extended_eax_input();

  cpuid_fill_brand_string(info);

  init_all_features_to_false(info);

  if (std::string("GenuineIntel") == info.vendor_id) {
    intel_fill_processor_caches(info);
    intel_fill_processor_features(info);
    //intel_detect_processor_topology();
  } else if (std::string("AuthenticAMD") == info.vendor_id) {
    amd_fill_processor_features(info);
    amd_fill_processor_caches(info);
    if (info.max_ext_eax >= 0x80000008) {
      cpuid_with_eax(0x80000008);
      info.max_linear_address_size = MASK_RANGE_IN(eax, 15, 8);
      info.max_physical_address_size = MASK_RANGE_IN(eax, 7, 0);
    }
  } else {
    // Unknown vendor ID!
    return false;
  }

  if (info.features["tsc"]) {
    estimate_rdtsc_overhead(info);
  }
  return true;
}

