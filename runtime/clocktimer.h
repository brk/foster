// Minimalist, header-only platform wrapper around high-resolution timer sources.
// Significantly inspired by plf_nanotimer:
// https://github.com/mattreecebentley/plf_nanotimer

#include <cstdint>

#if defined(_WIN32)

#define VC_EXTRALEAN
#define WIN32_LEAN_AND_MEAN
#include <windows.h>

class clocktimer {
public:
  clocktimer() {
    LARGE_INTEGER f;
    QueryPerformanceFrequency(&f);
    // (t * 1e9) / (t/s) ==> t * (1e9 / (t/s))
    freq_ns = 1e9 / double(f.QuadPart);
  }
  void start() { QueryPerformanceCounter(&st); }
  double elapsed_ns_d() {
    QueryPerformanceCounter(&nd);
    return double(nd.QuadPart - st.QuadPart) * freq_ns;
  }
  uint64_t elapsed_ns() { return uint64_t(elapsed_ns_d()); }
  double elapsed_us() { return elapsed_ns_d() / 1e3; }
  double elapsed_ms() { return elapsed_ns_d() / 1e6; }
  double elapsed_s()  { return elapsed_ns_d() / 1e9; }

  static uint64_t current_us() {
    LARGE_INTEGER v;
    LARGE_INTEGER f;
    QueryPerformanceCounter(&v);
    QueryPerformanceFrequency(&f);

    return uint64_t((double(v.QuadPart) / double(f.QuadPart)) * 1e6);
  }

private:
  LARGE_INTEGER st, nd; double freq_ns;
};

#else

class clocktimer {
public:
  clocktimer() {}
  void start() { if (ENABLE_CLOCKTIMER) clock_gettime(CLOCK_MONOTONIC, &st); }
  double elapsed_ns_d() { return double(elapsed_ns()); }
  uint64_t elapsed_ns() {
    if (!ENABLE_CLOCKTIMER) return 0;

    clock_gettime(CLOCK_MONOTONIC, &nd);
    return (1000000000 * (nd.tv_sec - st.tv_sec)) + (nd.tv_nsec - st.tv_nsec);
  }
  double elapsed_us() { return elapsed_ns_d() / 1e3; }
  double elapsed_ms() { return elapsed_ns_d() / 1e6; }
  double elapsed_s()  { return elapsed_ns_d() / 1e9; }

  static uint64_t current_us() {
    struct timespec curr;
    clock_gettime(CLOCK_MONOTONIC, &curr);
    return (1000000 * curr.tv_sec) + (curr.tv_nsec / 1000);
  }

private:
  struct timespec st, nd;
};

#endif
