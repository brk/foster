#ifndef FOSTER_RUNTIME_STAT_TRACKER_H
#define FOSTER_RUNTIME_STAT_TRACKER_H

#include <vector>
#include <algorithm>
#include <numeric>

template<typename T>
struct stat_tracker {
  int  idx;
  int  idx_max;
  std::vector<T> samples;
  stat_tracker() : idx(0), idx_max(0) {}

  void resize(size_t sz) { samples.resize(sz); }

  void record_sample(T v) {
    samples[idx] = v;
    if (idx > idx_max) { idx_max = idx; }
    idx = (idx + 1) % int(samples.size());
  }

  T compute_min() const {
    return *std::min_element(samples.begin(), samples.end());
  }

  T compute_max() const {
    return *std::max_element(samples.begin(), samples.end());
  }

  T compute_avg_arith() const {
    return std::accumulate(samples.begin(), samples.end(), T(0)) /
                                                              T(samples.size());
  }
};

#endif
