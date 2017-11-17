set (cycle_ROOT ${PROJECT_SOURCE_DIR}/third_party/fftw_cycle/)

add_library(cycle STATIC
  ${cycle_ROOT}/cycle-wrapper.cpp
)

include_directories(${cycle_ROOT})

