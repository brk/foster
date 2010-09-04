set (imath_VERSION 1.14)
set (imath_ROOT ${PROJECT_SOURCE_DIR}/third_party/imath/imath-${imath_VERSION})

add_library(imath STATIC
  ${imath_ROOT}/imath.c
  ${imath_ROOT}/iprime.c
  ${imath_ROOT}/imrat.c
  )

include_directories(${imath_ROOT})

