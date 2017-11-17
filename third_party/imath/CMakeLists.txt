set (imath_VERSION 1.17)
set (imath_ROOT ${PROJECT_SOURCE_DIR}/third_party/imath/imath-${imath_VERSION})

add_library(imath STATIC
  ${imath_ROOT}/imath.c
  ${imath_ROOT}/iprime.c
  ${imath_ROOT}/imrat.c
  )

# Copy imath.h to _generated_/ so that it's easier to include in the runtime.
add_custom_target(imath_h DEPENDS ${PROJECT_BINARY_DIR}/_generated_/imath.h)
add_custom_command(
  OUTPUT ${PROJECT_BINARY_DIR}/_generated_/imath.h
  COMMAND ${CMAKE_COMMAND} -E copy
           ${imath_ROOT}/imath.h
           ${PROJECT_BINARY_DIR}/_generated_/imath.h
  DEPENDS
    ${PROJECT_BINARY_DIR}/_generated_
    ${imath_ROOT}/imath.h
  )

add_dependencies(imath imath_h)

include_directories(${imath_ROOT})

