set (imath_VERSION 1.14)
set (imath_ROOT ${PROJECT_SOURCE_DIR}/third_party/imath/imath-${imath_VERSION})

add_custom_command(
  OUTPUT ${PROJECT_BINARY_DIR}/_generated_/imath.h
  COMMAND
    python ${imath_ROOT}/generate-imath.h.py
           ${imath_ROOT}/imath.in.h
           ${PROJECT_BINARY_DIR}/_generated_/imath.h
           -C ${CMAKE_CXX_COMPILER}
           -F "${CMAKE_CXX_CFLAGS}"
  VERBATIM
  DEPENDS
    ${imath_ROOT}/imath.in.h
    ${imath_ROOT}/generate-imath.h.py
  )
add_custom_target(imath_h DEPENDS ${PROJECT_BINARY_DIR}/_generated_/imath.h)

add_library(imath STATIC
  ${imath_ROOT}/imath.c
  ${imath_ROOT}/iprime.c
  ${imath_ROOT}/imrat.c
  )

set_target_properties(imath PROPERTIES
    COMPILE_FLAGS -I${PROJECT_BINARY_DIR}/_generated_
)

add_dependencies(imath imath_h)

include_directories(${imath_ROOT})

