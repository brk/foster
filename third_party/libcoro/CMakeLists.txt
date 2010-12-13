set (libcoro_ROOT ${PROJECT_SOURCE_DIR}/third_party/libcoro/libcoro)

set (CORO_METHOD CORO_ASM
    DOC "libcoro implementation: CORO_{ASM,SJLJ,LOSER,PTHREAD}")

#add_custom_command(
#  OUTPUT ${PROJECT_BINARY_DIR}/libcoro.h
#  COMMAND
#    python ${imath_ROOT}/generate-imath.h.py
#           ${imath_ROOT}/imath.in.h
#           ${PROJECT_BINARY_DIR}/imath.h
#           -C ${CMAKE_CXX_COMPILER}
#           -F "${CMAKE_CXX_CFLAGS}"
#  VERBATIM
#  DEPENDS
#    ${imath_ROOT}/imath.in.h
#    ${imath_ROOT}/generate-imath.h.py
#  )
#add_custom_target(imath_h DEPENDS ${PROJECT_BINARY_DIR}/imath.h)

set_source_files_properties(${libcoro_ROOT}/coro.c PROPERTIES
  COMPILE_DEFINITIONS ${CORO_METHOD})

add_library(coro STATIC ${libcoro_ROOT}/coro.c)
include_directories(${libcoro_ROOT})

