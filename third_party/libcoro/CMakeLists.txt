set (libcoro_ROOT ${PROJECT_SOURCE_DIR}/third_party/libcoro/libcoro)

set_source_files_properties(
  ${libcoro_ROOT}/coro.c
  PROPERTIES
  COMPILE_DEFINITIONS ${CORO_METHOD})

add_library(coro STATIC ${libcoro_ROOT}/coro.c)
include_directories(${libcoro_ROOT})

