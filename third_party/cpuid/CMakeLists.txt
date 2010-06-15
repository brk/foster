set (CPUID_ROOT ${PROJECT_SOURCE_DIR}/third_party/cpuid)

add_library(cpuid STATIC ${CPUID_ROOT}/cpuid.cpp)
