set (gtest_ROOT ${PROJECT_SOURCE_DIR}/third_party/gtest)
set (gtest_SOURCE_ROOT ${gtest_ROOT}/fused-src)
set (gtest_SOURCE_DIR ${gtest_SOURCE_ROOT}/gtest)

include_directories(${gtest_SOURCE_ROOT})

# The following rules are copied from the gtest standard
# CMakeLists.txt, which is not included in its entirety
# because it assumes that gtest is the root project

if (MSVC)
  # Newlines inside flags variables break CMake's NMake generator.
  set(cxx_base_flags "-GS -W4 -WX -wd4275 -nologo -J -Zi")
  set(cxx_base_flags "${cxx_base_flags} -D_UNICODE -DUNICODE -DWIN32 -D_WIN32")
  set(cxx_base_flags "${cxx_base_flags} -DSTRICT -DWIN32_LEAN_AND_MEAN")
  set(cxx_exception_flags "-EHsc -D_HAS_EXCEPTIONS=1")
  set(cxx_no_exception_flags "-D_HAS_EXCEPTIONS=0")
  set(cxx_no_rtti_flags "-GR-")
elseif (CMAKE_COMPILER_IS_GNUCXX)
  set(cxx_base_flags "-Wall -Wshadow")
  set(cxx_exception_flags "-fexceptions")
  set(cxx_no_exception_flags "-fno-exceptions")
  # Until version 4.3.2, GCC doesn't define a macro to indicate
  # whether RTTI is enabled.  Therefore we define GTEST_HAS_RTTI
  # explicitly.
  set(cxx_no_rtti_flags "-fno-rtti -DGTEST_HAS_RTTI=0")
  set(cxx_strict_flags "-Wextra")
elseif (CMAKE_CXX_COMPILER_ID STREQUAL "SunPro")
  set(cxx_exception_flags "-features=except")
  # Sun Pro doesn't provide macros to indicate whether exceptions and
  # RTTI are enabled, so we define GTEST_HAS_* explicitly.
  set(cxx_no_exception_flags "-features=no%except -DGTEST_HAS_EXCEPTIONS=0")
  set(cxx_no_rtti_flags "-features=no%rtti -DGTEST_HAS_RTTI=0")
elseif (CMAKE_CXX_COMPILER_ID STREQUAL "VisualAge" OR
        CMAKE_CXX_COMPILER_ID STREQUAL "XL")
  # CMake 2.8 changes Visual Age's compiler ID to "XL".
  set(cxx_exception_flags "-qeh")
  set(cxx_no_exception_flags "-qnoeh")
  # Until version 9.0, Visual Age doesn't define a macro to indicate
  # whether RTTI is enabled.  Therefore we define GTEST_HAS_RTTI
  # explicitly.
  set(cxx_no_rtti_flags "-qnortti -DGTEST_HAS_RTTI=0")
endif()

if (CMAKE_USE_PTHREADS_INIT)  # The pthreads library is available.
  set(cxx_base_flags "${cxx_base_flags} -DGTEST_HAS_PTHREAD=1")
endif()

# For building gtest's own tests and samples.
set(cxx_exception "${CMAKE_CXX_FLAGS} ${cxx_base_flags} ${cxx_exception_flags}")
set(cxx_no_exception
    "${CMAKE_CXX_FLAGS} ${cxx_base_flags} ${cxx_no_exception_flags}")
set(cxx_default "${cxx_exception}")
set(cxx_no_rtti "${cxx_default} ${cxx_no_rtti_flags}")
set(cxx_use_own_tuple "${cxx_default} -DGTEST_USE_OWN_TR1_TUPLE=1")

# For building the gtest libraries.
set(cxx_strict "${cxx_default} ${cxx_strict_flags}")

########################################################################
#
# Defines the gtest & gtest_main libraries.  User tests should link
# with one of them.
function(cxx_library_with_type name type cxx_flags)
  # type can be either STATIC or SHARED to denote a static or shared library.
  # ARGN refers to additional arguments after 'cxx_flags'.
  add_library(${name} ${type} ${ARGN})
  set_target_properties(${name}
    PROPERTIES
    COMPILE_FLAGS "${cxx_flags}")
    if (CMAKE_USE_PTHREADS_INIT)
      target_link_libraries(${name} ${CMAKE_THREAD_LIBS_INIT})
    endif()
endfunction()

# Static versions of Google Test libraries.  We build them using more
# strict warnings than what are used for other targets, to ensure that
# gtest can be compiled by a user aggressive about warnings.
cxx_library_with_type(gtest      STATIC "${cxx_strict}" ${gtest_SOURCE_DIR}/gtest-all.cc)
cxx_library_with_type(gtest_main STATIC "${cxx_strict}" ${gtest_SOURCE_DIR}/gtest_main.cc)
target_link_libraries(gtest_main gtest)

