cmake_minimum_required (VERSION 3.4.3)

# {{{ We need to set up the compiler paths before calling project()...
# ~~~~~~~~~~~~~~~~~~~~

set(PYTHON python2)
set(LLVM_VERSION 6.0.0)

find_program(LLVM_CONFIG NAMES llvm-config llvm-config-${LLVM_VERSION}
  PATHS
    $ENV{HOME}/llvm/${LLVM_VERSION}/bin
    $ENV{HOME}/sw/local/llvm-${LLVM_VERSION}/bin
    $ENV{HOME}/sw/local/llvm/${LLVM_VERSION}/bin
    /usr/lib/llvm-${LLVM_VERSION}/bin
  DOC "llvm-config"
  NO_SYSTEM_ENVIRONMENT_PATH)
# In case the paths above didn't work, fall back to the system path.
find_program(LLVM_CONFIG NAMES llvm-config llvm-config-${LLVM_VERSION})

execute_process(COMMAND ${LLVM_CONFIG} --bindir OUTPUT_VARIABLE LLVM_BINDIR)

# If llvm-config isn't found, LLVM_BINDIR will be empty
# and CMake will report an error here.
string(REPLACE "\n" "" LLVM_BINDIR ${LLVM_BINDIR})

set(CLANG   ${LLVM_BINDIR}/clang++)
set(CLANG_C ${LLVM_BINDIR}/clang)

# We need to build our runtime with Clang in order to get LLVM bitcode,
# which means that we need to build everything that the runtime links
# against with Clang as well, since other compilers might make different
# choices about ABI and/or name mangling.
set(CMAKE_CXX_COMPILER ${CLANG})
set(CMAKE_C_COMPILER ${CLANG_C})

# ~~~~~~~~~~~~~~~~~~~~
# ... Okay, now we can proceed.
# }}}

project (foster)

# Uses of the CMAKE_CXX_COMPILER variable will now come from the cache,
# which might be different than the value we set above. Whelp...
if (NOT (${CMAKE_CXX_COMPILER} STREQUAL ${CLANG}))
  message("CMake wants to use a C++ compiler (${CMAKE_CXX_COMPILER}) that's not the version of Clang we want (${CLANG}).")
  message("To fix this, I'm afriad you'll need to blow away CMake's cache and rebuild. Sorry!")
  message("Oh, and just to make things extra fun, if you were unfortunate enough to compile LLVM with GCC 5,")
  message("  you'll need to recompile and reinstall with either GCC 4.x or LLVM, thanks to GCC's cxx11_abi tags.")
  message("Blergh.")
  return()
endif (NOT (${CMAKE_CXX_COMPILER} STREQUAL ${CLANG}))

cmake_policy(VERSION 3.0)

####################### Configuration Rules ########################

set(LIBRARY_OUTPUT_PATH ${PROJECT_BINARY_DIR}/_nativelibs_)
set(GENERATED           ${PROJECT_BINARY_DIR}/_generated_)

# {{{ ~~~~~~~~~~~~~~~~~~~~ ANTLR ~~~~~~~~~~~~~~~~~~~~~

# This isn't cached since CMake doesn't seem to have any way of
# specifying that some cached variables depend on others, and it's
# sort of annoying to see the option to change it AFTER the paths
# that depend on it have been presented...
set(ANTLR_VERSION 3.4)
find_path(ANTLR_DIR antlr-${ANTLR_VERSION}.jar
  PATHS $ENV{HOME}/antlr/${ANTLR_VERSION}
        $ENV{HOME}/sw/local/antlr/${ANTLR_VERSION}
  DOC   "ANTLR library install dir")
set(ANTLR_JAR ${ANTLR_DIR}/antlr-${ANTLR_VERSION}.jar
    CACHE FILEPATH "ANTLR jarfile")
set(ANTLR_LIBDIR ${ANTLR_DIR}/lib)

if (${ANTLR_DIR} STREQUAL "ANTLR_DIR-NOTFOUND")
    message("ANTLR not found! Please configure with ccmake or a CMake GUI")
    return()
endif (${ANTLR_DIR} STREQUAL "ANTLR_DIR-NOTFOUND")
# }}}

if (NOT EXISTS ${LIBRARY_OUTPUT_PATH}/nacl)
  if   (EXISTS ${PROJECT_SOURCE_DIR}/third_party/nacl-20110221/build/foster)
    file (COPY ${PROJECT_SOURCE_DIR}/third_party/nacl-20110221/build/foster/lib
          DESTINATION ${LIBRARY_OUTPUT_PATH}/nacl)
  else (EXISTS ${PROJECT_SOURCE_DIR}/third_party/nacl-20110221/build/foster)
    message("Please cd to  ${PROJECT_SOURCE_DIR}/third_party/nacl-20110221/    and run  ./do")
    return()
  endif (EXISTS ${PROJECT_SOURCE_DIR}/third_party/nacl-20110221/build/foster)
endif (NOT EXISTS ${LIBRARY_OUTPUT_PATH}/nacl)

# {{{ ~~~~~~~~~~~~~~~~~~~~ libcoro ~~~~~~~~~~~~~~~~~~~~~~
set(CORO_METHOD CORO_ASM
    CACHE
    DOC "libcoro implementation: CORO_{ASM,SJLJ,LOSER,PTHREAD}")
# }}}

# {{{ ~~~~~~~~~~~~~~~~~~~~ Cap'n Proto ~~~~~~~~~~~~~~~~~~~~~~

find_program(CAPNP NAMES capnp
  PATHS
    $ENV{HOME}/.local/capnp-c++-0.6.1/bin
    $ENV{HOME}/sw/local/capnp-c++-0.6.1/bin
  DOC "capnp: Cap'n Proto compiler driver")

find_program(MINUPROTO NAMES minuproto
  PATHS
    $ENV{HOME}/.cabal/bin
    ${PROJECT_SOURCE_DIR}/compiler/me/.cabal-sandbox/bin
  DOC "Cap'n Proto plugin to generate Haskell code from .capnp files")

get_filename_component(CAPNP_BIN_DIR ${CAPNP} DIRECTORY)
set(CAPNP_DIR ${CAPNP_BIN_DIR}/..)

# }}}

# {{{ ~~~~~~~~~~~~~~~~~~~~~~~~~ LLVM ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

# Get flags for LLVM
execute_process(COMMAND ${LLVM_CONFIG} --cxxflags
  OUTPUT_VARIABLE LLVM_ORIGINAL_CFLAGS
)

# We want to control whether our binaries are compiled
# in debug mode independently of whether LLVM was so compiled.
# Stripping -DNDEBUG can cause problems with CallGraph analysis,
# so we simply leave it and use a custom ASSERT() instead of the
# standard <cassert> macro.
#
string(REPLACE "-g"          "" LLVM_CFLAGS "${LLVM_ORIGINAL_CFLAGS}")
string(REPLACE "-ggdb"       "" LLVM_CFLAGS "${LLVM_CFLAGS}")

# LLVM libraries may also be compiled with -fno-rtti.
# We are free to compile almost all of our code with RTTI,
# except for LLVM plugins, which inherit from LLVM classes and
# therefore must agree on whether to expect and use typeinfo or not.
#
set (NO_RTTI_FLAG "-fno-rtti")
set (NDEBUG_FLAG "-DNDEBUG")
string(REPLACE ${NO_RTTI_FLAG} "" LLVM_CFLAGS "${LLVM_CFLAGS}")
string(REPLACE ${NDEBUG_FLAG} "" LLVM_CFLAGS "${LLVM_CFLAGS}")
# Note: we unconditionally remove this flag here
# (because we can't compile C-only code with it)
# and unconditionally add it to CXXFLAGS later.
string(REPLACE "-std=c++11" "" LLVM_CFLAGS "${LLVM_CFLAGS}")
string(REPLACE "-std=c++14" "" LLVM_CFLAGS "${LLVM_CFLAGS}")

# llvm-config reports flags for the compiler used to build it,
# which may result in flags for GCC that clang++ chokes on.
#   https://bugs.llvm.org//show_bug.cgi?id=24979
string(REPLACE "-Wno-maybe-uninitialized" "" LLVM_CFLAGS "${LLVM_CFLAGS}")

# Make sure we don't have any extraneous newlines in generated Makefiles
#
string(STRIP "${LLVM_ORIGINAL_CFLAGS}" LLVM_ORIGINAL_CFLAGS)

# We've already set most of llvm-config's flags above via LLVM_CFLAGS;
# here, we just want to set the flags we removed from LLVM_CFLAGS,
# for programs which must compile without RTTI for LLVM compatibility.
#
set (LLVM_EXTRA_CFLAGS "")

   if (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NO_RTTI_FLAG})
  set (LLVM_EXTRA_CFLAGS "${LLVM_EXTRA_CFLAGS} ${NO_RTTI_FLAG}")
endif (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NO_RTTI_FLAG})

   if (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NDEBUG_FLAG})
  set (LLVM_EXTRA_CFLAGS "${LLVM_EXTRA_CFLAGS} ${NDEBUG_FLAG}")
endif (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NDEBUG_FLAG})


execute_process(COMMAND ${LLVM_CONFIG} --libfiles OUTPUT_VARIABLE LLVM_LIBS)
execute_process(COMMAND ${LLVM_CONFIG} --libdir OUTPUT_VARIABLE LLVM_LIBDIR)

string(STRIP "${LLVM_LIBS}" LLVM_LIBS)
string(STRIP "${LLVM_LIBDIR}" LLVM_LIBDIR)

# Unfortunately CMake does the wrong thing when we try to link against
# LLVM when the OS includes libLLVM in the system lib directory.
set(LLVM_LDFLAGS "-L${LLVM_LIBDIR} ${LLVM_LIBS}")

# (X)Ubuntu 17.10 ships with LLVM 5.0 in /usr/lib/x86_64-linux-gnu/libLLVM-5.0.so
# which confuses CMake into thinking it doesn't need to provide an RPATH
# entry for the LLVM version we're compiling against, even though our version
# is likely built with a different ABI.

# use, i.e. don't skip the full RPATH for the build tree
SET(CMAKE_SKIP_BUILD_RPATH        FALSE)
SET(CMAKE_BUILD_WITH_INSTALL_RPATH TRUE)
SET(CMAKE_INSTALL_RPATH "${LLVM_LIBDIR}:${ANTLR_LIBDIR}")

# }}}

####################### Compilation Rules ##########################

# Just run these every time we build... CMake seems to have trouble
# with the concept of having a target depend on a directory.
execute_process(COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_generated_)
execute_process(COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_bitcodelibs_)
execute_process(COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_nativelibs_)

# {{{ Use python to build fosterParser.c when grammar/foster.g changes
add_custom_command(
  OUTPUT ${GENERATED}/fosterParser.c
         ${GENERATED}/fosterLexer.c
         ${GENERATED}/fosterLexer.h

  # Make sure later stages fail if this stage fails.
  COMMAND rm -f ${GENERATED}/fosterLexer.h

  COMMAND ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
                    ${ANTLR_JAR}
                    ${GENERATED}
                    ${PROJECT_SOURCE_DIR}/grammar/foster.g
  DEPENDS
        ${PROJECT_SOURCE_DIR}/grammar/foster.g
        ${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
)
# }}}

# {{{ Re-generate the Tokens.hs file when the ANTLR-generated tokens change.
add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Tokens.hs
  COMMAND
    ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/extract-antlr3-token-ids.py
           ${GENERATED}/fosterLexer.h
                > ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Tokens.hs
  DEPENDS
    ${PROJECT_SOURCE_DIR}/scripts/extract-antlr3-token-ids.py
    ${GENERATED}/fosterLexer.h
)
# }}} -----------------------------------------------------------

# {{{ Generate C++ code to read serialized FosterIL capnproto buffers.
add_custom_command(
  OUTPUT ${GENERATED}/FosterIL.capnp.c++
  COMMAND ${CAPNP} compile FosterIL.capnp
                 --output=${CAPNP_BIN_DIR}/capnpc-c++:${GENERATED}
                 --import-path=${CAPNP_DIR}/include
  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/compiler/parse
  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.capnp
  )
# }}} -----------------------------------------------------------

# {{{ Generate Haskell code to generate capnp files for the backend.
add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/compiler/me/src/FosterIL_capnp.hs
  COMMAND ${CAPNP} compile FosterIL.capnp
                 --output=${MINUPROTO}:${PROJECT_SOURCE_DIR}/compiler/me/src
                 --import-path=${CAPNP_DIR}/include
  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/compiler/parse
  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.capnp
  )

set(HS_ME_PROFILE_OR_OPTIMIZE profile CACHE STRING
        "Middle end: ask GHC to [profile] or to [optimize] it")
set(HS_ME hs_me_${HS_ME_PROFILE_OR_OPTIMIZE})

# Generate middle-end from Haskell source files, once
# Haskell capnp module sources have been generated.
add_custom_target(me DEPENDS ${HS_ME})
add_custom_target(${HS_ME}              USES_TERMINAL
  DEPENDS ${PROJECT_SOURCE_DIR}/compiler/me/src/FosterIL_capnp.hs
          ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Tokens.hs
  COMMAND ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/mk_me.py
          --srcroot ${PROJECT_SOURCE_DIR}
          --bindir ${PROJECT_BINARY_DIR}
          --${HS_ME_PROFILE_OR_OPTIMIZE}
  )

# We currently run tests in parallel on Linux and serially on Mac OS X.
# Haskell's profiling coverage tool corrupts its database when
# run in parallel, so consider yourself warned...

add_custom_target(cmake_clean
  COMMAND rm -rf ${PROJECT_BINARY_DIR}/CMakeCache.txt ${PROJECT_BINARY_DIR}/CMakeFiles ${PROJECT_BINARY_DIR}/cmake_install.cmake
  )

add_custom_target(hs_clean
  COMMAND rm -rf ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/*.o
  COMMAND rm -f  ${PROJECT_SOURCE_DIR}/compiler/me/src/Main.o
  COMMAND rm -f  ${PROJECT_SOURCE_DIR}/compiler/me/src/FosterIL_capnp.o
  )

# Attaching commands to add_custom_target basically means
# "run these commands whenver the target is mentioned."
# }}} -------------------------------------------------------------------

# {{{ Generate libfoster_main (object code and bitcode).
# Note that clang is explicitly used for the bitcode, and the default C++ compiler
# is used for the object code.
add_custom_command(
  OUTPUT ${LIBRARY_OUTPUT_PATH}/libfoster_main.o
   	 ${PROJECT_BINARY_DIR}/_bitcodelibs_/libfoster_main.bc
  COMMAND
        ${CMAKE_CXX_COMPILER} -g
          ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
          -I ${PROJECT_SOURCE_DIR}/runtime/gc/
          -I ${PROJECT_SOURCE_DIR}/third_party/chromium_base/
                -c -o ${LIBRARY_OUTPUT_PATH}/libfoster_main.o
  COMMAND
        ${CLANG} -g -emit-llvm
          ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
          -I ${PROJECT_SOURCE_DIR}/runtime/gc/
          -I ${PROJECT_SOURCE_DIR}/third_party/chromium_base/
                -c -o ${PROJECT_BINARY_DIR}/_bitcodelibs_/libfoster_main.bc
  DEPENDS
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
)
# }}}

# The .py file here is basically `touch` with a hardcoded path.
# The intention here was that we could store/overwrite compile-time
# config flags for the runtime/GC in a way that's more easily amenable
# to automated re-configuration than source editing or command line flags
# or such.
add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_reconfig-inl.h
  COMMAND
    ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/mk_gc_reconfig_h.py
      --srcdir=${PROJECT_SOURCE_DIR}
  DEPENDS
    ${PROJECT_SOURCE_DIR}/scripts/mk_gc_reconfig_h.py
)

# {{{ Use clang to build libfoster.bc
set (hdrhist_ROOT ${PROJECT_SOURCE_DIR}/third_party/HdrHistogram_c/)

#  ${hdrhist_ROOT}/src/hdr_encoding.c
#  ${hdrhist_ROOT}/src/hdr_histogram_log.c
#  ${hdrhist_ROOT}/src/hdr_interval_recorder.c
#  ${hdrhist_ROOT}/src/hdr_thread.c
#  ${hdrhist_ROOT}/src/hdr_time.c
#  ${hdrhist_ROOT}/src/hdr_writer_reader_phaser.c
set (hdrhist_SOURCES
  ${hdrhist_ROOT}/src/hdr_histogram.c
)

include_directories(${hdrhist_ROOT}/src)

add_custom_command(
  OUTPUT
   	 ${PROJECT_BINARY_DIR}/_bitcodelibs_/foster_hdrhist.bc
  COMMAND
     ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/build_hdrhist.py
        --clang="${CLANG_C}"
        --srcdir=${PROJECT_SOURCE_DIR}
        --bindir=${PROJECT_BINARY_DIR}
        --llvmdir="${LLVM_BINDIR}"
         ${hdrhist_SOURCES}
  DEPENDS
        ${hdrhist_SOURCES}
)

set(LIBFOSTER_CPP_SOURCES
        ${PROJECT_SOURCE_DIR}/runtime/libfoster.cpp
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_coro.cpp
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_posix.cpp
        ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc.cpp
        ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_stackmaps.cpp
        ${PROJECT_SOURCE_DIR}/runtime/foster_globals.cpp
        ${PROJECT_SOURCE_DIR}/third_party/jemalloc_pages/src/pages.cpp
)

add_custom_command(
  OUTPUT ${PROJECT_BINARY_DIR}/_bitcodelibs_/foster_runtime.bc
  COMMAND rm -f ${PROJECT_BINARY_DIR}/_bitcodelibs_/foster_runtime.bc
  COMMAND
    ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
        --clang="${CLANG}"
        --srcdir=${PROJECT_SOURCE_DIR}
        --bindir=${PROJECT_BINARY_DIR}
        --llvmdir="${LLVM_BINDIR}"
        --corodef=${CORO_METHOD}
        ${LIBFOSTER_CPP_SOURCES}
  DEPENDS
    ${LIBFOSTER_CPP_SOURCES}
    ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
    ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_utils.h
    ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_reconfig-inl.h
    ${PROJECT_BINARY_DIR}/_bitcodelibs_/foster_hdrhist.bc
)

# We could attach the command to build libfoster.bc directly
# to the libfoster_bc target, but the effect of doing that would
# be that libfoster.bc would always be considered out of date,
# and would be rebuilt on every single invocation of make.
add_custom_target(foster_runtime_bc DEPENDS
        ${PROJECT_BINARY_DIR}/_bitcodelibs_/foster_runtime.bc
        ${LIBRARY_OUTPUT_PATH}/libfoster_main.o)
# }}} -----------------------------------------------------------

# Look for ANTLR-generated lexer and parser, and ANTLR library files
include_directories(${ANTLR_DIR}/include ${PROJECT_BINARY_DIR})

include_directories(
  ${PROJECT_SOURCE_DIR}/compiler/include/foster
  ${PROJECT_SOURCE_DIR}/compiler/llvm
  ${PROJECT_SOURCE_DIR}/third_party
  ${PROJECT_SOURCE_DIR}/third_party/cityhash/src
  ${PROJECT_SOURCE_DIR}/third_party/fftw_cycle
  ${PROJECT_SOURCE_DIR}/third_party/cbor-cpp/src
)

# {{{ Miscellaneous flag munging
link_directories(${ANTLR_LIBDIR} ${LLVM_LIBDIR})

add_definitions(${LLVM_CFLAGS} "-ggdb")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14")

# Compressing debug sections can significantly reduce link time,
# but the functionality is specific to GNU gold.
if (CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
  execute_process(COMMAND ld --version
                  OUTPUT_VARIABLE LD_VERSION_STRING)
  if(LD_VERSION_STRING MATCHES "GNU gold")
    set(CMAKE_EXE_LINKER_FLAGS
    "${CMAKE_EXE_LINKER_FLAGS} -Wl,--compress-debug-sections,zlib")
  endif(LD_VERSION_STRING MATCHES "GNU gold")
endif(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
# }}}

#####################################################################
include(${PROJECT_SOURCE_DIR}/third_party/libcoro/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/fftw_cycle/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/HdrHistogram_c/CMakeLists.txt)

# {{{ Define inputs and dependencies between the various foster* libraries and executables.
add_library(fosterc_base STATIC
  compiler/base/Assert.cpp
  compiler/base/Diagnostics.cpp
  compiler/base/LLVMUtils.cpp
  compiler/base/InputFile.cpp
  compiler/base/InputTextBuffer.cpp
  compiler/base/SourceRange.cpp
  compiler/base/TimingsRepository.cpp
  compiler/base/FreshNameGenerator.cpp
  compiler/base/PughSinofskyPrettyPrinter.cpp
  third_party/pystring/pystring.cpp
  third_party/cityhash/src/city.cc
)

add_library(fosterc_parse STATIC
  compiler/parse/FosterTypeAST.cpp
  compiler/parse/ParsingContext.cpp
  compiler/parse/ANTLRtoFosterAST.cpp
  compiler/parse/ANTLRtoFosterErrorHandling.cpp
  third_party/cbor-cpp/src/output_dynamic.cpp
  third_party/cbor-cpp/src/encoder.cpp
  ${GENERATED}/fosterParser.c
  ${GENERATED}/fosterLexer.c
)
add_dependencies(fosterc_parse fosterc_base)

set(ANTLR_C_FLAGS "-Wno-parentheses-equality -Wno-unused-variable
 		   -Wno-trigraphs -Wno-unused-function -Wno-cast-qual
 		   -Wno-tautological-compare -std=gnu11")
string(REPLACE "\n" "" ANTLR_C_FLAGS ${ANTLR_C_FLAGS})
# gnu11 disables trigraphs...
set_source_files_properties(
      ${GENERATED}/fosterParser.c
      ${GENERATED}/fosterLexer.c
  COMPILE_FLAGS "${ANTLR_C_FLAGS}")

add_library(fosterc_llvm STATIC
  compiler/llvm/passes/GCRootSafetyChecker.cpp
  compiler/llvm/passes/EscapingAllocaFinder.cpp
  compiler/llvm/passes/FosterMallocSpecializer.cpp
  compiler/llvm/passes/CallingConventionChecker.cpp
  compiler/llvm/passes/TimerCheckerInsertion.cpp
  compiler/llvm/passes/BitcastLoadRecognizer.cpp
  compiler/llvm/passes/FosterPasses.cpp
  compiler/llvm/plugins/FosterGC.cpp
)
add_dependencies(fosterc_llvm fosterc_base)

add_library(fosterc_passes STATIC
  compiler/passes/PrettyPrintPass.cpp
)

add_dependencies(fosterc_passes fosterc_parse)

############

add_executable(fosterparse compiler/fosterparse.cpp)

target_link_libraries(fosterparse
  fosterc_parse fosterc_passes fosterc_base
  antlr3c ${LLVM_LDFLAGS})

############

add_executable(fosterlower
    compiler/fosterlower.cpp
    compiler/StandardPrelude.cpp
    compiler/passes/CapnpToLLExpr.cpp
    compiler/passes/LLCodegen.cpp
    compiler/passes/Codegen/CodegenUtils.cpp
    compiler/passes/Codegen/Codegen-coro.cpp
    compiler/passes/Codegen/Codegen-typemaps.cpp
    ${GENERATED}/FosterIL.capnp.c++
  )

target_link_libraries(fosterlower
  fosterc_parse fosterc_passes fosterc_base
  fosterc_llvm
  ${CAPNP_DIR}/lib/libcapnp${CMAKE_STATIC_LIBRARY_SUFFIX}
  ${CAPNP_DIR}/lib/libkj${CMAKE_STATIC_LIBRARY_SUFFIX}
  antlr3c ${LLVM_LDFLAGS})

target_include_directories(fosterlower
     PRIVATE  ${CAPNP_DIR}/include)

add_dependencies(fosterlower
    foster_runtime_bc cycle)

############

add_executable(fosteroptc compiler/fosteroptc.cpp)
target_link_libraries(fosteroptc
    fosterc_base fosterc_llvm ${LLVM_LDFLAGS})

add_dependencies(fosteroptc
    foster_runtime_bc ${HS_ME})
# We have a dependency here just to ensure that HS_ME
# gets built with a bare 'make' command.

############

add_dependencies(foster_runtime_bc coro)

set_target_properties(
  fosterc_passes fosterc_parse
  PROPERTIES
  COMPILE_FLAGS -Wall
)

############

# The --start/end-group is needed to resolve circular linking dependencies
# on Linux.
# If/once LLVM ships proper EXPORT info, we can avoid this problem in a
# portable manner.
if (CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
  set(START_GROUP "-Wl,--start-group")
  set(END_GROUP   "-Wl,--end-group")
else()
  set(START_GROUP "")
  set(END_GROUP   "")
endif(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")

set(CLANGLIBS
  ${START_GROUP}
  clangAST clangAnalysis clangBasic clangDriver clangEdit
  clangFrontend clangFrontendTool clangLex clangParse clangSema
  clangEdit clangASTMatchers clangRewrite clangRewriteFrontend
  clangSerialization clangToolingCore clangTooling
  ${END_GROUP})

add_executable(c2f tools/c2f/c2f.cpp tools/c2f/c2f_cfg.cpp)
target_link_libraries(c2f
  ${CLANGLIBS}
  ${LLVM_LDFLAGS})

#####################################################################
# These files contain code which inherits from LLVM classes,
# or uses llvm::cl, and thus must be compiled without RTTI.
set_target_properties(fosterc_llvm fosterc_base
                      fosterlower fosteroptc fosterparse
                      c2f
  PROPERTIES
  COMPILE_FLAGS ${LLVM_EXTRA_CFLAGS}
)

#####################################################################
# https://github.com/martine/ninja/issues/174
if (CMAKE_GENERATOR STREQUAL "Ninja")
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fcolor-diagnostics")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fcolor-diagnostics")
endif()
#####################################################################
set(REGRESS_CMD
      ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/run_all.py
                 ${PROJECT_SOURCE_DIR}/test/bootstrap
                 --bindir ${PROJECT_BINARY_DIR}
                 --cxxpath ${CLANG}
                 --no_extra_bitcode
                 --quietish
                 -I ${PROJECT_SOURCE_DIR}/stdlib)
add_custom_target(regress       USES_TERMINAL
        COMMAND echo ${REGRESS_CMD}
        COMMAND ${REGRESS_CMD})

add_custom_target(regresstc       USES_TERMINAL
  COMMAND
      ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/run_all.py
                 ${PROJECT_SOURCE_DIR}/test/bootstrap
                 --bindir ${PROJECT_BINARY_DIR}
                 --cxxpath ${CLANG}
                 --no_extra_bitcode
                 --quietish
                 --me-arg=--typecheck-only
                 -I ${PROJECT_SOURCE_DIR}/stdlib)

add_custom_target(stress        USES_TERMINAL
  COMMAND ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/run_all.py
	     ${PROJECT_SOURCE_DIR}/test/stress
	     --bindir ${PROJECT_BINARY_DIR}
             --cxxpath ${CLANG}
	     -I ${PROJECT_SOURCE_DIR}/stdlib
  )

add_custom_target(list_regression_tests
  COMMAND ${PYTHON} ${PROJECT_SOURCE_DIR}/scripts/list_all.py
	     ${PROJECT_SOURCE_DIR}/test/bootstrap
  )

add_custom_target(list_disabled_tests
  COMMAND ${PROJECT_SOURCE_DIR}/scripts/fack DISABLED_TEST --after-context=3
  )
