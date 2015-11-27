cmake_minimum_required (VERSION 2.8)

# We need to set up the compiler paths before calling project()...
# ~~~~~~~~~~~~~~~~~~~~

set(LLVM_VERSION 3.7.0)

find_program(LLVM_CONFIG NAMES llvm-config llvm-config-${LLVM_VERSION}
  PATHS
    $ENV{HOME}/llvm/${LLVM_VERSION}/bin
    $ENV{HOME}/sw/local/llvm-${LLVM_VERSION}/bin
    /usr/lib/llvm-${LLVM_VERSION}/bin
  DOC "llvm-config")

execute_process(COMMAND ${LLVM_CONFIG} --bindir OUTPUT_VARIABLE LLVM_BINDIR)

# If llvm-config isn't found, LLVM_BINDIR will be empty
# and CMake will report an error here.
string(REPLACE "\n" "" LLVM_BINDIR ${LLVM_BINDIR})

find_program(CLANG NAMES clang++-${LLVM_VERSION} clang++
  PATHS
    ${LLVM_BINDIR}
  DOC "C++ compiler to emit LLVM bytecode: clang++")

string(REPLACE "++" "" CLANG_C ${CLANG})

set(CMAKE_CXX_COMPILER ${CLANG})
set(CMAKE_C_COMPILER ${CLANG_C})

# ~~~~~~~~~~~~~~~~~~~~
# ... Okay, now we can proceed.
project (foster)

cmake_policy(VERSION 2.8.0)

####################### Configuration Rules ########################

set(LIBRARY_OUTPUT_PATH ${PROJECT_BINARY_DIR}/_nativelibs_)

# ~~~~~~~~~~~~~~~~~~~~ ANTLR ~~~~~~~~~~~~~~~~~~~~~

# This isn't cached since CMake doesn't seem to have any way of
# specifying that some cached variables depend on others, and it's
# sort of annoying to see the option to change it AFTER the paths
# that depend on it have been presented...
set(ANTLR_VERSION 3.2)
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

set(CORO_METHOD CORO_ASM
    CACHE
    DOC "libcoro implementation: CORO_{ASM,SJLJ,LOSER,PTHREAD}")

set(GENERATED ${PROJECT_BINARY_DIR}/_generated_)

# ~~~~~~~~~~~~~~~~~~~~ Protocol Buffers ~~~~~~~~~~~~~~~~~~~~~~
find_package(Protobuf REQUIRED)
include_directories(${PROTOBUF_INCLUDE_DIRS})

find_program(HPROTOC NAMES hprotoc
  PATHS
    $ENV{HOME}/.cabal/bin
  DOC "hprotoc: Protobuf compiler for Haskell")

# ~~~~~~~~~~~~~~~~~~~~~~~~~ LLVM ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

# Collect the linker flags for us to link against LLVM
set(LLVM_COMPONENTS_NEEDED all)

execute_process(COMMAND
    ${LLVM_CONFIG} --libs ${LLVM_COMPONENTS_NEEDED} --ldflags  --system-libs
  OUTPUT_VARIABLE LLVM_LDFLAGS
)

# Make sure that the linker flags are one physical line
string(REPLACE "\n" " " LLVM_LDFLAGS "${LLVM_LDFLAGS}")
string(STRIP "${LLVM_LDFLAGS}" LLVM_LDFLAGS)

find_package(Threads REQUIRED)

# Rather than running all programs JITted from the main fosterc
# compiler binary (and embedding the foster runtime inside the foster compiler)
# we instead compile the foster runtime with clang++ to bitcode, then link the
# foster runtime bitcode in along with the bitcode for a program to run it.

# TODO: provide ${CMAKE_THREAD_LIBS_INIT} to compile scripts

####################### Compilation Rules ##########################

# Just run these every time we build... CMake seems to have trouble
# with the concept of having a target depend on a directory.
execute_process(COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_generated_)
execute_process(COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_bitcodelibs_)
execute_process(COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_nativelibs_)

# Use python to build fosterParser.c when grammar/foster.g changes
add_custom_command(
  OUTPUT ${GENERATED}/fosterParser.c
         ${GENERATED}/fosterLexer.c

  # Make sure later stages fail if this stage fails.
  COMMAND rm -f ${GENERATED}/fosterLexer.h

  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
                    ${ANTLR_JAR}
                    ${GENERATED}
                    ${PROJECT_SOURCE_DIR}/grammar/foster.g
  DEPENDS
        ${PROJECT_SOURCE_DIR}/grammar/foster.g
        ${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
)

# Generate C++ code to manipulate protobuf files.
add_custom_command(
  OUTPUT
          ${GENERATED}/FosterIL.pb.h
          ${GENERATED}/FosterIL.pb.cc
  COMMAND ${PROTOBUF_PROTOC_EXECUTABLE}
          -I ${PROJECT_SOURCE_DIR}/compiler/parse/
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.proto
          --cpp_out=${GENERATED}
  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.proto
  )

#-------------------------------------------------------------------

# Generate Haskell code to manipulate protobuf files.
add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Bepb.hs
  COMMAND cp ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.proto
             ${PROJECT_SOURCE_DIR}/compiler/me/FosterIL.protox
  COMMAND ${HPROTOC}
          --haskell_out=${PROJECT_SOURCE_DIR}/compiler/me/src
          ${PROJECT_SOURCE_DIR}/compiler/me/FosterIL.protox
  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/compiler/me
  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.proto
  )

# Generate middle-end from Haskell source files, once
# Haskell protobuf module sources have been generated.
add_custom_target(hs_me
  DEPENDS ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Bepb.hs
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/mk_me.py
          --srcroot ${PROJECT_SOURCE_DIR}
          --bindir ${PROJECT_BINARY_DIR}
          --profile
  )
# We currently run tests in parallel on Linux and serially on Mac OS X.
# Haskell's profiling coverage tool corrupts its database when
# run in parallel, so consider yourself warned...

add_custom_target(hs_clean
  COMMAND rm -rf ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/*.o
  COMMAND rm -f  ${PROJECT_SOURCE_DIR}/compiler/me/src/Main.o
  )

#-------------------------------------------------------------------

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
        ${LIBRARY_OUTPUT_PATH}
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
)

# The .py file here is basically `touch` with a hardcoded path.
# The intention here was that we could store/overwrite compile-time
# config flags for the runtime/GC in a way that's more easily amenable
# to automated re-configuration than source editing or command line flags
# or such.
add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_reconfig-inl.h
  COMMAND
    python ${PROJECT_SOURCE_DIR}/scripts/mk_gc_reconfig_h.py
      --srcdir=${PROJECT_SOURCE_DIR}
  DEPENDS
    ${PROJECT_SOURCE_DIR}/scripts/mk_gc_reconfig_h.py
)

set(LIBFOSTER_CPP_SOURCES
        ${PROJECT_SOURCE_DIR}/runtime/libfoster.cpp
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_coro.cpp
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_posix.cpp
        ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc.cpp
        ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_stackmaps.cpp
        ${PROJECT_SOURCE_DIR}/runtime/foster_globals.cpp
)

# Use clang to build libfoster.bc
add_custom_command(
  OUTPUT ${PROJECT_BINARY_DIR}/_bitcodelibs_/foster_runtime.bc
  COMMAND
    python ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
        --clang="${CLANG}"
        --srcdir=${PROJECT_SOURCE_DIR}
        --bindir=${PROJECT_BINARY_DIR}
        --llvmdir="${LLVM_BINDIR}"
        --corodef=${CORO_METHOD}
        ${LIBFOSTER_CPP_SOURCES}
  DEPENDS
    ${LIBFOSTER_CPP_SOURCES}
    ${PROJECT_BINARY_DIR}/_bitcodelibs_
    ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
    ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_utils.h
    ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_reconfig-inl.h
)
# We could attach the command to build libfoster.bc directly
# to the libfoster_bc target, but the effect of doing that would
# be that libfoster.bc would always be considered out of date,
# and would be rebuilt on every single invocation of make.
add_custom_target(foster_runtime_bc DEPENDS
        ${PROJECT_BINARY_DIR}/_bitcodelibs_/foster_runtime.bc
        ${LIBRARY_OUTPUT_PATH}/libfoster_main.o)

#-----------------------------------------------------------

# Attaching commands to add_custom_target basically means
# "run these commands whenver the target is mentioned."


# Look for ANTLR-generated lexer and parser, and ANTLR library files
include_directories(${ANTLR_DIR}/include ${PROJECT_BINARY_DIR})

include_directories(
  ${PROJECT_SOURCE_DIR}/compiler/include/foster
  ${PROJECT_SOURCE_DIR}/compiler/llvm
  ${PROJECT_SOURCE_DIR}/third_party
  ${PROJECT_SOURCE_DIR}/third_party/chromium_base
  ${PROJECT_SOURCE_DIR}/third_party/cityhash/src
  ${PROJECT_SOURCE_DIR}/third_party/fftw_cycle
  ${PROJECT_SOURCE_DIR}/third_party/cbor-cpp/src
)

# Takes ldflags, which looks like
# "... -L/path/to/llvm/lib ..." and puts
# "-L/path/to/llvm/lib" in LLVM_LD_PATH.
string(REGEX MATCH "-L[ ]?[^ ]+" LLVM_LD_PATH "${LLVM_LDFLAGS}")

# Strip off leading -L to give the path alone.
string(REGEX REPLACE "^-L[ ]?" "" LLVM_LD_PATH "${LLVM_LD_PATH}")

link_directories(${LLVM_LD_PATH} ${ANTLR_LIBDIR})

add_definitions(${LLVM_CFLAGS} "-ggdb")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

if (CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
  # Only works with the GNU Gold linker
  set(CMAKE_EXE_LINKER_FLAGS
   "${CMAKE_EXE_LINKER_FLAGS} -Wl,--compress-debug-sections,zlib")
endif(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")

#####################################################################
include(${PROJECT_SOURCE_DIR}/third_party/chromium_base/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/libcoro/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/fftw_cycle/CMakeLists.txt)

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
  ${GENERATED}/FosterAST.pb.h
  ${GENERATED}/FosterIL.pb.h
)

add_library(fosterc_parse STATIC
  compiler/parse/FosterTypeAST.cpp
  compiler/parse/ParsingContext.cpp
  compiler/parse/ANTLRtoFosterAST.cpp
  compiler/parse/ANTLRtoFosterErrorHandling.cpp
  third_party/cbor-cpp/src/output_dynamic.cpp
  third_party/cbor-cpp/src/encoder.cpp
  ${GENERATED}/FosterAST.pb.cc
  ${GENERATED}/fosterParser.c
  ${GENERATED}/fosterLexer.c
)
add_dependencies(fosterc_parse fosterc_base)

set(ANTLR_C_FLAGS "-Wno-parentheses-equality -Wno-unused-variable
 		   -Wno-trigraphs -Wno-unused-function
 		   -Wno-tautological-compare -std=gnu11")
string(REPLACE "\n" "" ANTLR_C_FLAGS ${ANTLR_C_FLAGS})
# gnu11 disables trigraphs...
set_source_files_properties(
      ${GENERATED}/fosterParser.c
      ${GENERATED}/fosterLexer.c
  COMPILE_FLAGS "${ANTLR_C_FLAGS}")

add_library(fosterc_llvm STATIC
  compiler/llvm/passes/GCMallocFinder.cpp
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

add_library(fosterc_fosteril_pb STATIC
  ${GENERATED}/FosterIL.pb.cc
)

add_dependencies(fosterc_passes fosterc_parse)

############

add_executable(fosterparse compiler/fosterparse.cpp)

target_link_libraries(fosterparse
  fosterc_parse fosterc_passes fosterc_base
  antlr3c ${PROTOBUF_LIBRARY} ${LLVM_LDFLAGS})

############

add_executable(fosterlower
    compiler/fosterlower.cpp
    compiler/StandardPrelude.cpp
    compiler/passes/ProtobufToLLExpr.cpp
    compiler/passes/LLCodegen.cpp
    compiler/passes/Codegen/CodegenUtils.cpp
    compiler/passes/Codegen/Codegen-coro.cpp
    compiler/passes/Codegen/Codegen-typemaps.cpp
  )
target_link_libraries(fosterlower
  fosterc_parse fosterc_passes fosterc_parse fosterc_base
  fosterc_llvm fosterc_fosteril_pb
  antlr3c ${PROTOBUF_LIBRARY} ${LLVM_LDFLAGS})

add_dependencies(fosterlower
    foster_runtime_bc hs_me cycle)

############

add_executable(fosteroptc compiler/fosteroptc.cpp)
target_link_libraries(fosteroptc
    fosterc_base fosterc_llvm ${LLVM_LDFLAGS})

add_dependencies(fosteroptc
    foster_runtime_bc hs_me)

############

add_dependencies(foster_runtime_bc chromium_base)
add_dependencies(foster_runtime_bc coro)


set_target_properties(
  fosterc_passes fosterc_parse
  PROPERTIES
  COMPILE_FLAGS -Wall
)

# These files contain code which inherits from LLVM classes,
# or uses llvm::cl, and thus must be compiled without RTTI.
set_target_properties(fosterc_llvm fosterc_base
                      fosterlower fosteroptc fosterparse
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
      python ${PROJECT_SOURCE_DIR}/scripts/run_all.py
                 ${PROJECT_SOURCE_DIR}/test/bootstrap
                 --bindir ${PROJECT_BINARY_DIR}
                 --cxxpath ${CLANG}
                 --no_extra_bitcode
                 -I ${PROJECT_SOURCE_DIR}/stdlib)
add_custom_target(regress
        COMMAND echo ${REGRESS_CMD}
        COMMAND ${REGRESS_CMD})

add_custom_target(stress
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/run_all.py
	     ${PROJECT_SOURCE_DIR}/test/stress
	     --bindir ${PROJECT_BINARY_DIR}
             --cxxpath ${CLANG}
	     -I ${PROJECT_SOURCE_DIR}/stdlib
  )

add_custom_target(speed
  COMMAND ${PROJECT_SOURCE_DIR}/scripts/gotest.sh speed/siphash -I ${PROJECT_SOURCE_DIR}/stdlib
  )

add_custom_target(list_regression_tests
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/list_all.py
	     ${PROJECT_SOURCE_DIR}/test/bootstrap
  )

add_custom_target(list_disabled_tests
  COMMAND ${PROJECT_SOURCE_DIR}/scripts/fack DISABLED_TEST --after-context=3
  )
