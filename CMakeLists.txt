cmake_minimum_required (VERSION 2.8)
project (foster)

cmake_policy(VERSION 2.8.0)

####################### Configuration Rules ########################

SET(LIBRARY_OUTPUT_PATH ${PROJECT_BINARY_DIR}/_nativelibs_)

set(LLVM_VERSION 2.8)

option(USE_FOSTER_GC_PLUGIN
       "Use compiled stackmaps for garbage collection"
       true)

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

find_program(LLVM_CONFIG NAMES llvm-config
  PATHS
    $ENV{HOME}/llvm/${LLVM_VERSION}/bin
    $ENV{HOME}/sw/local/llvm-${LLVM_VERSION}/bin
  DOC "llvm-config")

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

# Make sure we don't have any extraneous newlines in generated Makefiles
#
string(STRIP "${LLVM_ORIGINAL_CFLAGS}" LLVM_ORIGINAL_CFLAGS)


# Hack for now: rather than running all programs JITted from the main fosterc
# compiler binary (and embedding the foster runtime inside the foster compiler)
# we instead compile the foster runtime with llvm-g++ to bitcode, then link the
# foster runtime bitcode in along with the bitcode for a program to run it.
#
find_program(LLVM_G++ NAMES llvm-g++ clang++ clang
  PATHS
        /usr/bin
        $ENV{HOME}/llvm/${LLVM_VERSION}/gcc/bin
        $ENV{HOME}/llvm/${LLVM_VERSION}/bin
        /usr/lib/llvm/llvm/gcc-4.2/bin
  DOC "C++ compiler to emit LLVM bytecode: llvm-g++ or clang++")


execute_process(COMMAND ${LLVM_CONFIG} --bindir OUTPUT_VARIABLE LLVM_BINDIR)

# If llvm-config isn't found, LLVM_BINDIR will be empty
# and CMake will report an error here.
string(REPLACE "\n" "" LLVM_BINDIR ${LLVM_BINDIR})

# Collect the linker flags for us to link against LLVM
set(LLVM_COMPONENTS_NEEDED core jit interpreter native linker executionengine
  analysis ipo scalaropts bitwriter bitreader asmparser asmprinter instrumentation
)
execute_process(COMMAND
    ${LLVM_CONFIG} --ldflags --libs ${LLVM_COMPONENTS_NEEDED}
  OUTPUT_VARIABLE LLVM_LDFLAGS
)

# Make sure that the linker flags are one physical line
string(REPLACE "\n" "" LLVM_LDFLAGS "${LLVM_LDFLAGS}")
string(STRIP "${LLVM_LDFLAGS}" LLVM_LDFLAGS)

find_package(Threads REQUIRED)

# TODO: provide ${CMAKE_THREAD_LIBS_INIT} to compile scripts

####################### Compilation Rules ##########################

# Creating the _generated_ directory is easy enough!
add_custom_command(
  OUTPUT           ${PROJECT_BINARY_DIR}/_generated_
                   ${PROJECT_BINARY_DIR}/_nativelibs_
                   ${PROJECT_BINARY_DIR}/_bitcodelibs_
  COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_generated_
  COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_nativelibs_
  COMMAND mkdir -p ${PROJECT_BINARY_DIR}/_bitcodelibs_
)

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

# Generate C++ and Python code to manipulate AST protobuf files.
add_custom_command(
  OUTPUT
          ${GENERATED}/FosterAST.pb.h
          ${GENERATED}/FosterAST.pb.cc
          ${GENERATED}/FosterAST_pb2.py
          ${GENERATED}/FosterIL.pb.h
          ${GENERATED}/FosterIL.pb.cc
  COMMAND ${PROTOBUF_PROTOC_EXECUTABLE}
          -I ${PROJECT_SOURCE_DIR}/compiler/parse/
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterAST.proto
          --cpp_out=${GENERATED}
          --python_out=${GENERATED}
  COMMAND ${PROTOBUF_PROTOC_EXECUTABLE}
          -I ${PROJECT_SOURCE_DIR}/compiler/parse/
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.proto
          --cpp_out=${GENERATED}
          --python_out=${GENERATED}
  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterAST.proto
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterIL.proto
  )


add_custom_command(
  OUTPUT
          ${GENERATED}/LLVM.pb.h
          ${GENERATED}/LLVM.pb.cc
          ${GENERATED}/LLVM_pb2.py
  COMMAND ${PROTOBUF_PROTOC_EXECUTABLE}
          -I ${PROJECT_SOURCE_DIR}/compiler/llvm/
          ${PROJECT_SOURCE_DIR}/compiler/llvm/LLVM.proto
          --cpp_out=${GENERATED}
          --python_out=${GENERATED}

  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/llvm/LLVM.proto
  )

#-------------------------------------------------------------------

# Generate Haskell code to manipulate AST protobuf files.
add_custom_command(
  OUTPUT ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Fepb.hs
  COMMAND cp ${PROJECT_SOURCE_DIR}/compiler/parse/FosterAST.proto
             ${PROJECT_SOURCE_DIR}/compiler/me/FosterAST.protox
  COMMAND ${HPROTOC}
          --haskell_out=${PROJECT_SOURCE_DIR}/compiler/me/src
          ${PROJECT_SOURCE_DIR}/compiler/me/FosterAST.protox
  WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/compiler/me
  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterAST.proto
  )

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
  DEPENDS ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Fepb.hs
          ${PROJECT_SOURCE_DIR}/compiler/me/src/Foster/Bepb.hs
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/mk_me.py
          --srcroot ${PROJECT_SOURCE_DIR}
          --bindir ${PROJECT_BINARY_DIR}
  )

#-------------------------------------------------------------------

add_custom_command(
  OUTPUT ${LIBRARY_OUTPUT_PATH}/libfoster_main.o
  COMMAND
        ${CMAKE_CXX_COMPILER} -g
          ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
          -I ${PROJECT_SOURCE_DIR}/runtime/gc/
                -c -o ${LIBRARY_OUTPUT_PATH}/libfoster_main.o
  DEPENDS
        ${LIBRARY_OUTPUT_PATH}
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
)

set(LIBFOSTER_CPP_SOURCES
        ${PROJECT_SOURCE_DIR}/runtime/libfoster.cpp
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_coro.cpp
        ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc.cpp
        ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc_stackmaps.cpp
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_gc_roots.cpp
)

# Use clang or llvm-g++ to build libfoster.bc
add_custom_command(
  OUTPUT ${PROJECT_BINARY_DIR}/_bitcodelibs_/libfoster.bc
  COMMAND
    python ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
        --clang="${LLVM_G++}"
        --srcdir=${PROJECT_SOURCE_DIR}
        --bindir=${PROJECT_BINARY_DIR}
        --llvmdir="${LLVM_BINDIR}"
        --corodef=${CORO_METHOD}
        ${LIBFOSTER_CPP_SOURCES}
  DEPENDS
    ${LIBFOSTER_CPP_SOURCES}
    ${PROJECT_BINARY_DIR}/_bitcodelibs_
    ${PROJECT_BINARY_DIR}/_generated_/imath.h
    ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
)
# We could attach the command to build libfoster.bc directly
# to the libfoster_bc target, but the effect of doing that would
# be that libfoster.bc would always be considered out of date,
# and would be rebuilt on every single invocation of make.
add_custom_target(libfoster_bc DEPENDS
        ${PROJECT_BINARY_DIR}/_bitcodelibs_/libfoster.bc
        ${LIBRARY_OUTPUT_PATH}/libfoster_main.o)


#-----------------------------------------------------------

add_custom_command(
  OUTPUT
        ${PROJECT_BINARY_DIR}/_bitcodelibs_/imath-wrapper.bc
  COMMAND
        ${LLVM_G++} -x c
          ${PROJECT_SOURCE_DIR}/third_party/imath/imath-wrapper.c
          -I ${PROJECT_BINARY_DIR}
          -c -emit-llvm
          -o ${PROJECT_BINARY_DIR}/_bitcodelibs_/imath-wrapper.bc
  DEPENDS
          ${PROJECT_BINARY_DIR}/_generated_/imath.h
          ${PROJECT_BINARY_DIR}/_bitcodelibs_
          ${PROJECT_SOURCE_DIR}/third_party/imath/imath-wrapper.c
)

add_custom_target(imath_wrapper_bc DEPENDS
        ${PROJECT_BINARY_DIR}/_bitcodelibs_/imath-wrapper.bc
        imath)

#-----------------------------------------------------------

# Attaching commands to add_custom_target basically means
# "run these commands whenver the target is mentioned."
add_custom_target(unittests COMMAND ctest -V -R unittest
  DEPENDS
    unittest_fosterc_base
    unittest_fosterc_parse)

# Look for ANTLR-generated lexer and parser, and ANTLR library files
include_directories(${ANTLR_DIR}/include ${PROJECT_BINARY_DIR})

include_directories(
  ${PROJECT_SOURCE_DIR}/compiler/include/foster
  ${PROJECT_SOURCE_DIR}/compiler/llvm
  ${PROJECT_SOURCE_DIR}/third_party
  ${PROJECT_SOURCE_DIR}/third_party/chromium_base
)

# Takes ldflags, which looks like
# "... -L/path/to/llvm/lib ..." and puts
# "-L/path/to/llvm/lib" in LLVM_LD_PATH.
string(REGEX MATCH "-L[ ]?[^ ]+" LLVM_LD_PATH "${LLVM_LDFLAGS}")

# Strip off leading -L to give the path alone.
string(REGEX REPLACE "^-L[ ]?" "" LLVM_LD_PATH "${LLVM_LD_PATH}")

link_directories(${LLVM_LD_PATH} ${ANTLR_LIBDIR})

add_definitions(${LLVM_CFLAGS} "-ggdb")

if (CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
  # Only works with the GNU Gold linker
  set(CMAKE_EXE_LINKER_FLAGS
   "${CMAKE_EXE_LINKER_FLAGS} -Wl,--compress-debug-sections,zlib")
endif(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")

#####################################################################
include(${PROJECT_SOURCE_DIR}/third_party/chromium_base/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/cpuid/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/gtest/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/imath/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/libcoro/CMakeLists.txt)

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
)
add_dependencies(fosterc_base
  ${GENERATED}/FosterAST.pb.h
  ${GENERATED}/FosterIL.pb.h
)

add_library(fosterc_parse STATIC
  compiler/parse/FosterAST.cpp
  compiler/parse/FosterTypeAST.cpp
  compiler/parse/ParsingContext.cpp
  compiler/parse/ANTLRtoFosterAST.cpp
  compiler/parse/ANTLRtoFosterErrorHandling.cpp
  compiler/parse/OperatorPrecedence.cpp
  compiler/parse/DumpStructure.cpp
  compiler/parse/FosterUtils.cpp
  ${GENERATED}/FosterAST.pb.cc
  ${GENERATED}/fosterParser.c
  ${GENERATED}/fosterLexer.c
)
add_dependencies(fosterc_parse fosterc_base)

# Avoid GCC complaints that -Woverloaded-virtual
# only applies to C++ code, not regular C code.
set_source_files_properties(
      ${GENERATED}/fosterParser.c
      ${GENERATED}/fosterLexer.c
      PROPERTIES LANGUAGE CXX)

add_library(fosterc_llvm STATIC
  compiler/llvm/passes/ImathImprover.cpp
  compiler/llvm/passes/GCMallocFinder.cpp
  compiler/llvm/passes/GCRootSafetyChecker.cpp
  compiler/llvm/passes/EscapingAllocaFinder.cpp
  compiler/llvm/passes/FosterPasses.cpp
  compiler/llvm/plugins/FosterGC.cpp
)
add_dependencies(fosterc_llvm fosterc_base)


add_library(fosterc_passes STATIC
  compiler/passes/Codegen/CodegenUtils.cpp
  compiler/passes/Codegen/Codegen-coro.cpp
  compiler/passes/Codegen/Codegen-typemaps.cpp
  compiler/passes/DumpToProtobuf.cpp
  compiler/passes/PrettyPrintPass.cpp
)

add_dependencies(fosterc_passes fosterc_parse)
set_target_properties(fosterc_llvm
  PROPERTIES
  COMPILE_FLAGS -Wall
)


# We've already set most of llvm-config's flags above via LLVM_CFLAGS;
# here, we just want to set the flags we removed from LLVM_CFLAGS.
#
set (LLVM_EXTRA_CFLAGS "")

   if (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NO_RTTI_FLAG})
  set (LLVM_EXTRA_CFLAGS "${LLVM_EXTRA_CFLAGS} ${NO_RTTI_FLAG}")
endif (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NO_RTTI_FLAG})

   if (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NDEBUG_FLAG})
  set (LLVM_EXTRA_CFLAGS "${LLVM_EXTRA_CFLAGS} ${NDEBUG_FLAG}")
endif (${LLVM_ORIGINAL_CFLAGS} MATCHES         ${NDEBUG_FLAG})

set_target_properties(fosterc_llvm
  PROPERTIES
  COMPILE_FLAGS ${LLVM_EXTRA_CFLAGS}
)
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
    ${GENERATED}/FosterIL.pb.cc
  )
target_link_libraries(fosterlower
  fosterc_parse fosterc_passes fosterc_parse fosterc_base
  fosterc_llvm
  antlr3c ${PROTOBUF_LIBRARY} ${LLVM_LDFLAGS})

add_dependencies(fosterlower
    libfoster_bc coro_wrapper_bc imath_wrapper_bc hs_me)

############

add_executable(fosteroptc compiler/fosteroptc.cpp)
target_link_libraries(fosteroptc
    fosterc_base fosterc_llvm ${LLVM_LDFLAGS})

add_dependencies(fosteroptc
    libfoster_bc coro_wrapper_bc imath_wrapper_bc hs_me)

############

#add_executable(proto2llvm
#    compiler/llvm/ProtoToLLVM.cpp
#    ${GENERATED}/LLVM.pb.cc)
#
#target_link_libraries(proto2llvm
#    ${PROTOBUF_LIBRARY} ${LLVM_LDFLAGS})
#
#add_dependencies(proto2llvm
#    libfoster_bc coro_wrapper_bc imath_wrapper_bc)

############

add_dependencies(libfoster_bc chromium_base)
add_dependencies(libfoster_bc cpuid)
add_dependencies(libfoster_bc coro)


set_target_properties(
  fosterc_passes fosterc_parse fosterc_base
  fosterparse fosterlower fosteroptc
  PROPERTIES
  COMPILE_FLAGS -Wall
)

#####################################################################

add_executable(unittest_fosterc_base
  ${PROJECT_SOURCE_DIR}/compiler/base/Assert_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/SourceRange_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/GenericGraph_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/FreshNameGenerator_unittest.cpp
)
target_link_libraries(unittest_fosterc_base
  fosterc_parse fosterc_base
  gtest_main
  antlr3c ${LLVM_LDFLAGS})

#######

add_executable(unittest_fosterc_parse
  ${PROJECT_SOURCE_DIR}/compiler/parse/ANTLRtoFosterAST_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/PughSinofskyPrettyPrinter_unittest.cpp
  ${GENERATED}/FosterAST.pb.cc
)
target_link_libraries(unittest_fosterc_parse
  fosterc_passes fosterc_parse fosterc_base
  gtest_main
  antlr3c ${PROTOBUF_LIBRARY} ${LLVM_LDFLAGS})

#####################################################################

enable_testing()

add_test(bootstrap
  python ${PROJECT_SOURCE_DIR}/scripts/run_all.py
         ${PROJECT_SOURCE_DIR}/test/bootstrap
         --bindir ${PROJECT_BINARY_DIR}
  )

# Look for non-silent diff -u output
set(CTEST_CUSTOM_ERROR_MATCH ${CTEST_CUSTOM_ERROR_MATCH}
  "[1-9][0-9] tests failed")

add_test(NAME fosterc_unittest_base
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/gtest_wrapper.py
                 ${PROJECT_BINARY_DIR}/unittest_fosterc_base)

add_test(NAME fosterc_unittest_parse
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/gtest_wrapper.py
                 ${PROJECT_BINARY_DIR}/unittest_fosterc_parse)
