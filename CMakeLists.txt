cmake_minimum_required (VERSION 2.6)
project (foster)

####################### Configuration Rules ########################

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

set(LLVM_VERSION 2.7)

option(USE_FOSTER_GC_PLUGIN
       "Use compiled stackmaps for garbage collection"
       true)

if (${ANTLR_DIR} STREQUAL "ANTLR_DIR-NOTFOUND")
    message("ANTLR not found! Please configure with ccmake or a CMake GUI")
    return()
endif (${ANTLR_DIR} STREQUAL "ANTLR_DIR-NOTFOUND")

set(GENERATED ${PROJECT_BINARY_DIR}/_generated_)

configure_file(${PROJECT_SOURCE_DIR}/FosterConfig.in.h
               ${GENERATED}/FosterConfig.h)

find_package(Protobuf REQUIRED)
include_directories(${PROTOBUF_INCLUDE_DIRS})

find_program(LLVM_CONFIG NAMES llvm-config
  PATHS $ENV{HOME}/llvm/${LLVM_VERSION}/bin
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
string(REPLACE "-g"                   "" LLVM_CFLAGS "${LLVM_ORIGINAL_CFLAGS}")

# This flag is C++ only, and the generated ANTLR files are in plain C.
#
string(REPLACE "-Woverloaded-virtual" "" LLVM_CFLAGS "${LLVM_CFLAGS}")

# LLVM libraries may also be compiled with -fno-rtti.
# We are free to compile almost all of our code with RTTI,
# except for LLVM plugins, which inherit from LLVM classes and
# therefore must agree on whether to expect and use typeinfo or not.
#
string(REPLACE "-fno-rtti" "" LLVM_CFLAGS "${LLVM_CFLAGS}")

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

# Use python to build fosterParser.c when grammar/foster.g changes
add_custom_command(
  OUTPUT ${GENERATED}/fosterParser.c
         ${GENERATED}/fosterLexer.c
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
                    ${ANTLR_JAR}
                    ${GENERATED}
                    ${PROJECT_SOURCE_DIR}/grammar/foster.g
  DEPENDS
        grammar/foster.g
        ${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
)

# Generate C++, Java, and Python code to manipulate AST protobuf files.
add_custom_command(
  OUTPUT
          ${GENERATED}/FosterAST.pb.h
          ${GENERATED}/FosterAST.pb.cc
          ${GENERATED}/FosterAST_pb2.py
  COMMAND ${PROTOBUF_PROTOC_EXECUTABLE}
          -I ${PROJECT_SOURCE_DIR}/compiler/parse/
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterAST.proto
          --cpp_out=${GENERATED}
          --java_out=${GENERATED}
          --python_out=${GENERATED}
  DEPENDS
          ${PROJECT_SOURCE_DIR}/compiler/parse/FosterAST.proto
  )

add_custom_command(
  OUTPUT ${PROJECT_BINARY_DIR}/libfoster_main.o
  COMMAND
        ${CMAKE_CXX_COMPILER}
          ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
          -I ${PROJECT_SOURCE_DIR}/runtime/gc/
                -c -o ${PROJECT_BINARY_DIR}/libfoster_main.o
  DEPENDS
        ${PROJECT_SOURCE_DIR}/runtime/libfoster_main.cpp
)

set(LIBFOSTER_CPP_SOURCES
        ${PROJECT_SOURCE_DIR}/runtime/libfoster.cpp
        ${PROJECT_SOURCE_DIR}/runtime/gc/foster_gc.cpp
)

# Use llvm-g++ to build libfoster.bc
add_custom_command(
  OUTPUT ${PROJECT_BINARY_DIR}/libfoster.bc
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
        "${LLVM_G++}"
        ${PROJECT_SOURCE_DIR}
        ${PROJECT_BINARY_DIR}
        "${CMAKE_STATIC_LIBRARY_SUFFIX}"
        "${LLVM_BINDIR}"
        ${LIBFOSTER_CPP_SOURCES}
  DEPENDS ${LIBFOSTER_CPP_SOURCES} ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
)
add_custom_target(libfoster_bc DEPENDS
        ${PROJECT_BINARY_DIR}/libfoster.bc
        ${PROJECT_BINARY_DIR}/libfoster_main.o)


# Look for ANTLR-generated lexer and parser, and ANTLR library files
include_directories(${ANTLR_DIR}/include ${PROJECT_BINARY_DIR})

include_directories(
  ${PROJECT_SOURCE_DIR}/compiler/include/foster
  ${PROJECT_SOURCE_DIR}/third_party
  ${PROJECT_SOURCE_DIR}/third_party/chromium_base
)

# Assumes path to LLVM lib dir has no spaces in it!
string(REGEX MATCH "-L[^ ]+" LLVM_LD_PATH "${LLVM_LDFLAGS}")

link_directories(${LLVM_LD_PATH} ${ANTLR_LIBDIR})

add_definitions(${LLVM_CFLAGS} "-ggdb")

if (CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
  # Only works with the GNU Gold linker
  set(CMAKE_EXE_LINKER_FLAGS
   "${CMAKE_EXE_LINKER_FLAGS} -Wl,--compress-debug-sections,zlib")
endif(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")

add_custom_target(fosterc_config_h DEPENDS ${GENERATED}/FosterConfig.h)

#####################################################################
include(${PROJECT_SOURCE_DIR}/third_party/chromium_base/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/cpuid/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/gtest/CMakeLists.txt)

add_library(fosterc_base STATIC
  compiler/base/Assert.cpp
  compiler/base/Diagnostics.cpp
  compiler/base/InputFile.cpp
  compiler/base/PathManager.cpp
  compiler/base/SourceRange.cpp
)
add_dependencies(fosterc_base fosterc_config_h)

add_library(fosterc_parse STATIC
  compiler/parse/FosterAST.cpp
  compiler/parse/FosterTypeAST.cpp
  compiler/parse/FosterSymbolTable.cpp
  compiler/parse/ANTLRtoFosterAST.cpp
  compiler/parse/ANTLRtoFosterErrorHandling.cpp
  compiler/parse/CompilationContext.cpp
  compiler/parse/FosterUtils.cpp
  ${GENERATED}/fosterParser.c
  ${GENERATED}/fosterLexer.c
)
add_dependencies(fosterc_parse fosterc_base)

add_library(fosterc_llvm STATIC
  compiler/llvm/passes/Hello.cpp
  compiler/llvm/plugins/FosterGC.cpp
)

# We've already set most of llvm-config's flags above via LLVM_CFLAGS;
# here, we just want to set the flags we removed from LLVM_CFLAGS.
#
set (NO_RTTI_FLAG "-fno-rtti")
if (${LLVM_ORIGINAL_CFLAGS} MATCHES ${NO_RTTI_FLAG})
set_target_properties(fosterc_llvm
  PROPERTIES
  COMPILE_FLAGS ${NO_RTTI_FLAG}
)
endif (${LLVM_ORIGINAL_CFLAGS} MATCHES ${NO_RTTI_FLAG})

add_executable(fosterc
  compiler/foster.cpp
  compiler/cfg/CFG.cpp
  compiler/passes/BuildCFG.cpp
  compiler/passes/CodegenPass.cpp
  compiler/passes/TypecheckPass.cpp
  compiler/passes/DumpToProtobuf.cpp
  compiler/passes/PrettyPrintPass.cpp
  compiler/passes/AddParentLinksPass.cpp
  compiler/passes/ReplaceExprTransform.cpp
  compiler/passes/ClosureConversionPass.cpp
  #  compiler/llvm/passes/LLVMCallGraphDotPrinter.cpp
  third_party/pystring/pystring.cpp
  ${GENERATED}/FosterAST.pb.cc
)

target_link_libraries(fosterc
  fosterc_base fosterc_parse fosterc_llvm
  ${PROTOBUF_LIBRARY} antlr3c ${LLVM_LDFLAGS})

add_dependencies(fosterc libfoster_bc)

add_dependencies(libfoster_bc chromium_base)
add_dependencies(libfoster_bc cpuid)

#####################################################################

add_executable(unittest_fosterc_base
  ${PROJECT_SOURCE_DIR}/compiler/base/Assert_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/PathManager_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/SourceRange_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/FilteringIterator_unittest.cpp
)
target_link_libraries(unittest_fosterc_base
  fosterc_base fosterc_parse antlr3c gtest_main ${LLVM_LDFLAGS})

#######

add_executable(unittest_fosterc_parse
  ${PROJECT_SOURCE_DIR}/compiler/parse/ANTLRtoFosterAST_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/passes/TypecheckPass.cpp
  ${PROJECT_SOURCE_DIR}/compiler/passes/PrettyPrintPass.cpp
  ${PROJECT_SOURCE_DIR}/third_party/pystring/pystring.cpp
)
target_link_libraries(unittest_fosterc_parse
  fosterc_base fosterc_parse antlr3c gtest_main ${LLVM_LDFLAGS})

#####################################################################

enable_testing()

add_test(bootstrap
  python ${PROJECT_SOURCE_DIR}/scripts/run_all.py
         ${PROJECT_SOURCE_DIR}/test/bootstrap
         ${PROJECT_BINARY_DIR}
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
