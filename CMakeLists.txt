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

if (${ANTLR_DIR} STREQUAL "ANTLR_DIR-NOTFOUND")
    message("ANTLR not found! Please configure with ccmake or a CMake GUI")
    return()
endif (${ANTLR_DIR} STREQUAL "ANTLR_DIR-NOTFOUND")


set(LLVM_VERSION 2.7)

find_program(LLVM_CONFIG NAMES llvm-config
  PATHS $ENV{HOME}/llvm/${LLVM_VERSION}/bin
  DOC "llvm-config")

# Get flags for LLVM
execute_process(COMMAND ${LLVM_CONFIG} --cppflags
  OUTPUT_VARIABLE LLVM_CFLAGS
)

# We want to control whether our binaries are compiled
# in debug mode independently of whether LLVM was so compiled.
# Stripping -DNDEBUG can cause problems with CallGraph analysis,
# so we simply leave it and use a custom ASSERT() instead of the
# standard <cassert> macro.
string(REPLACE "-g" "" LLVM_CFLAGS "${LLVM_CFLAGS}")

# Hack for now: rather than running all programs JITted from the main fosterc
# compiler binary (and embedding the foster runtime inside the foster compiler)
# we instead compile the foster runtime with llvm-g++ to bitcode, then link the
# foster runtime bitcode in along with the bitcode for a program to run it.
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
  OUTPUT ${PROJECT_BINARY_DIR}/fosterParser.c
         ${PROJECT_BINARY_DIR}/fosterLexer.c
  COMMAND python ${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
                    ${ANTLR_JAR}
                    ${PROJECT_BINARY_DIR}
                    ${PROJECT_SOURCE_DIR}/grammar/foster.g
  DEPENDS
  	grammar/foster.g
	${PROJECT_SOURCE_DIR}/scripts/run_antlr.py
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
  ${PROJECT_SOURCE_DIR}/compiler
  ${PROJECT_SOURCE_DIR}/third_party
  ${PROJECT_SOURCE_DIR}/third_party/chromium_base
)

# Assumes path to LLVM lib dir has no spaces in it!
string(REGEX MATCH "-L[^ ]+" LLVM_LD_PATH "${LLVM_LDFLAGS}")

link_directories(${LLVM_LD_PATH} ${ANTLR_LIBDIR})

add_definitions(${LLVM_CFLAGS})

if (CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
  # Only works with the GNU Gold linker
  set(CMAKE_EXE_LINKER_FLAGS
   "${CMAKE_EXE_LINKER_FLAGS} -Wl,--compress-debug-sections,zlib")
endif(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")

#####################################################################
include(${PROJECT_SOURCE_DIR}/third_party/chromium_base/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/cpuid/CMakeLists.txt)
include(${PROJECT_SOURCE_DIR}/third_party/gtest/CMakeLists.txt)

add_executable(fosterc
  compiler/foster.cpp
  compiler/FosterUtils.cpp
  compiler/base/InputFile.cpp
  compiler/base/PathManager.cpp
  compiler/base/SourceRange.cpp
  compiler/parse/FosterAST.cpp
  compiler/parse/FosterTypeAST.cpp
  compiler/parse/ANTLRtoFosterAST.cpp
  compiler/parse/ANTLRtoFosterErrorHandling.cpp
  compiler/passes/CodegenPass.cpp
  compiler/passes/TypecheckPass.cpp
  compiler/passes/PrettyPrintPass.cpp
  compiler/passes/AddParentLinksPass.cpp
  compiler/passes/ReplaceExprTransform.cpp
  compiler/passes/ClosureConversionPass.cpp
  compiler/llvm/passes/Hello.cpp
  #  compiler/llvm/passes/LLVMCallGraphDotPrinter.cpp
  third_party/pystring/pystring.cpp
  ${PROJECT_BINARY_DIR}/fosterParser.c
  ${PROJECT_BINARY_DIR}/fosterLexer.c
)

target_link_libraries(fosterc antlr3c ${LLVM_LDFLAGS})

add_dependencies(fosterc libfoster_bc)

add_dependencies(libfoster_bc chromium_base)
add_dependencies(libfoster_bc cpuid)

#####################################################################

add_executable(unittest_fosterc
  ${PROJECT_SOURCE_DIR}/compiler/base/PathManager_unittest.cpp
  ${PROJECT_SOURCE_DIR}/compiler/base/Assert_unittest.cpp
)
target_link_libraries(unittest_fosterc gtest_main ${LLVM_LDFLAGS})

#####################################################################

enable_testing()

add_test(bootstrap
  python ${PROJECT_SOURCE_DIR}/test/bootstrap/run_all.py
  ${PROJECT_SOURCE_DIR}/test/bootstrap
  ${PROJECT_BINARY_DIR}
  ${PROJECT_BINARY_DIR}/test-bootstrap-output
  ${LLVM_CONFIG})

# Look for non-silent diff -u output
set(CTEST_CUSTOM_ERROR_MATCH ${CTEST_CUSTOM_ERROR_MATCH}
  "[1-9][0-9] tests failed")

add_test(NAME fosterc
  COMMAND ${PROJECT_BINARY_DIR}/unittest_fosterc)

