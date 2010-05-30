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

# Hack for now: rather than running all programs JITted from the main foster
# compiler binary (and embedding the foster runtime inside the foster compiler)
# we instead compile the foster runtime with llvm-g++ to bitcode, then link the
# foster runtime bitcode in along with the bitcode for a program to run it.
# For now I'm reusing an older version 2.5 llvm-g++ installation rather than
# installing the MacPorts version. Since (I hope?) there is link compatibility
# of bitcode files produced with different versions of llvm-g++, it shouldn't
# be a problem...
find_program(LLVM_G++ NAMES llvm-g++ clang++ clang
  PATHS
        /usr/bin
        $ENV{HOME}/llvm/${LLVM_VERSION}/gcc/bin
        $ENV{HOME}/llvm/${LLVM_VERSION}/bin
        /usr/lib/llvm/llvm/gcc-4.2/bin
  DOC "C++ compiler to emit LLVM bytecode: llvm-g++ or clang++")


execute_process(COMMAND ${LLVM_CONFIG} --bindir
  OUTPUT_VARIABLE LLVM_BINDIR
)

message("LLVM_CONFIG is ${LLVM_CONFIG}")

# If llvm-config isn't found, LLVM_BINDIR will be empty
# and CMake will report an error here.
string(REPLACE "\n" "" LLVM_BINDIR ${LLVM_BINDIR})

# Collect the linker flags for us to link against LLVM
execute_process(COMMAND ${LLVM_CONFIG} --ldflags --libs core jit interpreter native linker
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
  COMMAND python ${PROJECT_SOURCE_DIR}/run_antlr.py
                    ${ANTLR_JAR}
                    ${PROJECT_BINARY_DIR}
                    ${PROJECT_SOURCE_DIR}/grammar/foster.g
  DEPENDS grammar/foster.g
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
	${PROJECT_BINARY_DIR}
	"${LLVM_BINDIR}"
	${LIBFOSTER_CPP_SOURCES}
  DEPENDS ${LIBFOSTER_CPP_SOURCES} ${PROJECT_SOURCE_DIR}/scripts/build_libfoster.py
)
add_custom_target(libfoster_bc DEPENDS ${PROJECT_BINARY_DIR}/libfoster.bc)


# Look for ANTLR-generated lexer and parser, and ANTLR library files
include_directories(${ANTLR_DIR}/include ${PROJECT_BINARY_DIR})

include_directories(
  ${PROJECT_SOURCE_DIR}/compiler
  ${PROJECT_SOURCE_DIR}/compiler/passes
  ${PROJECT_SOURCE_DIR}/third_party)

# Assumes path to LLVM lib dir has no spaces in it!
string(REGEX MATCH "-L[^ ]+" LLVM_LD_PATH "${LLVM_LDFLAGS}")

link_directories(${LLVM_LD_PATH} ${ANTLR_LIBDIR})

set(DEBUG_FLAGS -g -DDEBUG)
add_definitions(${LLVM_CFLAGS} ${DEBUG_FLAGS})

if (CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")
  # Only works with the GNU Gold linker
  set(CMAKE_EXE_LINKER_FLAGS
   "${CMAKE_EXE_LINKER_FLAGS} -Wl,--compress-debug-sections,zlib")
endif(CMAKE_HOST_SYSTEM_NAME STREQUAL "Linux")

add_executable(foster
  compiler/ANTLRtoFosterAST.cpp
  compiler/FosterAST.cpp
  compiler/FosterUtils.cpp
  compiler/foster.cpp
  compiler/passes/CodegenPass.cpp
  compiler/passes/TypecheckPass.cpp
  compiler/passes/PrettyPrintPass.cpp
  compiler/passes/AddParentLinksPass.cpp
  compiler/passes/ReplaceExprTransform.cpp
  compiler/passes/ClosureConversionPass.cpp
  third_party/pystring/pystring.cpp
  ${PROJECT_BINARY_DIR}/fosterParser.c
  ${PROJECT_BINARY_DIR}/fosterLexer.c
)

target_link_libraries(foster antlr3c ${LLVM_LDFLAGS})

add_dependencies(foster libfoster_bc)

#####################################################################

enable_testing()

add_test(bootstrap python ${PROJECT_SOURCE_DIR}/test/bootstrap/run_all.py
  ${PROJECT_SOURCE_DIR}/test/bootstrap
  ${PROJECT_BINARY_DIR}
  ${PROJECT_BINARY_DIR}/test-bootstrap-output
  ${LLVM_CONFIG})

# Look for non-silent diff -u output
set(CTEST_CUSTOM_ERROR_MATCH ${CTEST_CUSTOM_ERROR_MATCH}
  "[1-9][0-9] tests failed")
