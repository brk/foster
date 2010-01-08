cmake_minimum_required (VERSION 2.6)
project (foster)

# Look for ANTLR-generated lexer and parser
include_directories (output)

set(ANTLR_VERSION 3.2 CACHE STRING "ANTLR library version (not ANTLRWorks!)")
find_path(ANTLR_DIR antlr-${ANTLR_VERSION}.jar
  PATHS $ENV{HOME}/antlr/${ANTLR_VERSION}
  DOC   "ANTLR library install dir")
set(ANTLR_JAR ${ANTLR_DIR}/antlr-${ANTLR_VERSION}.jar CACHE FILEPATH "ANTLR jarfile")
set(ANTLR_LIBDIR ${ANTLR_DIR}/lib)

set(LLVM_VERSION 2.6)

find_program(LLVM_CONFIG NAMES llvm-config
  PATHS $ENV{HOME}/llvm/${LLVM_VERSION}/bin
  DOC "llvm-config")

# Get flags for LLVM
execute_process(COMMAND ${LLVM_CONFIG} --cppflags
  OUTPUT_VARIABLE LLVM_CFLAGS
)

execute_process(COMMAND ${LLVM_CONFIG} --ldflags --libs core jit interpreter native
  OUTPUT_VARIABLE LLVM_LDFLAGS
)

string(REPLACE "\n" "" LLVM_LDFLAGS ${LLVM_LDFLAGS})
string(STRIP ${LLVM_LDFLAGS} LLVM_LDFLAGS)

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

include_directories(${ANTLR_DIR}/include)
# Assumes path to LLVM lib dir has no spaces in it!
string(REGEX MATCH "-L[^ ]+" LLVM_LD_PATH ${LLVM_LDFLAGS})

link_directories(${LLVM_LD_PATH} ${ANTLR_LIBDIR})

set(DEBUG_FLAG -g)
add_definitions(${LLVM_CFLAGS} ${DEBUG_FLAG})

add_executable(foster
  compiler/ANTLRtoFosterAST.cpp
  compiler/FosterAST.cpp
  compiler/foster.cpp
  ${PROJECT_BINARY_DIR}/fosterParser.c
  ${PROJECT_BINARY_DIR}/fosterLexer.c
)

target_link_libraries(foster antlr3c ${LLVM_LDFLAGS})

