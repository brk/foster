#!/bin/sh

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

LLVM_VERSION=12.0.0
LLVM_V=${LLVM_VERSION}.src
LLVM_ROOT=${HOME}/llvm

# $0 is either a path to the script,
# implying `which` will return an empty string,
# or it's a path, in which case we should use `which`.
if [ "x$(which $0)" == "x" ]; then
SD=$(dirname $0)/../scripts
else
SD=$(dirname `which $0`)/../scripts
fi

FOSTER_ROOT=$($SD/normpath.py $SD/..)
MAKEJ=$(${FOSTER_ROOT}/third_party/vstinner_perf/makej)

# https://github.com/llvm/llvm-project/releases/download/llvmorg-10.0.0/llvm-10.0.0.src.tar.xz
download_llvm_component () {
  wget https://github.com/llvm/llvm-project/releases/download/llvmorg-${LLVM_VERSION}/${1}-${LLVM_V}.tar.xz
}


# invoke from LLVM_ROOT
checkout_source() {
pushd src
        echo "downloading sources..."
        download_llvm_component llvm
        download_llvm_component clang
        download_llvm_component compiler-rt
        download_llvm_component lld
        download_llvm_component lldb
        download_llvm_component libcxx
        download_llvm_component libcxxabi
        download_llvm_component libunwind
        #download_llvm_component clang-tools-extra

        echo "unpacking sources..."
        for proj in $(ls *-${LLVM_V}.tar.xz); do
          tar -xf ${proj}
        done
        if [ ! -d clang-${LLVM_V} ]; then
          echo "failed to unpack..."
          exit 1
        fi
        mv lld-${LLVM_V}         llvm-${LLVM_V}/tools/lld
        mv lldb-${LLVM_V}        llvm-${LLVM_V}/tools/lldb
        mv clang-${LLVM_V}       llvm-${LLVM_V}/tools/clang
        mv compiler-rt-${LLVM_V} llvm-${LLVM_V}/projects/compiler-rt
        mv libcxx-${LLVM_V}      llvm-${LLVM_V}/projects/libcxx
        mv libcxxabi-${LLVM_V}   llvm-${LLVM_V}/projects/libcxxabi
        mv libunwind-${LLVM_V}   llvm-${LLVM_V}/runtimes/libunwind
        #mv clang-tools-extra-${LLVM_V} llvm-${LLVM_V}/tools/clang/tools/extra

        echo "done unpacking sources..."
popd
}

# invoke from LLVM_ROOT
build_source () {
pushd src/llvm-${LLVM_V}
        echo "building sources..."

        rm -rf build
        mkdir -p build
        cd       build

        # Note: it's OK to use GCC 4.x instead of Clang, I think, but using GCC 5 will lead
        # to pain and suffering until the whole cxx11 abi_tag situation gets worked out.
        #CC=clang CXX=clang++
        cmake .. -G "Unix Makefiles" -DCMAKE_INSTALL_PREFIX=${LLVM_ROOT}/${LLVM_VERSION} -DCMAKE_BUILD_TYPE="RelWithDebInfo" -DLLVM_TARGETS_TO_BUILD="host" -DLLVM_ENABLE_ASSERTIONS=ON -DLLVM_LINK_LLVM_DYLIB=ON
        # On macOS, add: -DDEFAULT_SYSROOT="$(xcrun --show-sdk-path)"

	time make -j${MAKEJ}

	make install
popd
}

mkdir -p ${LLVM_ROOT}
cd ${LLVM_ROOT}

mkdir -p src
mkdir -p ${LLVM_VERSION}

checkout_source
build_source
