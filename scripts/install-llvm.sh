#!/bin/sh

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

LLVM_VERSION=3.9.0
LLVM_V=${LLVM_VERSION}.src
LLVM_ROOT=${HOME}/llvm

# invoke from LLVM_ROOT
checkout_source() {
pushd src
        echo "downloading sources..."
        wget http://llvm.org/releases/${LLVM_VERSION}/cfe-${LLVM_V}.tar.xz
        wget http://llvm.org/releases/${LLVM_VERSION}/compiler-rt-${LLVM_V}.tar.xz
        wget http://llvm.org/releases/${LLVM_VERSION}/llvm-${LLVM_V}.tar.xz
        wget http://llvm.org/releases/${LLVM_VERSION}/lld-${LLVM_V}.tar.xz
        wget http://llvm.org/releases/${LLVM_VERSION}/lldb-${LLVM_V}.tar.xz
        wget http://llvm.org/releases/${LLVM_VERSION}/libcxx-${LLVM_V}.tar.xz
        wget http://llvm.org/releases/${LLVM_VERSION}/libcxxabi-${LLVM_V}.tar.xz

        echo "unpacking sources..."
        for proj in $(ls *-${LLVM_V}.tar.xz); do
          tar -xf ${proj}
        done
        if [ ! -d cfe-${LLVM_V} ]; then
          echo "failed to unpack..."
          exit 1
        fi
        mv lld-${LLVM_V}         llvm-${LLVM_V}/tools/lld
        mv lldb-${LLVM_V}        llvm-${LLVM_V}/tools/lldb
        mv cfe-${LLVM_V}         llvm-${LLVM_V}/tools/clang
        mv compiler-rt-${LLVM_V} llvm-${LLVM_V}/projects/compiler-rt
        mv libcxx-${LLVM_V}      llvm-${LLVM_V}/projects/libcxx
        mv libcxxabi-${LLVM_V}   llvm-${LLVM_V}/projects/libcxxabi
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
        CC=clang CXX=clang++ cmake .. -G "Unix Makefiles" -DCMAKE_INSTALL_PREFIX=${LLVM_ROOT}/${LLVM_VERSION} -DCMAKE_BUILD_TYPE="RelWithDebInfo" -DLLVM_TARGETS_TO_BUILD="host" -DLLVM_ENABLE_ASSERTIONS=ON -DLLVM_LINK_LLVM_DYLIB=ON

	make -j2

	make install
popd
}

mkdir -p ${LLVM_ROOT}
cd ${LLVM_ROOT}

mkdir -p src
mkdir -p ${LLVM_VERSION}

checkout_source
build_source
