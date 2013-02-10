#!/bin/sh

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

LLVM_VERSION=3.2
LLVM_V=${LLVM_VERSION}.src
LLVM_ROOT=${HOME}/llvm

# invoke from LLVM_ROOT
checkout_source() {
pushd src
	#echo "checking out llvm..."
        #svn co http://llvm.org/svn/llvm-project/llvm/trunk llvm-${LLVM_VERSION}
	#echo "checking out clang..."
        #svn co http://llvm.org/svn/llvm-project/cfe/trunk  llvm-${LLVM_VERSION}/tools/clang

        echo "downloading sources..."
        wget http://llvm.org/releases/${LLVM_VERSION}/llvm-${LLVM_V}.tar.gz
        wget http://llvm.org/releases/${LLVM_VERSION}/clang-${LLVM_V}.tar.gz
        echo "unpacking sources..."
        for proj in llvm clang; do
          tar -xzf ${proj}-${LLVM_V}.tar.gz
        done
        mv clang-${LLVM_V} llvm-${LLVM_V}/tools/clang
        echo "done unpacking sources..."
popd
}

# invoke from LLVM_ROOT
build_source () {
pushd src/llvm-${LLVM_V}
        echo "building sources..."
	./configure --prefix=${LLVM_ROOT}/${LLVM_VERSION} --enable-targets=host --enable-debug-symbols --enable-optimized

	make -j4

	make install
popd
}

mkdir -p ${LLVM_ROOT}
cd ${LLVM_ROOT}

mkdir -p src
mkdir -p ${LLVM_VERSION}

checkout_source
build_source
