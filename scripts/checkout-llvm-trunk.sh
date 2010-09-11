#!/bin/sh

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

LLVM_VERSION=trunk
LLVM_ROOT=${HOME}/llvm

# invoke from LLVM_ROOT
checkout_source() {
pushd src
	echo "checking out llvm..."
        svn co http://llvm.org/svn/llvm-project/llvm/trunk llvm-${LLVM_VERSION}
	echo "checking out clang..."
        svn co http://llvm.org/svn/llvm-project/cfe/trunk  llvm-${LLVM_VERSION}/tools/clang
popd
}

# invoke from LLVM_ROOT
build_source () {
pushd src/llvm-${LLVM_VERSION}
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
