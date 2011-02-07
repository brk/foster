#!/bin/sh

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

LLVM_VERSION=2.8
LLVM_ROOT=${HOME}/llvm

# invoke from LLVM_ROOT
download_source() {
pushd src
	echo "downloading llvm..."
	wget http://llvm.org/releases/${LLVM_VERSION}/llvm-${LLVM_VERSION}.tgz
	echo "downloading clang..."
	wget http://llvm.org/releases/${LLVM_VERSION}/clang-${LLVM_VERSION}.tgz

	for ball in *.tgz; do
		echo "extracting $ball..."
		tar xzf $ball
	done

	rm *.tgz

	mv clang-${LLVM_VERSION} llvm-${LLVM_VERSION}/tools/clang
popd
}

# invoke from LLVM_ROOT
build_source () {
pushd src/llvm-${LLVM_VERSION}
	./configure --prefix=${LLVM_ROOT}/${LLVM_VERSION} --enable-targets=host,cpp --enable-debug-symbols --enable-assertions --enable-optimized

	make

	make install
popd
}


mkdir -p ${LLVM_ROOT}
cd ${LLVM_ROOT}

mkdir -p src
mkdir -p ${LLVM_VERSION}

download_source
build_source
