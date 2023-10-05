#!/bin/sh

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

LLVM_VERSION=17.0.1
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

# invoke from LLVM_ROOT
checkout_source() {
pushd src
        echo "downloading sources..."
        wget https://github.com/llvm/llvm-project/archive/refs/tags/llvmorg-${LLVM_VERSION}.tar.gz

        echo "unpacking sources..."
        tar -xf llvmorg-${LLVM_VERSION}.tar.gz

        echo "done unpacking sources..."
popd
}

# invoke from LLVM_ROOT
build_source () {
pushd src/llvm-project-llvmorg-${LLVM_VERSION}
        echo "building sources..."

        #CC=clang CXX=clang++
        cmake -S llvm -B build -G "Unix Makefiles" -DCMAKE_INSTALL_PREFIX=${LLVM_ROOT}/${LLVM_VERSION} -DCMAKE_BUILD_TYPE="RelWithDebInfo" -DLLVM_TARGETS_TO_BUILD="host" -DLLVM_ENABLE_ASSERTIONS=ON -DLLVM_LINK_LLVM_DYLIB=ON -DLLVM_ENABLE_PROJECTS="clang;lld"
        # On macOS, add: -DDEFAULT_SYSROOT="$(xcrun --show-sdk-path)"

	cd build

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
