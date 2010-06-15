// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef LIBFOSTER_H
#define LIBFOSTER_H

// This file exists to provide symbols to link
// libfoster_main.cpp::main() to libfoster

namespace foster {
namespace runtime {

void initialize();
void cleanup();

} }

#endif
