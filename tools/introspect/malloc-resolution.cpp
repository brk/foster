// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <iostream>
#include <cstring>

// Allocates successive small blocks of memory and inspects
// the relative spacing between blocks.
//
// For example, on Mac OS X 10.6, the smallest  malloc granularity
// is 16 bytes, even for 1-byte allocations.

int main() {
  std::cout << "alloc\tdiff from" << std::endl;
  std::cout << "size \tprev ptr " << std::endl;
  std::cout << "-----\t---------" << std::endl;
  for (int size = 1; size <= 32; size += 1) {
    char* ptr = (char*) malloc(size);
    int n = 5;
    do {
      char* next = (char*) malloc(size);
      ptrdiff_t diff = next - ptr;
      std::cout << size << "\t" << diff << std::endl;
      ptr = next;
    } while (n --> 0);
  }
  return 0;
}
