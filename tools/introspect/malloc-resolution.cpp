// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <iostream>
#include <cstring>
#include <cstdlib>
#include <inttypes.h>

// Allocates successive small blocks of memory and inspects
// the relative spacing between blocks.
//
// For example, on Mac OS X 10.6, the smallest malloc granularity
// is 16 bytes, even for 1-byte allocations.


void inspect(int size, intptr_t& prevdiff) {
  char* ptr = (char*) malloc(size);
  int n = 5;
  do {
    char* next = (char*) malloc(size);
    intptr_t diff = next - ptr;
    if (diff > 0 && diff != prevdiff) {
      if (((diff - prevdiff) > 0) && (size < 32 || diff < intptr_t(1.4 * float(size)))) {
        if (prevdiff == 0) {
          std::cout << size << "\t" << diff << "\t" << "" << std::endl;
        } else {
          std::cout << size << "\t" << diff << "\t" << (diff - prevdiff) << std::endl;
        }
      }
      prevdiff = diff;
    }
    ptr = next;
  } while (n --> 0);
}

int main() {
  std::cout << "alloc\tsize \tsize " << std::endl;
  std::cout << "size \tclass\tdelta" << std::endl;
  std::cout << "-----\t------------" << std::endl;
  intptr_t prevdiff = 0;
  for (int size = 1; size <= (1<<10); size += 1) {
    inspect(size, prevdiff);
  }
  inspect((1 << 11)     , prevdiff);
  inspect((1 << 12)     , prevdiff);
  inspect((1 << 13)     , prevdiff);
  inspect((1 << 14)     , prevdiff); prevdiff = 0;
  inspect((1 << 15) - 16, prevdiff); prevdiff = 0;
  inspect((1 << 15) -  8, prevdiff); prevdiff = 0;
  inspect((1 << 15)     , prevdiff);
  return 0;
}

/*
Output on Ubuntu 17.10 with the default allocator:

alloc	size 	size 
size 	class	delta
-----	------------
1	32	
25	48	16
73	96	16
89	112	16
105	128	16
121	144	16
[...]
969	992	16
985	1008	16
1001	1024	16
1017	1040	16
2048	2064	
4096	4112	
8192	8208	
16384	16400	
32752	32768	
32760	32768	
32768	32784	

Note the minimum size class of 32, the consistent size deltas of size 16,
and the fact that allocations reserve (at least) 8 bytes for overhead
(for example, malloc(121) returns a 144-byte region, because the size class
for 121+8 bytes is 144).
*/

// Try running with jemalloc:
// clang++ malloc-resolution.cpp -O2 -o malloc-resolution.exe && LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libjemalloc.so ./malloc-resolution.exe
//
/* Output:
alloc	size 	size 
size 	class	delta
-----	------------
1	8	
9	16	8
17	32	16
49	64	16
65	80	16
81	96	16
97	112	16
113	128	16
129	160	32
143	192	32
150	192	32
158	192	32
161	192	32
193	224	32
225	256	32
257	320	64
321	384	64
385	448	64
449	512	64
513	640	128
556	768	128
571	768	128
578	768	128
585	768	128
593	768	128
600	768	128
607	768	128
622	768	128
629	768	128
636	768	128
641	768	128
769	896	128
897	1024	128
2048	2048	1024
4096	4096	2048
8192	8192	4096
16384	16384	8192
32752	32768	
32760	32768	
32768	32768	

Note the 8-byte minimum,
the growing size bins (perfectly reflecting jemalloc's documentation),
and the lack of "inline" metadata space: a 128-byte allocation returns
a 128-byte region 
   */
