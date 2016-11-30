#!/bin/sh

gcc -std=c99 mandel.c     -o mandel.O0.exe
gcc -std=c99 mandel.c -O3 -o mandel.O3.exe
gcc -pipe -Wall -O3 -march=native -std=c99 -D_GNU_SOURCE -mfpmath=sse -msse2 -o mandel.native.exe
