#!/bin/sh

gcc -std=c99 mandel.c     -o mandel.gcc.O0.exe
gcc -std=c99 mandel.c -O2 -o mandel.gcc.O2.exe
gcc -std=c99 mandel.c -O3 -o mandel.gcc.O3.exe
gcc -std=c99 mandel.c -O3 -fno-unroll-loops -o mandel.gcc.O3.roll.exe
gcc -std=c99 mandel.c -pipe -Wall -O3 -march=native -D_GNU_SOURCE -mfpmath=sse -msse2 -o mandel.gcc.native.exe

gcc -std=c99 mandel.c -O3 -S -o mandel.gcc.O3.s

clang -std=c99 mandel.c     -o mandel.clang.O0.exe
clang -std=c99 mandel.c -O2 -o mandel.clang.O2.exe
clang -std=c99 mandel.c -O3 -o mandel.clang.O3.exe
clang -std=c99 mandel.c -O3 -fno-unroll-loops -o mandel.clang.O3.roll.exe
clang -std=c99 mandel.c -pipe -Wall -O3 -march=native -D_GNU_SOURCE -mfpmath=sse -msse2 -o mandel.clang.native.exe

clang -std=c99 mandel.c -O3 -S -o mandel.clang.O3.s

clang -std=c99 mandel.c -emit-llvm -S -o mandel.O0.ll
clang -std=c99 mandel.c -emit-llvm -O3 -S -o mandel.O3.ll
clang -std=c99 mandel.c -emit-llvm -O3 -fno-unroll-loops -S -o mandel.O3.roll.ll

perf stat ./mandel.gcc.native.exe 2048 > /dev/null
perf stat ./mandel.gcc.O3.exe 2048 > /dev/null
perf stat ./mandel.gcc.O0.exe 2048 > /dev/null
perf stat ./mandel.gcc.O3.roll.exe 2048 > /dev/null
perf stat ./mandel.clang.native.exe 2048 > /dev/null
perf stat ./mandel.clang.O3.exe 2048 > /dev/null
perf stat ./mandel.clang.O0.exe 2048 > /dev/null
perf stat ./mandel.clang.O3.roll.exe 2048 > /dev/null
