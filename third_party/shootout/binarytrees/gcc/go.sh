gcc -O3 -fomit-frame-pointer -funroll-loops -static binarytrees.c -lm -o binary-trees_run

perf stat ./binary-trees_run 19
