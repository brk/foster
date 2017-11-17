#!/bin/sh

rustc -C opt-level=3 -C target-cpu=core2  src/main.rs -o mandelbrot.exe

perf stat -r 5 ./mandelbrot.exe 2048 > /dev/null
