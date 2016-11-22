#CXX=$HOME/llvm/3.9.0/bin/clang++
CXX=g++
${CXX} -c -pipe -O3 -fomit-frame-pointer -march=native  -std=c++0x binarytrees.6.c++ -o binarytrees.gpp-6.c++.o &&  \
      ${CXX} binarytrees.gpp-6.c++.o -o binarytrees.gpp-6.gpp_run -lboost_system

perf stat ./binarytrees.gpp-6.gpp_run 19
