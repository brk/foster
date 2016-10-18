CXX=g++
${CXX} -c -pipe -O3 -fomit-frame-pointer -march=native  -std=c++0x binarytrees.7.c++ -o binarytrees.gpp-7.c++.o &&  \
      ${CXX} binarytrees.gpp-7.c++.o -o binarytrees.gpp-7.gpp_run -fopenmp -lboost_system

perf stat ./binarytrees.gpp-7.gpp_run 20
