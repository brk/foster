default: all

OBJ=_obj

${OBJ}:
	mkdir -p ${OBJ}

all: ${OBJ} ${OBJ}/switch-vs-vtable-default ${OBJ}/switch-vs-vtable-O2 ${OBJ}/malloc-resolution-default ${OBJ}/int-checks-O2

${OBJ}/switch-vs-vtable-default: switch-vs-vtable.cpp f.cpp
	g++ switch-vs-vtable.cpp f.cpp -o ${OBJ}/switch-vs-vtable-default

${OBJ}/switch-vs-vtable-O2: switch-vs-vtable.cpp f.cpp
	g++ switch-vs-vtable.cpp f.cpp -o ${OBJ}/switch-vs-vtable-O2 -O2

${OBJ}/malloc-resolution-default: malloc-resolution.cpp
	g++ malloc-resolution.cpp -o ${OBJ}/malloc-resolution-default

${OBJ}/int-checks-O2: int-checks.cpp ${OBJ} Makefile
	clang slowpath.c -c -o ${OBJ}/slowpath.o -O2
	clang++ -std=c++11 int-checks.cpp ${OBJ}/slowpath.o -o ${OBJ}/int-checks-O2 -O2
	clang++ -std=c++11 int-checks.cpp -O2 -c -S -o ${OBJ}/int-checks.O2.s
	clang++ -std=c++11 int-checks.cpp -O2 -c -emit-llvm -S -o ${OBJ}/int-checks.O2.llvm

bench32: ${OBJ}/int-checks-O2
	${OBJ}/int-checks-O2 100 500 highbit_32_1e2
	${OBJ}/int-checks-O2 100 500 highbit_32_1e5
	${OBJ}/int-checks-O2 100 500 lowbit_32_1e2
	${OBJ}/int-checks-O2 100 500 lowbit_32_1e5
	#
	${OBJ}/int-checks-O2 100000 500 highbit_32_1e2
	${OBJ}/int-checks-O2 10000  500 highbit_32_1e5
	${OBJ}/int-checks-O2 100000 500 lowbit_32_1e2
	${OBJ}/int-checks-O2 10000  500 lowbit_32_1e5
	#
	${OBJ}/int-checks-O2 100   1 highbit_32_1e5
	${OBJ}/int-checks-O2 100  10 highbit_32_1e5
	${OBJ}/int-checks-O2 100 100 highbit_32_1e5
	${OBJ}/int-checks-O2 100 250 highbit_32_1e5
	${OBJ}/int-checks-O2 100 500 highbit_32_1e5
	${OBJ}/int-checks-O2 100 750 highbit_32_1e5
	${OBJ}/int-checks-O2 100 900 highbit_32_1e5
	${OBJ}/int-checks-O2 100 990 highbit_32_1e5
	${OBJ}/int-checks-O2 100 999 highbit_32_1e5
	#
	${OBJ}/int-checks-O2 100   1 lowbit_32_1e5
	${OBJ}/int-checks-O2 100  10 lowbit_32_1e5
	${OBJ}/int-checks-O2 100 100 lowbit_32_1e5
	${OBJ}/int-checks-O2 100 250 lowbit_32_1e5
	${OBJ}/int-checks-O2 100 500 lowbit_32_1e5
	${OBJ}/int-checks-O2 100 750 lowbit_32_1e5
	${OBJ}/int-checks-O2 100 900 lowbit_32_1e5
	${OBJ}/int-checks-O2 100 990 lowbit_32_1e5
	${OBJ}/int-checks-O2 100 999 lowbit_32_1e5
	#
	${OBJ}/int-checks-O2 100 500 bare_32_1e5

bench64: ${OBJ}/int-checks-O2
	${OBJ}/int-checks-O2 100 500 highbit_64_1e2
	${OBJ}/int-checks-O2 100 500 highbit_64_1e5
	${OBJ}/int-checks-O2 100 500 lowbit_64_1e2
	${OBJ}/int-checks-O2 100 500 lowbit_64_1e5
	#
	${OBJ}/int-checks-O2 100000 500 highbit_64_1e2
	${OBJ}/int-checks-O2 10000  500 highbit_64_1e5
	${OBJ}/int-checks-O2 100000 500 lowbit_64_1e2
	${OBJ}/int-checks-O2 10000  500 lowbit_64_1e5
	#
	${OBJ}/int-checks-O2 100   1 highbit_64_1e5
	${OBJ}/int-checks-O2 100  10 highbit_64_1e5
	${OBJ}/int-checks-O2 100 100 highbit_64_1e5
	${OBJ}/int-checks-O2 100 250 highbit_64_1e5
	${OBJ}/int-checks-O2 100 500 highbit_64_1e5
	${OBJ}/int-checks-O2 100 750 highbit_64_1e5
	${OBJ}/int-checks-O2 100 900 highbit_64_1e5
	${OBJ}/int-checks-O2 100 990 highbit_64_1e5
	${OBJ}/int-checks-O2 100 999 highbit_64_1e5
	#
	${OBJ}/int-checks-O2 100   1 lowbit_64_1e5
	${OBJ}/int-checks-O2 100  10 lowbit_64_1e5
	${OBJ}/int-checks-O2 100 100 lowbit_64_1e5
	${OBJ}/int-checks-O2 100 250 lowbit_64_1e5
	${OBJ}/int-checks-O2 100 500 lowbit_64_1e5
	${OBJ}/int-checks-O2 100 750 lowbit_64_1e5
	${OBJ}/int-checks-O2 100 900 lowbit_64_1e5
	${OBJ}/int-checks-O2 100 990 lowbit_64_1e5
	${OBJ}/int-checks-O2 100 999 lowbit_64_1e5
	#
	${OBJ}/int-checks-O2 100 500 bare_64_1e5
