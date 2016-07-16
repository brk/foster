default: all

OBJ=_obj

${OBJ}:
	mkdir -p ${OBJ}

all: ${OBJ} ${OBJ}/switch-vs-vtable-default ${OBJ}/switch-vs-vtable-O2 ${OBJ}/malloc-resolution-default

${OBJ}/switch-vs-vtable-default: switch-vs-vtable.cpp f.cpp
	g++ switch-vs-vtable.cpp f.cpp -o ${OBJ}/switch-vs-vtable-default

${OBJ}/switch-vs-vtable-O2: switch-vs-vtable.cpp f.cpp
	g++ switch-vs-vtable.cpp f.cpp -o ${OBJ}/switch-vs-vtable-O2 -O2

${OBJ}/malloc-resolution-default: malloc-resolution.cpp
	g++ malloc-resolution.cpp -o ${OBJ}/malloc-resolution-default
