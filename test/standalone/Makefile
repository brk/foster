ROOT=../..

.SUFFIXES:

test: main.exe
	./main.exe

main.exe: main.o code.foster.o
	gcc main.o code.foster.o -o main.exe

main.o: main.c
	gcc main.c -c -o main.o

code.foster.o: code.foster
	fosterc-standalone code.foster

clean:
	rm -f *.pb *.o *~ main.exe
