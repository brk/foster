ROOT=../..

test: main.exe
	./main.exe

main.exe: main.o code.o
	gcc main.o code.o -o main.exe

main.o: main.c
	gcc main.c -c -o main.o

code.o: code.foster
	${ROOT}/_obj/fosterparse code.foster _out.parsed.pb
	${ROOT}/_obj/me _out.parsed.pb _out.checked.pb +RTS -K400M -RTS --standalone
	${ROOT}/_obj/fosterlower _out.checked.pb --standalone -o out -outdir . --unsafe-disable-gc
	${ROOT}/_obj/fosteroptc    out.preopt.bc -o code.o -O0
	rm *.pb *.bc

clean:
	rm -f *.pb *.o *~ main.exe
