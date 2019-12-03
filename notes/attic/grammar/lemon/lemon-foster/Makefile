parser.foster: lemon-foster lempar.foster
	cp ../parser.lemon .
	lemon-foster -l parser.lemon
	mv parser.c parser.foster
	rm parser.lemon

lemon-foster: lemon-foster.c
	clang lemon-foster.c -o lemon-foster -O0

clean:
	rm -f parser.foster parser.c
