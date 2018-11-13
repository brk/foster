parser.foster: parser.lemon lemon-foster lempar.c
	lemon-foster -l parser.lemon
	mv parser.c parser.foster

lemon-foster: lemon-foster.c
	clang lemon-foster.c -o lemon-foster -O0

clean:
	rm -f parser.foster parser.c
