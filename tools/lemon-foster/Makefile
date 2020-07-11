lemon-foster: lemon-foster.c lempar.foster
	clang lemon-foster.c -o lemon-foster -O0

parser.foster: parser.lemon lemon-foster lempar.foster
	lemon-foster -l parser.lemon

clean:
	rm -f parser.foster parser.c
