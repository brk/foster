PROJ=fost

CC=clang
GRAMMAR=parser.lemon

help:
	echo "Targets to consider:"
	echo "   tokendumper.exe spits out lexed token info."
	echo "   fost8.exe combines a lemon-generated parser with re2c-generated lexer."
	echo ""
	echo "   fosterlexer.c contains the re2c-generated lexer."

fost8.exe: parser.c parserdriver.c fosterlexer.c
	$(CC) -O3 $(CFLAGS) -o $@ parser.c parserdriver.c fosterlexer.c

tokendumper.exe: tokendumper.c fosterlexer.c parser.h
	$(CC) -O3 $(CFLAGS) -o $@ tokendumper.c fosterlexer.c

tokencount.exe: fosterlexer.noyych.c parser.h
	$(CC) -O3 $(CFLAGS) -o $@ fosterlexer.noyych.c tokencount.c

fosterlexer.c: fosterlexer.re
	re2c -o fosterlexer.c fosterlexer.re --input custom -8 -W

fosterlexer.noyych.c: fosterlexer.re
	re2c -o fosterlexer.noyych.c fosterlexer.re --input custom -8 -W

parser.h: parser.c
	echo

parser.c: parser.lemon
	lemon parser.lemon

lexer.png: lexer.dot
	dot -Tpng lexer.dot > lexer.png

lexer.dot: fosterlexer.re
	re2c -D -o lexer.dot -8 fosterlexer.re

tokendumper.combined.c:
	cat fosterlexer.c  > tokendumper.combined.c
	cat tokendumper.c >> tokendumper.combined.c
	$(CC) -O3 $(CFLAGS) -o td.c.exe tokendumper.combined.c

.PHONY: clean tokendumper.combined.c

clean:
	rm -f fost8.exe tokendumper.exe fosterlexer.c parser.c parser.h lexer.dot lexer.png parser.out
