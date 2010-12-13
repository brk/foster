OTT=/home/benkarel/tmp/ott_distro_0.20.1/bin/ott

SOURCES = \
	  foster.ott

default: output/foster.pdf

output:
	mkdir -p output

output/foster.tex: output $(SOURCES)
	$(OTT) -merge true -o output/foster.tex $(SOURCES)

output/foster.pdf: output/foster.tex
	make -C output -f ../latexMakefile
