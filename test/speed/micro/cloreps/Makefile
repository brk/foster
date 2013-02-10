GXX=g++ -march=core2 -msse2

default:
	for x in *.cpp; do make `basename-cpp.sh $$x`; done

.PHONY: default

%: %.cpp
	${GXX} $<         -o $*.O0.exe
	${GXX} $<     -S  -o $*.O0.s
	${GXX} $< -O2     -o $*.O2.exe
	${GXX} $< -O2 -S  -o $*.O2.s
	./$*.O0.exe
	./$*.O2.exe

clean:
	rm -f *.exe *.s *~
