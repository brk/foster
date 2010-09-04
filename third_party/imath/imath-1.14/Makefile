##
## Name:     Makefile
## Purpose:  Makefile for imath library and associated tools
## Author:   M. J. Fromberger <http://spinning-yarns.org/michael/>
## Info:     $Id: Makefile 827 2009-02-11 16:35:34Z sting $
##
## Copyright (C) 2002-2008 Michael J. Fromberger, All Rights Reserved.
##

# --- begin configuration section ---

## Generic settings for systems with GCC (default)
## To build with debugging, add DEBUG=Y on the "make" command line.
##
## If building under MacOS 10.1.x, use CC=cc instead.
##
CC=gcc
CFLAGS+=-ansi -pedantic -Wall -I. $(DFLAGS$(DEBUG)) $(SIZEFLAGS$(USELLONG))
LIBS=$(DLIBS$(DEBUG))

DFLAGS=-O3 -funroll-loops -finline-functions
DFLAGSN=$(DFLAGS)
DFLAGSY=-g -DDEBUG=1
#DLIBS=
#DLIBSY=-lefence

## If USELONG=N, disable the use of the "long long" data type; it is
## enabled by default even though it is non-standard.  Define
## USELONG=Y to explicitly enable the use of "long long"
SIZEFLAGS = -Wno-long-long -DUSE_LONG_LONG -D_GNU_SOURCE
SIZEFLAGSN =
SIZEFLAGSY = $(SIZEFLAGS)

# --- end of configuration section ---
VERS=1.14
TARGETS=imtest imtimer pi bintest
HDRS=imath.h imrat.h iprime.h imdrover.h rsamath.h
SRCS=$(HDRS:.h=.c) $(TARGETS:=.c)
OBJS=$(SRCS:.c=.o)
OTHER=LICENSE ChangeLog Makefile doc.txt findsizes.py \
	findthreshold.py imath-test.scm
VPATH += examples
EXAMPLES=basecvt findprime imcalc input rounding rsakey

.PHONY: all test clean distclean dist 

.c.o:
	$(CC) $(CFLAGS) -c $<

all: objs examples test

objs: $(OBJS)

test: imtest pi
	@ echo ""
	@ echo "Running tests, you should not see any 'FAILED' lines here."
	@ echo "If you do, please see doc.txt for how to report a bug."
	@ echo ""
	(cd tests && ./test.sh)

$(EXAMPLES):%: imath.o imrat.o iprime.o %.o
	$(CC) $(CFLAGS) -o $@ $^ $(LIBS)

examples: $(EXAMPLES)

imtest: imtest.o imath.o imrat.o imdrover.o 
	$(CC) $(CFLAGS) -o $@ $^ $(LIBS)

imtimer: imath.c imtimer.c
	$(CC) $(CFLAGS) -DIMATH_TEST -o $@ $^ $(LIBS)

pi: pi.o imath.o
	$(CC) $(CFLAGS) -o $@ $^ $(LIBS)

rtest: rtest.o imath.o rsamath.o 
	$(CC) $(CFLAGS) -o $@ $^ $(LIBS)

bintest: imath.o bintest.o
	$(CC) $(CFLAGS) -o $@ $^ $(LIBS)

clean:
	rm -f *.o *~ core gmon.out tests/*~ tests/gmon.out examples/*~

distclean: clean
	rm -f $(TARGETS) imath-$(VERS).tar imath-$(VERS).tar.gz
	rm -f $(EXAMPLES)

dist: distclean
	@ echo "Packing files for distribution"
	@ tar -cf imtemp.tar --exclude .svn \
		$(HDRS) $(SRCS) $(OTHER) tests examples
	@ mkdir imath-$(VERS)
	@ (cd imath-$(VERS) && tar -xf ../imtemp.tar)
	@ rm -f imtemp.tar
	@ tar -cvf imath-$(VERS).tar imath-$(VERS)
	@ echo "Compressing distribution file: " imath-$(VERS).tar
	@ gzip -9v imath-$(VERS).tar
	@ rm -rf imath-$(VERS)
