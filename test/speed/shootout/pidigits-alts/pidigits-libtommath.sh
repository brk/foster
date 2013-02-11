#git clone git://github.com/libtom/libtommath.git
make -C libtommath CC='cc -DBN_MP_DIV_SMALL'
mv libtommath/libtommath.a libtommath_divsmall.a
make -C libtommath clean
make -C libtommath
mv libtommath/libtommath.a libtommath_divbig.a
make -C libtommath clean

cc -Ilibtommath/ -Wall -W -Wshadow -Wsign-compare -O3 -funroll-loops -fomit-frame-pointer pidigits_ltm.c libtommath_divsmall.a -o pd_small
cc -Ilibtommath/ -Wall -W -Wshadow -Wsign-compare -O3 -funroll-loops -fomit-frame-pointer pidigits_ltm.c libtommath_divbig.a   -o pd_big
