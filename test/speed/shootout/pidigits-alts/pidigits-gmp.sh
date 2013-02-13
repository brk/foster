wget ftp://ftp.gnu.org/gnu/gmp/gmp-5.1.0a.tar.bz2
tar xjvf gmp-5.1.0a.tar.bz2
cd gmp-5.1.0/
configure --prefix=`pwd`
make
make install
cd ..

clang -std=gnu99 -Igmp-5.1.0/ -Wall -W -Wshadow -Wsign-compare -O3 -funroll-loops -fomit-frame-pointer pidigits_gmp.c -Lgmp-5.1.0/ gmp-5.1.0/lib/libgmp.a -o pd_gmp.exe

clang -std=gnu99 -Igmp-5.1.0/ -Wall -W -Wshadow -Wsign-compare -O3 -funroll-loops -fomit-frame-pointer pidigits_gmp_pure.c -Lgmp-5.1.0/ gmp-5.1.0/lib/libgmp.a -o pd_gmp_pure.exe
