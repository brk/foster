clang -std=gnu99 -Igmp-5.1.0/ -Wall -W -Wshadow -Wsign-compare -O3 -funroll-loops -fomit-frame-pointer addtobits_gmp.c -Lgmp-5.1.0/ gmp-5.1.0/lib/libgmp.a -o a2b_gmp.exe

#clang -std=gnu99 -Igmp-5.1.0/ -Wall -W -Wshadow -Wsign-compare -O3 -funroll-loops -fomit-frame-pointer pidigits_gmp_pure.c -Lgmp-5.1.0/ gmp-5.1.0/lib/libgmp.a -o pd_gmp_pure.exe
