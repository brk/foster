#clang -O2 base64_encode.c -o b64e.exe
#perf stat -d ./b64e.exe
#rm b64e.exe

clang -O2 sta/base64_sta.c -o b64_sta.exe
clang -O2 sta/base64_sta.c -S -c -o b64_sta.s
clang -O2 sta/base64_sta.c -S -c -emit-llvm -o b64_sta.ll

perf stat -d ./b64_sta.exe


clang -O2 dyn/base64_dyn.c -o b64_dyn.exe
clang -O2 dyn/base64_dyn.c -S -c -o b64_dyn.s
clang -O2 dyn/base64_dyn.c -S -c -emit-llvm -o b64_dyn.ll

perf stat -d ./b64_dyn.exe


clang -O2 dyn/base64_fos.c -o b64_fos.exe
clang -O2 dyn/base64_fos.c -S -c -o b64_fos.s
clang -O2 dyn/base64_fos.c -S -c -emit-llvm -o b64_fos.ll

perf stat -d ./b64_fos.exe


clang -O2 dyn/base64_alt.c -o b64_alt.exe
clang -O2 dyn/base64_alt.c -S -c -o b64_alt.s
clang -O2 dyn/base64_alt.c -S -c -emit-llvm -o b64_alt.ll

perf stat -d ./b64_alt.exe

rm *.exe
