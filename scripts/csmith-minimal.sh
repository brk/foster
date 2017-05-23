#!/bin/sh
~/sw/local/csmith-2.3.0/bin/csmith --no-argc --no-arrays --no-bitfields --no-checksum --no-comma-operators --no-divs --nomain --no-safe-math --no-packed-struct --no-paranoid --no-pointers --no-structs --no-unions --no-volatiles --no-volatile-pointers --no-global-variables --no-builtins --max-array-dim 2 --max-array-len-per-dim 64 --max-block-depth 3 --max-block-size 4 --max-expr-complexity 4 --max-funcs 4 --max-pointer-depth 3 --max-struct-fields 4 --max-union-fields 4
echo '#include <inttypes.h>'
echo 'int main() { printf("0x%" PRIX64 "\\n", (uint64_t) func_1()); return 0; }'
