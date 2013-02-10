#!/bin/sh

~/pin/pin -injection child -t ~/pin/source/tools/SimpleExamples/obj-ia32/opcodemix.so -- ./test-tmpdir/nested-ctor-matching/a.out

echo "OK, take a look at opcodemix.out..."
echo "You can compare opcodemix files using ../scripts/compare-opcodemix.py <mixA> <mixB>"
