#!/bin/sh

T=../foster/test/$1/`basename $1`.foster
echo "break main" > gdbtestcmds.txt
echo "run $T" >> gdbtestcmds.txt
gdb fosterc -x gdbtestcmds.txt

