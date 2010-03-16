#!/bin/sh

T=../foster/test/bootstrap/$1/`basename $1`.foster
echo "break main" > gdbtestcmds.txt
echo "run $T" >> gdbtestcmds.txt
gdb foster -x gdbtestcmds.txt

