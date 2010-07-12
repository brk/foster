#!/bin/sh

D=../foster/test/$1
T=$D/`basename $1`.foster

shift

if [ -d $D ]; then
    ./test.sh ${T} $@
else
  echo "Make new test $T? y/[n]"
  read CONFIRM
  if [ "$CONFIRM" = "y" ]; then
    mkdir -p $D
    vim ${T}
  else
    echo "_${CONFIRM}_"
  fi
fi
