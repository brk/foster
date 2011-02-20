#!/bin/sh

P=$1
shift
D=../foster/test/$P
T=$D/`basename $P`.foster

cleanout () {
  rm -f gclog.txt
}

if [ -d $D ]; then
 make fosteroptc fosterparse fosterlower me && cleanout
 echo python ../foster/scripts/run_test.py --verbose ${T} "$@"
 python ../foster/scripts/run_test.py --verbose ${T} "$@"
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
