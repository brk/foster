#!/bin/sh

P=$1
shift
R=../
D=$R/test/$P
T=$D/`basename $P`.foster

cleanout () {
  rm -f gclog.txt
}

echo "testing $D"
if [ -d $D ]; then
 make fosteroptc fosterparse fosterlower me && cleanout && \
 echo python $R/scripts/run_test.py --verbose ${T} "$@" && \
 python $R/scripts/run_test.py --verbose ${T} "$@"
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
