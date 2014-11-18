#!/bin/sh

SD=$(dirname `which $0`)/../scripts
R=$(python $SD/normpath.py $SD/..)
P=$1
shift
D=$R/test/$P
T=$D/`basename $P`.foster

if [ -z "$R" ]; then
  echo "Unable to compute project root, exiting!"
  exit 1
fi

cleanout () {
  rm -f gclog.txt
}

echo "testing $D"
if [ -d $D ]; then
 make -C $R/_obj fosteroptc fosterparse fosterlower me && cleanout && \
 echo python $R/scripts/run_test.py --show-cmdlines ${T} "$@" && \
      python $R/scripts/run_test.py --show-cmdlines ${T} "$@" --bindir=$R/_obj --me-arg=--interactive
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
