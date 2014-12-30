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

cxxpath () {
  cat $R/_obj/CMakeCache.txt | grep CXX_COMPILER:FILEPATH | sed 's/CMAKE_CXX_COMPILER:FILEPATH=//'
}

echo "testing $D"
if [ -d $D ]; then
 make -s -C $R/_obj fosteroptc fosterparse fosterlower me && cleanout && \
 echo python $R/scripts/run_test.py --show-cmdlines ${T} "$@" && \
      python $R/scripts/run_test.py --show-cmdlines ${T} "$@" --bindir=$R/_obj --me-arg=--interactive --cxxpath=`cxxpath`
else
  echo "Make new test $T? y/[n]"
  read CONFIRM
  if [ "$CONFIRM" = "y" ]; then
    mkdir -p $D
    ${EDITOR} ${T}
  else
    echo "_${CONFIRM}_"
  fi
fi
