#!/bin/sh

SD=$(dirname `which $0`)/../scripts
R=$(python $SD/normpath.py $SD/..)
P=$1
shift

D=$R/test/$P

tmpfile=$(mktemp foster-gotest.XXXXXX)

# Allow running   gotest.sh array-prim-literals
# instead of      gotest.sh bootstrap/arrays/array-prim-literals
# as long as there's only one such subdirectory with that name.
if [ ! -d $D ]; then
  find $R/test -path "*$P*" -type d > $tmpfile
  nlines=$(wc -l < $tmpfile | sed 's/ *//')
  case $nlines in
  0)
    # No test by that name; silently fall through
    # and prompt to create it.
    ;;
  1)
    D=$(head -n 1 $tmpfile)
    ;;
  *)
    echo "Warning: multiple tests found..."
    cat $tmpfile | sed 's/^/    /'
    ;;
  esac
fi

rm $tmpfile

T=$D/`basename $D`.foster

if [ -z "$R" ]; then
  echo "Unable to compute project root, exiting!"
  exit 1
fi

cleanout () {
  rm -f gclog.txt
}

cxxcompilerpath () {
  cat $R/_obj/CMakeCache.txt | grep CXX_COMPILER:FILEPATH | sed 's/CMAKE_CXX_COMPILER:FILEPATH=//'
}

clangpath () {
  cat $R/_obj/CMakeCache.txt | grep CLANG:FILEPATH | sed 's/CLANG:FILEPATH=//'
}

cxxpath() {
  local P=`clangpath`
  if [ "x${P}" = "x" ];
  then echo `cxxcompilerpath`
  else echo ${P}
  fi
}

build_prereqs() {
  if [ -f $R/_obj/Makefile]; then
    make -s -C $R/_obj fosteroptc fosterparse fosterlower me && cleanout
  elif [ -f $R/_obj/build.ninja ]; then
    ninja -C $R/_obj fosteroptc fosterparse fosterlower me && cleanout
  else
    cmake --build $R/_obj --target fosteroptc && \
    cmake --build $R/_obj --target fosterparse && \
    cmake --build $R/_obj --target fosterlower && \
    cmake --build $R/_obj --target me && cleanout
  fi
}

echo "testing $D"
if [ -d $D ]; then
 build_prereqs && \
 echo python $R/scripts/run_test.py --show-cmdlines ${T} "$@" && \
      python $R/scripts/run_test.py --show-cmdlines ${T} "$@" --bindir=$R/_obj --me-arg=--interactive --cxxpath=`cxxpath` -I ${R}/stdlib
else
  echo "Make new test $T? y/[n]"
  read CONFIRM
  if [ "$CONFIRM" = "y" ]; then
    mkdir -p $D
    ${EDITOR} ${T}
  fi
fi

