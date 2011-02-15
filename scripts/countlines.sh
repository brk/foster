#!/bin/sh

title () {
  echo ""
  echo ""
  echo "****************************************************"
  echo "             " $@
  echo "****************************************************"
}

sumof () {
  $@ | grep SUM | awk '{print $5}'
}

inspbase () {
  /bin/echo -n "$1" ' '
  shift
  sumof cloc $@ --quiet --skip-uniqueness --exclude-dir=compiler/me/src/Foster/Fepb,compiler/me/src/Foster/Bepb
}

insp () {
  inspbase "$@" --not-match-f="_unittest.cpp"
}

need () {
  if [ "q" = "q`which $1`" ]; then
    echo "Must have $1 in PATH"
    exit
  fi
}

need cloc
need grep
need awk

# title "runtime"
# cloc --quiet runtime --by-file

/bin/echo -n "notes            "
cat   notes/*.rst notes/*.txt | wc -l | awk '{print $1}'
echo

insp 'compiler/*.cpp ' compiler/*.cpp
insp "compiler/passes" compiler/passes compiler/include/foster/passes
insp "compiler/parse " compiler/parse  compiler/include/foster/parse
insp "compiler/base  " compiler/base   compiler/include/foster/base
insp "compiler/llvm  " compiler/llvm
insp "compiler/me    " compiler/me

echo
insp "runtime        " runtime
insp "compiler       " compiler
inspbase "unittests      " compiler --match-f="_unittest.cpp"
insp "third_party    " third_party
