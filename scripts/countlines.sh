#!/bin/sh

FOSTER_SCRIPTS_DIR=$(dirname `which $0`)
cd ${FOSTER_SCRIPTS_DIR}/..

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

runcloc () {
 cloc $@ --quiet --skip-uniqueness --exclude-dir=compiler/me/src/Foster/Fepb,compiler/me/src/Foster/Bepb,compiler/me/src/Llvmpb,compiler/me/dist
}

inspbase () {
  /bin/echo -n "$1" ' '
  shift
  sumof runcloc $@
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

checkargs () {
  case $@ in
    *--help*)
      echo "$0 [--by-file]"
      echo "$0 [--runcloc <directory>]"
      exit
      ;;
    *--by-file*)
      runcloc compiler/base   --by-file --not-match-f="_unittest.cpp"
      runcloc compiler/parse  --by-file --not-match-f="_unittest.cpp"
      runcloc compiler/passes --by-file --not-match-f="_unittest.cpp"
      runcloc compiler/llvm   --by-file --not-match-f="_unittest.cpp"
      runcloc compiler/me     --by-file --not-match-f="_unittest.cpp"
      exit
      ;;
    *--runcloc*)
      shift
      echo "runcloc $@     --by-file --not-match-f='_unittest.cpp'"
            runcloc $@     --by-file --not-match-f="_unittest.cpp"
      exit
      ;;
  esac
}


need cloc
need grep
need awk

checkargs $@

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
insp "third_party    " third_party
