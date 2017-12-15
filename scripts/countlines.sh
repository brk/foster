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
 cloc $@ --quiet --skip-uniqueness --fullpath --not-match-d='compiler/me/dist'
}

inspbase () {
  /bin/echo -n "$1" ' '
  shift
  sumof runcloc $@
}

insp () {
  inspbase "$@"
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
      runcloc compiler/base   --by-file
      runcloc compiler/parse  --by-file
      runcloc compiler/passes --by-file
      runcloc compiler/llvm   --by-file
      runcloc compiler/me     --by-file
      exit
      ;;
    *--runcloc*)
      shift
      echo "runcloc $@     --by-file"
            runcloc $@     --by-file
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
insp "compiler/allcpp" compiler/*.cpp compiler/include compiler/base compiler/parse compiler/passes compiler/llvm
insp "third_party    " third_party
