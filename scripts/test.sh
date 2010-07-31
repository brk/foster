#!/bin/bash

OUTPUT=fc-output

STATIC_LIBS="libfoster_main.o libchromium_base.a libcpuid.a"
case `uname -s` in
  Darwin)
    RUNTIME_LIBS="-lpthread -framework CoreFoundation"
    ;;
  Linux)
    RUNTIME_LIBS="-lrt -lpthread"
    ;;
  *)
    echo "Unknown OS!"
    RUNTIME_LIBS="-lpthread"
    ;;
esac

TIMESTART () {
  STARTS=$(date "+%s");
  STARTZ=$(date "+%N");
  STARTN=`echo $STARTZ | sed 's/^0//'`;
}

TIMEEND () {
  TIMED_CMD_STATUS=$?

  ENDZ=$(date "+%N");
  ENDN=`echo $ENDZ | sed 's/^0//'`;
  ENDS=$(date "+%s");

  ELS="$(( $ENDS - $STARTS ))";
  ELM="$(( (${ENDN} - ${STARTN} )/1000000 ))";

  if (( $ELM < 0 )); then
    ELM=$(($ELM + 1000));
    ELS=$(($ELS - 1));
  fi

  echo "$1 took $ELS.$ELM s"
}

#linking explicit
#make && ./foster -c $1 && echo "-------" && cat foster.ll && echo "-----" && llvm-as foster.ll -f && llvm-ld foster.bc libfoster.bc -o ll-foster && ./ll-foster ; echo $?


#linking implicit
extractinput () {
  grep '// IN:' $1 | sed 's/.. IN: //' > recorded-input.txt
}

run () {
  OPT=$OUTPUT/out

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  #`llvm-config --libdir`/libprofile_rt.so 
  echo "g++ $OPT.s ${STATIC_LIBS} ${RUNTIME_LIBS} -o $OPT"
  g++ $OPT.s ${STATIC_LIBS} ${RUNTIME_LIBS} -o $OPT
  TIMEEND "gcc"

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  cat recorded-input.txt | ./$OPT
  TIMEEND "run"
}

speedtest () {
  runllc $1
  cat recorded-input.txt | ./$OPT
  cat recorded-input.txt | ./$OPT
  cat recorded-input.txt | ./$OPT
  cat recorded-input.txt | ./$OPT
  cat recorded-input.txt | ./$OPT
  cat recorded-input.txt | ./$OPT
  cat recorded-input.txt | ./$OPT
  cat recorded-input.txt | ./$OPT
}

runfosterc () {
  TIMESTART
  ./fosterc $TESTPATH $@
  TIMEEND "fosterc $@"
}

cleanout () {
  rm -f $OUTPUT/fstrprog.O2.bc foster.bc a.out foster.ll gclog.txt
}

TESTPATH=$1
shift

make && cleanout && runfosterc $@ && extractinput $TESTPATH && run ; echo $?
