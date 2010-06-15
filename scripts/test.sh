#!/bin/bash

OUTPUT=fc-output

RUNTIME_LIBS="libfoster_main.o libchromium_base.a -lrt"

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
runlli () {
  llvm-as foster.ll -f
  lli $1;
}

# $1 like foster.bc
runllc () {
  OPT=$OUTPUT/fstrprog.O2

  TIMESTART
  llvm-as foster.ll -f
  TIMEEND "las"

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  opt $1 -O2 -o=$OPT.bc -f
  TIMEEND "opt"

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  llvm-dis $OPT.bc -f
  TIMEEND "dis"

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  llc $OPT.bc -f # -> $OPT.s
  TIMEEND "llc"

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  #`llvm-config --libdir`/libprofile_rt.so 
  g++ -lrt $OPT.s ${RUNTIME_LIBS} -o $OPT -l pthread
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
  ./fosterc $1
  TIMEEND "fosterc"
}

RUN="runllc"

cleanout () {
  rm -f $OUTPUT/fstrprog.O2.bc foster.bc a.out foster.ll gclog.txt
}

make && cleanout && runfosterc $1 && extractinput $1 && $RUN foster.bc ; echo $?
