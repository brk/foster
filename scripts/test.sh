#!/bin/bash

OUTPUT=`pwd`/fc-output

STATIC_LIBS="libfoster_main.o libchromium_base.a libcpuid.a libimath.a libcoro.a"
case `uname -s` in
  Darwin)
    RUNTIME_LIBS="-lpthread -framework CoreFoundation -framework Cocoa -lobjc"
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

extractinput () {
  grep '// IN:' $1 | sed 's/.. IN: //' > recorded-input.txt
}

run () {
  OPT=$OUTPUT/out

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  #`llvm-config --libdir`/libprofile_rt.so 
  #echo "g++ $OPT.s ${STATIC_LIBS} ${RUNTIME_LIBS} -o $OPT"
  g++ $OPT.s ${STATIC_LIBS} ${RUNTIME_LIBS} -o $OPT
  TIMEEND "gcc"

  if [ "z$TIMED_CMD_STATUS" != "z0" ]; then return; fi
  TIMESTART
  <recorded-input.txt $OPT 2>_stderr.txt 1>_stdout.txt
  paste _stderr.txt _stdout.txt
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

runfosterme () {
  echo ./me $OUTPUT/_tmp.pb $OUTPUT/_tmp2.pb
  ./me $OUTPUT/_tmp.pb $OUTPUT/_tmp2.pb
}

runfosterc () {
  TIMESTART
  #./fosterc $TESTPATH $@
  echo ./fosterparse $TESTPATH $OUTPUT/_tmp.pb
  ./fosterparse $TESTPATH $OUTPUT/_tmp.pb

  runfosterme

  echo ./fosterlower $OUTPUT/_tmp2.pb
  ./fosterlower $OUTPUT/_tmp2.pb -o _tmp3 -dump-prelinked -dump-postlinked

  echo ./fosteroptc $OUTPUT/_tmp3.preopt.bc -dump-postopt
  ./fosteroptc $OUTPUT/_tmp3.preopt.bc -dump-postopt


  TIMEEND "fosterc $@"
}

cleanout () {
  rm -f $OUTPUT/fstrprog.O2.bc foster.bc $OUTPUT/out* $OUTPUT/_tmp* foster.ll gclog.txt
}

TESTPATH=$1
shift

make fosteroptc fosterparse fosterlower me && cleanout && runfosterc $@ && extractinput $TESTPATH && run ; echo $?
