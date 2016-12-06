#!/bin/sh

#MLTON=mlton
MLTON=${HOME}/Downloads/mlton/build/bin/mlton

for cg in amd64 c llvm; do

  echo Building reference ${cg}
  ${MLTON} -codegen ${cg} -output m.${cg}.exe mandelbrot.sml
  echo Building higher-order ${cg}
  ${MLTON} -codegen ${cg} -output m_ho.${cg}.exe mandelbrot_ho.sml
  echo Building first-order ${cg}
  ${MLTON} -codegen ${cg} -output m_fo.${cg}.exe mandelbrot_fo.sml

done

for x in `ls *.exe`; do
  perf stat ./${x} 2048 > /dev/null
done
