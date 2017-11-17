#!/bin/sh

function doit {

  opam switch ${VAR}
  eval `opam config env`

  ocamlopt first-order/mandelbrot_firstorder.ml     -o mandelbrot_firstorder_O1_${VAR}.exe
  rm *.o *.cmi *.cmx
  ocamlopt first-order/mandelbrot_firstorder.ml -O2 -o mandelbrot_firstorder_O2_${VAR}.exe
  rm *.o *.cmi *.cmx
  ocamlopt first-order/mandelbrot_firstorder.ml -O3 -o mandelbrot_firstorder_O3_${VAR}.exe
  rm *.o *.cmi *.cmx
  ocamlopt first-order/mandelbrot_firstorder.ml -unsafe -O3 -o mandelbrot_firstorder_O3_unsafe_${VAR}.exe
  rm *.o *.cmi *.cmx
  ocamlopt first-order/mandelbrot_firstorder.ml -unsafe -O3 -fno-PIC -o mandelbrot_firstorder_O3_unsafe_noPIC_${VAR}.exe
  rm *.o *.cmi *.cmx

  ocamlopt higher-order/mandelbrot_higherorder.ml -O2 -o mandelbrot_higherorder_O2_${VAR}.exe
  rm *.o *.cmi *.cmx

  for x in `ls *.exe`; do
    perf stat ${x} 2048 > /dev/null
  done

  sha1sum *.exe

  rm *.exe

}

VAR=4.04.1+flambda
doit

#VAR=4.03.0+fp+flambda
#doit

