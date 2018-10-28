ocamlopt -noassert -unsafe -nodynlink -inline 100 unix.cmxa binarytrees_ocaml_5.ml -o binarytrees_ocaml_5.ocaml_unsafe_run
ocamlopt                   -nodynlink -inline 100 unix.cmxa binarytrees_ocaml_5.ml -o binarytrees_ocaml_5.ocaml_run

ocaml -version

echo "Safe OCaml:"
perf stat ./binarytrees_ocaml_5.ocaml_run 19

echo "Unsafe OCaml:"
perf stat ./binarytrees_ocaml_5.ocaml_unsafe_run 19

rm *.o *_run *.cm{i,x}
